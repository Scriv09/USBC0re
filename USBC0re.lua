-- USBC0re exFAT graphical payload browser
-- Pure Lua. Storage access is READ-ONLY; selected .lua files can be executed.
--
-- Controls:
--   D-Pad Up/Down = select
--   CROSS (X)     = enter selected directory
--   CIRCLE (O)    = back to previous directory
--   OPTIONS       = exit browser
--
-- The mass-storage device, endpoints, partition and exFAT geometry
-- are discovered dynamically, so this works with the different endpoint
-- layouts already observed on tested drives.
--
-- GUI:
--   1920x1080 framebuffer through libSceVideoOut
--   Controller input through the pad library
--   Folder/file icons, path bar, selection highlight and scrollbar
--   Bottom-right CROSS Enter / CIRCLE Back legends
--
-- IMPORTANT:
-- This takes ownership of the title's VideoOut if a second VideoOut cannot
-- be opened normally. If takeover is needed, the game's graphics thread is
-- stopped, matching the validated framebuffer path.
--
-- When finished, unplug/replug the storage device so the system restores the mass-storage driver.

local SCAN_MAX_BUS = 7
local SCAN_MAX_DEV = 31

local SLOT_OUT = 0
local SLOT_IN  = 1

local MAX_USBFS_BYTES = 4096
local MAX_DEPTH = 12
local MAX_DIRECTORIES = 256
local MAX_CLUSTERS_PER_DIRECTORY = 8192

local TIMEOUT_MS = 5000
local POLL_LIMIT = 10000
local POLL_US = 1000

-- Descriptor ioctls
local USB_GET_CONFIG_DESC = 0x4009556A
local USB_GET_FULL_DESC   = 0xC020556D

-- Interface ownership
local USB_CLAIM_INTERFACE     = 0x8004557A
local USB_RELEASE_INTERFACE   = 0x8004557B
local USB_IFACE_DRIVER_ACTIVE = 0x8004557C
local USB_IFACE_DRIVER_DETACH = 0x8004557D

-- USB filesystem transfer interface
local USB_FS_START    = 0x800155C0
local USB_FS_COMPLETE = 0x400155C2
local USB_FS_INIT     = 0x801055C3
local USB_FS_UNINIT   = 0x800155C4
local USB_FS_OPEN     = 0xC01055C5
local USB_FS_CLOSE    = 0x800155C6

local USB_FS_ENDPOINT_SIZE = 0x28
local USB_FS_FLAG_SINGLE_SHORT_OK = 0x0001
local USB_FS_FLAG_MULTI_SHORT_OK  = 0x0002

local function log(s)
    if type(print) == "function" then
        pcall(print, "[usbc0re] " .. tostring(s))
    end
end

local function notify(s)
    if type(send_notification) == "function" then
        pcall(send_notification, tostring(s))
    end
end

local function hex32(v)
    if type(v) ~= "number" then return tostring(v) end
    return string.format("0x%08X", v & 0xFFFFFFFF)
end

local function hex8(v)
    if type(v) ~= "number" then return tostring(v) end
    return string.format("0x%02X", v & 0xFF)
end

local function valid_fd(v)
    return type(v) == "number" and v >= 0 and v < 0x10000
end

local function zero_mem(p, n)
    if type(memset) == "function" then
        local ok = pcall(memset, p, 0, n)
        if ok then return end
    end

    local rounded = (n + 3) & ~3
    for off = 0, rounded - 4, 4 do
        write32(p + off, 0)
    end
end

local function u8(base, off)
    local aligned = off & ~3
    local shift = (off & 3) * 8
    return (read32(base + aligned) >> shift) & 0xFF
end

local function u16le(base, off)
    return u8(base, off) | (u8(base, off + 1) << 8)
end

local function u32le(base, off)
    return (
        u8(base, off) |
        (u8(base, off + 1) << 8) |
        (u8(base, off + 2) << 16) |
        (u8(base, off + 3) << 24)
    ) & 0xFFFFFFFF
end

local function u32be(base, off)
    return (
        (u8(base, off) << 24) |
        (u8(base, off + 1) << 16) |
        (u8(base, off + 2) << 8) |
        u8(base, off + 3)
    ) & 0xFFFFFFFF
end

local function u64le_number(base, off)
    local lo = u32le(base, off)
    local hi = u32le(base, off + 4)
    return hi * 4294967296 + lo
end

local function set_u8(base, off, value)
    local aligned = off & ~3
    local shift = (off & 3) * 8
    local mask = 0xFF << shift
    local word = read32(base + aligned)
    word = (word & (~mask)) | ((value & 0xFF) << shift)
    write32(base + aligned, word)
end

local function set_u16(base, off, value)
    set_u8(base, off, value & 0xFF)
    set_u8(base, off + 1, (value >> 8) & 0xFF)
end

local function raw_ascii(base, off, len)
    local t = {}
    for i = 0, len - 1 do
        t[#t + 1] = string.char(u8(base, off + i))
    end
    return table.concat(t)
end

local function make_u8_arg(v)
    local p = malloc(4)
    zero_mem(p, 4)
    set_u8(p, 0, v)
    return p
end

local function make_iface_arg(iface)
    local p = malloc(4)
    zero_mem(p, 4)
    write32(p, iface)
    return p
end

local function ep_ptr(endpoints, index)
    return endpoints + index * USB_FS_ENDPOINT_SIZE
end

local function ioctl_call(ioctl_fn, fd, cmd, arg)
    local ok, ret = pcall(ioctl_fn, fd, cmd, arg)
    if not ok then return nil end
    return ret
end

-- ============================================================
-- USB device / endpoint discovery
-- ============================================================

local function read_full_config(ioctl_fn, fd)
    local cfg = malloc(0x20)
    zero_mem(cfg, 0x20)

    if ioctl_call(ioctl_fn, fd, USB_GET_CONFIG_DESC, cfg) ~= 0 then
        return nil
    end

    local total = u16le(cfg, 2)
    if total < 9 or total > 4096 then
        return nil
    end

    local blob = malloc(total + 16)
    zero_mem(blob, total + 16)

    local gd = malloc(0x20)
    zero_mem(gd, 0x20)

    write64(gd + 0x00, blob)
    set_u16(gd, 0x0A, total)
    set_u8(gd, 0x10, 0)

    if ioctl_call(ioctl_fn, fd, USB_GET_FULL_DESC, gd) ~= 0 then
        return nil
    end

    local actlen = u16le(gd, 0x0C)
    if actlen == 0 or actlen > total then actlen = total end

    return blob, actlen
end

local function parse_mass_storage_config(blob, length)
    local off = 0
    local current_mass = false
    local iface = nil
    local ep_out = nil
    local ep_in = nil

    while off + 2 <= length do
        local blen = u8(blob, off)
        local btype = u8(blob, off + 1)

        if blen < 2 or off + blen > length then break end

        if btype == 0x04 and blen >= 9 then
            local ifnum = u8(blob, off + 2)
            local alt = u8(blob, off + 3)
            local cls = u8(blob, off + 5)
            local sub = u8(blob, off + 6)
            local proto = u8(blob, off + 7)

            current_mass =
                alt == 0 and cls == 0x08 and sub == 0x06 and proto == 0x50

            if current_mass then
                iface = ifnum
                ep_out = nil
                ep_in = nil
            end

        elseif btype == 0x05 and blen >= 7 and current_mass then
            local addr = u8(blob, off + 2)
            local attr = u8(blob, off + 3)

            if (attr & 0x03) == 0x02 then
                if (addr & 0x80) ~= 0 then ep_in = addr
                else ep_out = addr end
            end

            if iface ~= nil and ep_out ~= nil and ep_in ~= nil then
                return iface, ep_out, ep_in
            end
        end

        off = off + blen
    end

    return nil
end

local function discover_mass_storage(ioctl_fn)
    log("scanning ugen devices for USB mass storage...")

    for bus = 0, SCAN_MAX_BUS do
        for dev = 1, SCAN_MAX_DEV do
            local ugen = string.format("/dev/ugen%d.%d", bus, dev)
            local ok, fd = pcall(sceKernelOpen, ugen, 0, 0)

            if ok and valid_fd(fd) then
                local blob, length = read_full_config(ioctl_fn, fd)

                if blob then
                    local iface, ep_out, ep_in =
                        parse_mass_storage_config(blob, length)

                    if iface ~= nil then
                        pcall(sceKernelClose, fd)

                        local control =
                            string.format("/dev/usb/%d.%d.0", bus, dev)

                        log("mass-storage device found:")
                        log("  ugen      = " .. ugen)
                        log("  control   = " .. control)
                        log("  interface = " .. tostring(iface))
                        log("  bulk OUT  = " .. hex8(ep_out))
                        log("  bulk IN   = " .. hex8(ep_in))

                        return {
                            control = control,
                            iface = iface,
                            ep_out = ep_out,
                            ep_in = ep_in
                        }
                    end
                end

                pcall(sceKernelClose, fd)
            end
        end
    end

    return nil
end

-- ============================================================
-- USB_FS transport
-- ============================================================

local function configure_slot(endpoints, index, ppbuf, plen)
    local ep = ep_ptr(endpoints, index)

    write64(ep + 0x00, ppbuf)
    write64(ep + 0x08, plen)
    write32(ep + 0x10, 1)
    write32(ep + 0x14, 0)

    set_u16(
        ep, 0x18,
        USB_FS_FLAG_SINGLE_SHORT_OK |
        USB_FS_FLAG_MULTI_SHORT_OK
    )

    set_u16(ep, 0x1A, TIMEOUT_MS)
    set_u16(ep, 0x1C, 0)
    write32(ep + 0x20, 0)
end

local function fs_open(ioctl_fn, fd, index, epno)
    local p = malloc(0x10)
    zero_mem(p, 0x10)

    write32(p + 0x00, MAX_USBFS_BYTES)
    write32(p + 0x04, 1)
    set_u8(p, 0x0A, 0)
    set_u8(p, 0x0B, index)
    set_u8(p, 0x0C, epno)

    local ret = ioctl_call(ioctl_fn, fd, USB_FS_OPEN, p)

    if ret ~= 0 then
        log("USB_FS_OPEN failed for endpoint " ..
            hex8(epno) .. ": " .. tostring(ret))
        return false
    end

    log("endpoint " .. hex8(epno) ..
        " opened, max packet=" .. tostring(u16le(p, 0x08)))

    return true
end

local function fs_close(ioctl_fn, fd, index)
    ioctl_call(ioctl_fn, fd, USB_FS_CLOSE, make_u8_arg(index))
end

local function wait_completion(ioctl_fn, fd, expected, endpoints, usleep_fn)
    local complete = malloc(4)
    zero_mem(complete, 4)

    for _ = 1, POLL_LIMIT do
        set_u8(complete, 0, 0xFF)

        local ok, ret = pcall(ioctl_fn, fd, USB_FS_COMPLETE, complete)

        if ok and ret == 0 and u8(complete, 0) == expected then
            local status =
                read32(ep_ptr(endpoints, expected) + 0x20) & 0xFFFFFFFF
            return status == 0
        end

        if usleep_fn then pcall(usleep_fn, POLL_US) end
    end

    return false
end

local function fs_transfer(
    io, index, buffer, length, ppbuf, plen
)
    zero_mem(ppbuf, 8)
    zero_mem(plen, 4)
    write64(ppbuf, buffer)
    write32(plen, length)

    configure_slot(io.endpoints, index, ppbuf, plen)

    if ioctl_call(
        io.ioctl_fn, io.fd,
        USB_FS_START, make_u8_arg(index)
    ) ~= 0 then
        return false, 0
    end

    local ok = wait_completion(
        io.ioctl_fn, io.fd,
        index, io.endpoints, io.usleep_fn
    )

    return ok, read32(plen) & 0xFFFFFFFF
end

local next_tag = 0x68AC0001

local function scsi_data_in(io, cdb, cdb_len, data_len)
    local tag = next_tag
    next_tag = next_tag + 1

    local cbw = malloc(32)
    zero_mem(cbw, 32)

    write32(cbw + 0x00, 0x43425355)
    write32(cbw + 0x04, tag)
    write32(cbw + 0x08, data_len)

    set_u8(cbw, 0x0C, 0x80)
    set_u8(cbw, 0x0D, 0)
    set_u8(cbw, 0x0E, cdb_len)

    for i = 0, cdb_len - 1 do
        set_u8(cbw, 0x0F + i, cdb[i + 1])
    end

    local ok, n = fs_transfer(
        io, SLOT_OUT, cbw, 31,
        io.out_pp, io.out_len
    )

    if not ok or n ~= 31 then
        return false, nil, 0, "CBW failed"
    end

    local data = malloc(data_len + 16)
    zero_mem(data, data_len + 16)

    ok, n = fs_transfer(
        io, SLOT_IN, data, data_len,
        io.in_pp, io.in_len
    )

    if not ok then
        return false, data, n, "data phase failed"
    end

    local csw = malloc(16)
    zero_mem(csw, 16)

    local csw_ok, csw_n = fs_transfer(
        io, SLOT_IN, csw, 13,
        io.in_pp, io.in_len
    )

    if not csw_ok or csw_n ~= 13 then
        return false, data, n, "CSW failed"
    end

    local sig = read32(csw + 0x00) & 0xFFFFFFFF
    local got_tag = read32(csw + 0x04) & 0xFFFFFFFF
    local residue = read32(csw + 0x08) & 0xFFFFFFFF
    local status = u8(csw, 0x0C)

    if sig ~= 0x53425355 or
       got_tag ~= tag or
       residue ~= 0 or
       status ~= 0 then
        return false, data, n, "bad CSW"
    end

    return true, data, n, nil
end

local function scsi_read_capacity(io)
    local cdb = {
        0x25, 0,
        0, 0, 0, 0,
        0, 0, 0, 0
    }

    local ok, data, n, err = scsi_data_in(io, cdb, 10, 8)

    if not ok or n < 8 then
        return nil, nil, err
    end

    return u32be(data, 0), u32be(data, 4), nil
end

local function scsi_read_blocks(io, lba, blocks)
    if blocks < 1 or blocks > io.max_blocks_per_read then
        return false, nil, 0, "invalid block count"
    end

    local bytes = blocks * io.block_size

    local cdb = {
        0x28, 0,
        (lba >> 24) & 0xFF,
        (lba >> 16) & 0xFF,
        (lba >> 8) & 0xFF,
        lba & 0xFF,
        0,
        (blocks >> 8) & 0xFF,
        blocks & 0xFF,
        0
    }

    return scsi_data_in(io, cdb, 10, bytes)
end

-- ============================================================
-- exFAT volume discovery / geometry
-- ============================================================

local function is_exfat_boot(buf)
    return raw_ascii(buf, 3, 8) == "EXFAT   "
end

local function find_exfat_volume(io)
    local ok, lba0, n, err = scsi_read_blocks(io, 0, 1)

    if not ok or n < io.block_size then
        return nil, nil, "could not read LBA 0: " .. tostring(err)
    end

    if is_exfat_boot(lba0) then
        return 0, lba0, nil
    end

    if io.block_size < 512 or
       u8(lba0, 510) ~= 0x55 or
       u8(lba0, 511) ~= 0xAA then
        return nil, nil, "no exFAT boot sector or valid MBR"
    end

    log("MBR detected; checking partitions...")

    for i = 0, 3 do
        local off = 446 + i * 16
        local ptype = u8(lba0, off + 4)
        local first_lba = u32le(lba0, off + 8)
        local sectors = u32le(lba0, off + 12)

        if ptype ~= 0 and sectors ~= 0 then
            log(string.format(
                "  partition %d type=%s first_lba=%u sectors=%u",
                i + 1, hex8(ptype), first_lba, sectors
            ))

            local pok, pbr, pn =
                scsi_read_blocks(io, first_lba, 1)

            if pok and pn >= io.block_size and is_exfat_boot(pbr) then
                log("  -> exFAT partition found")
                return first_lba, pbr, nil
            end
        end
    end

    return nil, nil, "no exFAT partition found"
end

local function parse_exfat_geometry(partition_lba, boot, block_size)
    local bytes_per_sector = 1 << u8(boot, 108)
    local sectors_per_cluster = 1 << u8(boot, 109)

    if bytes_per_sector ~= block_size then
        return nil,
            "exFAT bytes/sector does not match SCSI logical block size"
    end

    local g = {
        partition_lba = partition_lba,
        fat_offset = u32le(boot, 80),
        fat_length = u32le(boot, 84),
        cluster_heap_offset = u32le(boot, 88),
        cluster_count = u32le(boot, 92),
        root_cluster = u32le(boot, 96),
        bytes_per_sector = bytes_per_sector,
        sectors_per_cluster = sectors_per_cluster,
        cluster_size = bytes_per_sector * sectors_per_cluster
    }

    g.fat_start_lba = g.partition_lba + g.fat_offset

    g.cluster_to_lba = function(cluster)
        return g.partition_lba +
            g.cluster_heap_offset +
            ((cluster - 2) * g.sectors_per_cluster)
    end

    g.root_lba = g.cluster_to_lba(g.root_cluster)

    return g
end

-- ============================================================
-- FAT helper
-- ============================================================

local function make_fat_reader(io, g)
    local cache_lba = nil
    local cache_buf = nil

    return function(cluster)
        local byte_off = cluster * 4
        local sector_rel = math.floor(byte_off / g.bytes_per_sector)
        local off = byte_off % g.bytes_per_sector
        local lba = g.fat_start_lba + sector_rel

        if cache_lba ~= lba then
            local ok, buf, _, err =
                scsi_read_blocks(io, lba, 1)

            if not ok then return nil, err end

            cache_lba = lba
            cache_buf = buf
        end

        return u32le(cache_buf, off), nil
    end
end

-- ============================================================
-- UTF-16 / display helpers
-- ============================================================

local function utf8_cp(cp)
    if cp <= 0x7F then
        return string.char(cp)
    elseif cp <= 0x7FF then
        return string.char(
            0xC0 | ((cp >> 6) & 0x1F),
            0x80 | (cp & 0x3F)
        )
    elseif cp <= 0xFFFF then
        return string.char(
            0xE0 | ((cp >> 12) & 0x0F),
            0x80 | ((cp >> 6) & 0x3F),
            0x80 | (cp & 0x3F)
        )
    elseif cp <= 0x10FFFF then
        return string.char(
            0xF0 | ((cp >> 18) & 0x07),
            0x80 | ((cp >> 12) & 0x3F),
            0x80 | ((cp >> 6) & 0x3F),
            0x80 | (cp & 0x3F)
        )
    end

    return "?"
end

local function utf16_units_to_utf8(units, limit)
    local out = {}
    local i = 1
    local count = 0

    while i <= #units and count < limit do
        local w1 = units[i]
        local cp

        if w1 >= 0xD800 and w1 <= 0xDBFF and i < #units then
            local w2 = units[i + 1]

            if w2 >= 0xDC00 and w2 <= 0xDFFF then
                cp = 0x10000 +
                    ((w1 - 0xD800) << 10) +
                    (w2 - 0xDC00)
                i = i + 2
            else
                cp = 0xFFFD
                i = i + 1
            end
        elseif w1 >= 0xDC00 and w1 <= 0xDFFF then
            cp = 0xFFFD
            i = i + 1
        else
            cp = w1
            i = i + 1
        end

        out[#out + 1] = utf8_cp(cp)
        count = count + 1
    end

    return table.concat(out)
end

local function size_text(n)
    if n >= 1024 * 1024 * 1024 then
        return string.format("%.2f GiB", n / (1024 * 1024 * 1024))
    elseif n >= 1024 * 1024 then
        return string.format("%.2f MiB", n / (1024 * 1024))
    elseif n >= 1024 then
        return string.format("%.2f KiB", n / 1024)
    end

    return tostring(n) .. " B"
end

local function path_join(parent, name)
    if parent == "/" then return "/" .. name end
    return parent .. "/" .. name
end


-- ============================================================
-- Lazy exFAT directory loader
-- ============================================================

local function make_directory_parser(entries, meta)
    local p = {
        pending = nil,
        end_marker = false
    }

    local function emit_pending()
        local e = p.pending
        if not e or not e.stream then
            p.pending = nil
            return
        end

        local name = utf16_units_to_utf8(
            e.name_units,
            e.stream.name_length
        )

        entries[#entries + 1] = {
            name = name,
            is_dir = (e.attrs & 0x0010) ~= 0,
            attrs = e.attrs,
            first_cluster = e.stream.first_cluster or 0,
            data_length = e.stream.data_length or 0,
            valid_data_length = e.stream.valid_data_length or 0,
            no_fat_chain = e.stream.no_fat_chain
        }

        p.pending = nil
    end

    function p:feed(buf, bytes)
        for off = 0, bytes - 32, 32 do
            local entry_type = u8(buf, off)

            if entry_type == 0x00 then
                if self.pending then emit_pending() end
                self.end_marker = true
                return
            end

            if (entry_type & 0x80) == 0 then
                if self.pending then
                    self.pending.remaining =
                        self.pending.remaining - 1

                    if self.pending.remaining <= 0 then
                        emit_pending()
                    end
                end

            elseif entry_type == 0x81 then
                -- Allocation Bitmap: metadata, not shown as a normal file.
                meta.bitmap_cluster = u32le(buf, off + 20)
                meta.bitmap_length = u64le_number(buf, off + 24)

            elseif entry_type == 0x82 then
                -- Up-case Table: metadata, not shown.
                meta.upcase_cluster = u32le(buf, off + 20)
                meta.upcase_length = u64le_number(buf, off + 24)

            elseif entry_type == 0x83 then
                local count = u8(buf, off + 1)
                local units = {}

                for i = 0, math.min(count, 11) - 1 do
                    units[#units + 1] =
                        u16le(buf, off + 2 + i * 2)
                end

                meta.volume_label =
                    utf16_units_to_utf8(units, count)

            elseif entry_type == 0x85 then
                if self.pending then emit_pending() end

                self.pending = {
                    remaining = u8(buf, off + 1),
                    attrs = u16le(buf, off + 4),
                    stream = nil,
                    name_units = {}
                }

            elseif self.pending and entry_type == 0xC0 then
                local flags = u8(buf, off + 1)

                self.pending.stream = {
                    no_fat_chain = (flags & 0x02) ~= 0,
                    name_length = u8(buf, off + 3),
                    valid_data_length = u64le_number(buf, off + 8),
                    first_cluster = u32le(buf, off + 20),
                    data_length = u64le_number(buf, off + 24)
                }

                self.pending.remaining =
                    self.pending.remaining - 1

                if self.pending.remaining <= 0 then
                    emit_pending()
                end

            elseif self.pending and entry_type == 0xC1 then
                for i = 0, 14 do
                    self.pending.name_units[
                        #self.pending.name_units + 1
                    ] = u16le(buf, off + 2 + i * 2)
                end

                self.pending.remaining =
                    self.pending.remaining - 1

                if self.pending.remaining <= 0 then
                    emit_pending()
                end

            elseif self.pending then
                self.pending.remaining =
                    self.pending.remaining - 1

                if self.pending.remaining <= 0 then
                    emit_pending()
                end
            end
        end
    end

    function p:finish()
        if self.pending then emit_pending() end
    end

    return p
end

local function sort_directory_entries(entries)
    table.sort(entries, function(a, b)
        if a.is_dir ~= b.is_dir then
            return a.is_dir
        end

        return string.lower(a.name) < string.lower(b.name)
    end)
end

local function read_directory_entries(io, g, read_fat, dir)
    local entries = {}
    local meta = {}
    local parser = make_directory_parser(entries, meta)

    local function read_cluster(cluster, bytes_limit)
        local base_lba = g.cluster_to_lba(cluster)
        local sectors = g.sectors_per_cluster

        if bytes_limit then
            sectors = math.min(
                sectors,
                math.ceil(bytes_limit / g.bytes_per_sector)
            )
        end

        local remaining = bytes_limit

        for sector = 0, sectors - 1, io.max_blocks_per_read do
            local blocks = math.min(
                io.max_blocks_per_read,
                sectors - sector
            )

            local ok, buf, got, err =
                scsi_read_blocks(io, base_lba + sector, blocks)

            if not ok then
                return false,
                    "read failed at LBA " ..
                    tostring(base_lba + sector) ..
                    ": " .. tostring(err)
            end

            local feed_bytes = got

            if remaining then
                feed_bytes = math.min(feed_bytes, remaining)
                remaining = remaining - feed_bytes
            end

            feed_bytes = feed_bytes - (feed_bytes % 32)

            if feed_bytes > 0 then
                parser:feed(buf, feed_bytes)
            end

            if parser.end_marker then
                return true
            end

            if remaining and remaining <= 0 then
                return true
            end
        end

        return true
    end

    if dir.is_root then
        local cluster = g.root_cluster
        local visited = {}
        local count = 0

        while count < MAX_CLUSTERS_PER_DIRECTORY do
            if cluster < 2 or cluster > g.cluster_count + 1 then
                return nil, meta,
                    "invalid root cluster " .. tostring(cluster)
            end

            if visited[cluster] then
                return nil, meta,
                    "root FAT loop at cluster " .. tostring(cluster)
            end

            visited[cluster] = true
            count = count + 1

            local ok, err = read_cluster(cluster, nil)
            if not ok then return nil, meta, err end

            if parser.end_marker then break end

            local next_cluster, ferr = read_fat(cluster)
            if not next_cluster then
                return nil, meta, "FAT error: " .. tostring(ferr)
            end

            if next_cluster >= 0xFFFFFFF8 then break end
            if next_cluster == 0 or next_cluster == 0xFFFFFFF7 then break end

            cluster = next_cluster
        end

    elseif dir.no_fat_chain then
        local clusters_needed =
            math.ceil(dir.data_length / g.cluster_size)

        local remaining = dir.data_length

        if clusters_needed > MAX_CLUSTERS_PER_DIRECTORY then
            return nil, meta, "directory exceeds safety cluster limit"
        end

        for i = 0, clusters_needed - 1 do
            local bytes_this =
                math.min(remaining, g.cluster_size)

            local cluster = dir.first_cluster + i

            if cluster < 2 or cluster > g.cluster_count + 1 then
                return nil, meta,
                    "invalid contiguous cluster " .. tostring(cluster)
            end

            local ok, err = read_cluster(cluster, bytes_this)
            if not ok then return nil, meta, err end

            remaining = remaining - bytes_this

            if parser.end_marker or remaining <= 0 then break end
        end

    else
        local cluster = dir.first_cluster
        local remaining = dir.data_length
        local visited = {}
        local count = 0

        while remaining > 0 and
              count < MAX_CLUSTERS_PER_DIRECTORY do

            if cluster < 2 or cluster > g.cluster_count + 1 then
                return nil, meta,
                    "invalid directory cluster " .. tostring(cluster)
            end

            if visited[cluster] then
                return nil, meta,
                    "directory FAT loop at cluster " .. tostring(cluster)
            end

            visited[cluster] = true
            count = count + 1

            local bytes_this =
                math.min(remaining, g.cluster_size)

            local ok, err = read_cluster(cluster, bytes_this)
            if not ok then return nil, meta, err end

            remaining = remaining - bytes_this

            if parser.end_marker or remaining <= 0 then break end

            local next_cluster, ferr = read_fat(cluster)
            if not next_cluster then
                return nil, meta,
                    "FAT error: " .. tostring(ferr)
            end

            if next_cluster >= 0xFFFFFFF8 then break end
            if next_cluster == 0 or next_cluster == 0xFFFFFFF7 then break end

            cluster = next_cluster
        end
    end

    parser:finish()
    sort_directory_entries(entries)

    return entries, meta, nil
end

-- ============================================================
-- exFAT file reader / Lua payload loader
-- ============================================================

MAX_LUA_PAYLOAD_BYTES = 8 * 1024 * 1024

function pointer_bytes_to_string(ptr, n)
    if not n or n <= 0 then
        return ""
    end

    -- read_buffer(), when available, is dramatically faster than
    -- converting one byte at a time. Keep a byte-wise fallback for older
    -- environments.
    if type(read_buffer) == "function" then
        local ok, data =
            pcall(
                read_buffer,
                ptr,
                n
            )

        if ok and type(data) == "string" then
            if #data == n then
                return data
            elseif #data > n then
                return string.sub(data, 1, n)
            end
        end
    end

    local parts = {}
    local off = 0
    local STEP = 4096

    while off < n do
        local take =
            math.min(
                STEP,
                n - off
            )

        parts[#parts + 1] =
            raw_ascii(
                ptr,
                off,
                take
            )

        off = off + take
    end

    return table.concat(parts)
end

function read_file_contents(io, g, read_fat, e)
    if not e or e.is_dir then
        return nil, "not a file"
    end

    local total =
        tonumber(e.data_length or 0) or 0

    if total < 0 then
        return nil, "invalid file size"
    end

    if total == 0 then
        return "", nil
    end

    if total > MAX_LUA_PAYLOAD_BYTES then
        return nil,
            "file is too large (" ..
            tostring(total) ..
            " bytes); maximum Lua payload size is " ..
            tostring(MAX_LUA_PAYLOAD_BYTES) ..
            " bytes"
    end

    local first =
        tonumber(e.first_cluster or 0) or 0

    if first < 2 or first > g.cluster_count + 1 then
        return nil,
            "invalid first cluster " ..
            tostring(first)
    end

    local pieces = {}
    local remaining = total

    local function append_cluster(cluster, bytes_this)
        local base_lba =
            g.cluster_to_lba(cluster)

        local sectors =
            math.ceil(
                bytes_this /
                g.bytes_per_sector
            )

        local cluster_remaining =
            bytes_this

        for sector = 0,
            sectors - 1,
            io.max_blocks_per_read do

            local blocks =
                math.min(
                    io.max_blocks_per_read,
                    sectors - sector
                )

            local ok, buf, got, err =
                scsi_read_blocks(
                    io,
                    base_lba + sector,
                    blocks
                )

            if not ok then
                return false,
                    "read failed at LBA " ..
                    tostring(
                        base_lba + sector
                    ) ..
                    ": " ..
                    tostring(err)
            end

            local take =
                math.min(
                    got,
                    cluster_remaining
                )

            if take > 0 then
                pieces[#pieces + 1] =
                    pointer_bytes_to_string(
                        buf,
                        take
                    )

                cluster_remaining =
                    cluster_remaining -
                    take

                remaining =
                    remaining -
                    take
            end

            if cluster_remaining <= 0 or
               remaining <= 0 then
                break
            end
        end

        return true, nil
    end

    if e.no_fat_chain then
        local clusters_needed =
            math.ceil(
                total /
                g.cluster_size
            )

        for i = 0, clusters_needed - 1 do
            local bytes_this =
                math.min(
                    remaining,
                    g.cluster_size
                )

            local cluster =
                first + i

            if cluster < 2 or
               cluster > g.cluster_count + 1 then
                return nil,
                    "invalid contiguous cluster " ..
                    tostring(cluster)
            end

            local ok, err =
                append_cluster(
                    cluster,
                    bytes_this
                )

            if not ok then
                return nil, err
            end

            if remaining <= 0 then
                break
            end
        end

    else
        local cluster = first
        local visited = {}
        local count = 0

        while remaining > 0 do
            if count >=
               MAX_CLUSTERS_PER_DIRECTORY then
                return nil,
                    "file exceeds safety cluster limit"
            end

            if cluster < 2 or
               cluster > g.cluster_count + 1 then
                return nil,
                    "invalid file cluster " ..
                    tostring(cluster)
            end

            if visited[cluster] then
                return nil,
                    "file FAT loop at cluster " ..
                    tostring(cluster)
            end

            visited[cluster] = true
            count = count + 1

            local bytes_this =
                math.min(
                    remaining,
                    g.cluster_size
                )

            local ok, err =
                append_cluster(
                    cluster,
                    bytes_this
                )

            if not ok then
                return nil, err
            end

            if remaining <= 0 then
                break
            end

            local next_cluster, ferr =
                read_fat(cluster)

            if not next_cluster then
                return nil,
                    "FAT error: " ..
                    tostring(ferr)
            end

            if next_cluster >= 0xFFFFFFF8 then
                break
            end

            if next_cluster == 0 or
               next_cluster == 0xFFFFFFF7 then
                return nil,
                    "unexpected end of FAT chain"
            end

            cluster = next_cluster
        end
    end

    if remaining ~= 0 then
        return nil,
            "short file read; " ..
            tostring(remaining) ..
            " bytes missing"
    end

    return table.concat(pieces), nil
end

function is_lua_filename(name)
    if type(name) ~= "string" or
       #name < 4 then
        return false
    end

    return string.lower(
        string.sub(
            name,
            -4
        )
    ) == ".lua"
end

function compile_usb_lua(source, chunk_name)
    chunk_name =
        chunk_name or "@usb_payload.lua"

    if type(load) == "function" then
        local ok, chunk, err =
            pcall(
                load,
                source,
                chunk_name,
                "t",
                _ENV
            )

        if not ok then
            return nil,
                "load() failed: " ..
                tostring(chunk)
        end

        if not chunk then
            return nil,
                tostring(err or
                    "Lua compile failed")
        end

        return chunk, nil
    end

    -- Compatibility fallback for a Lua environment exposing loadstring.
    if type(loadstring) == "function" then
        local ok, chunk, err =
            pcall(
                loadstring,
                source,
                chunk_name
            )

        if not ok then
            return nil,
                "loadstring() failed: " ..
                tostring(chunk)
        end

        if not chunk then
            return nil,
                tostring(err or
                    "Lua compile failed")
        end

        return chunk, nil
    end

    return nil,
        "this Lua environment does not expose load()"
end

-- ============================================================
-- Small 5x7 UI font
-- Lowercase is intentionally rendered with the matching uppercase glyph.
-- ============================================================

local FONT5 = {
    [" "]={0,0,0,0,0,0,0},
    ["A"]={14,17,17,31,17,17,17},
    ["B"]={30,17,17,30,17,17,30},
    ["C"]={14,17,16,16,16,17,14},
    ["D"]={30,17,17,17,17,17,30},
    ["E"]={31,16,16,30,16,16,31},
    ["F"]={31,16,16,30,16,16,16},
    ["G"]={14,17,16,23,17,17,15},
    ["H"]={17,17,17,31,17,17,17},
    ["I"]={31,4,4,4,4,4,31},
    ["J"]={7,2,2,2,18,18,12},
    ["K"]={17,18,20,24,20,18,17},
    ["L"]={16,16,16,16,16,16,31},
    ["M"]={17,27,21,21,17,17,17},
    ["N"]={17,25,21,19,17,17,17},
    ["O"]={14,17,17,17,17,17,14},
    ["P"]={30,17,17,30,16,16,16},
    ["Q"]={14,17,17,17,21,18,13},
    ["R"]={30,17,17,30,20,18,17},
    ["S"]={15,16,16,14,1,1,30},
    ["T"]={31,4,4,4,4,4,4},
    ["U"]={17,17,17,17,17,17,14},
    ["V"]={17,17,17,17,17,10,4},
    ["W"]={17,17,17,21,21,21,10},
    ["X"]={17,17,10,4,10,17,17},
    ["Y"]={17,17,10,4,4,4,4},
    ["Z"]={31,1,2,4,8,16,31},

    ["0"]={14,17,19,21,25,17,14},
    ["1"]={4,12,4,4,4,4,14},
    ["2"]={14,17,1,2,4,8,31},
    ["3"]={30,1,1,14,1,1,30},
    ["4"]={2,6,10,18,31,2,2},
    ["5"]={31,16,16,30,1,1,30},
    ["6"]={14,16,16,30,17,17,14},
    ["7"]={31,1,2,4,8,8,8},
    ["8"]={14,17,17,14,17,17,14},
    ["9"]={14,17,17,15,1,1,14},

    ["."]={0,0,0,0,0,12,12},
    [","]={0,0,0,0,12,12,8},
    [":"]={0,4,4,0,4,4,0},
    [";"]={0,4,4,0,4,4,8},
    ["-"]={0,0,0,31,0,0,0},
    ["_"]={0,0,0,0,0,0,31},
    ["/"]={1,2,2,4,8,8,16},
    ["\\"]={16,8,8,4,2,2,1},
    ["!"]={4,4,4,4,4,0,4},
    ["?"]={14,17,1,2,4,0,4},
    ["("]={2,4,8,8,8,4,2},
    [")"]={8,4,2,2,2,4,8},
    ["["]={14,8,8,8,8,8,14},
    ["]"]={14,2,2,2,2,2,14},
    ["+"]={0,4,4,31,4,4,0},
    ["="]={0,31,0,31,0,0,0},
    ["#"]={10,31,10,10,31,10,0},
    ["'"]={4,4,0,0,0,0,0},
    ["\""]={10,10,0,0,0,0,0},
    ["<"]={2,4,8,16,8,4,2},
    [">"]={8,4,2,1,2,4,8},
    ["|"]={4,4,4,4,4,4,4},
    ["*"]={0,17,10,4,10,17,0},
    ["@"]={14,17,23,21,23,16,14}
}

local function glyph_for_byte(b)
    if b >= 97 and b <= 122 then
        b = b - 32
    end

    if b < 32 or b > 126 then
        return FONT5["?"]
    end

    return FONT5[string.char(b)] or FONT5["?"]
end

-- ============================================================
-- Framebuffer renderer
-- ============================================================

local UI_W = 1920
local UI_H = 1080
local UI_FB_SIZE = UI_W * UI_H * 4
local UI_FB_ALIGNED =
    (UI_FB_SIZE + 0x1FFFFF) & (~0x1FFFFF)
local UI_FB_TOTAL = UI_FB_ALIGNED * 2

local COL_BG       = 0x000D0E15
local COL_PANEL    = 0x00151822
local COL_PANEL2   = 0x00202433
local COL_SELECT   = 0x00162A20
local COL_SELECTED = 0x0048E07A
local COL_CYAN     = 0x0005D9E8
local COL_PINK     = 0x00FF2A6D
local COL_WHITE    = 0x00F4F7FB
local COL_TEXT     = 0x00F4F7FB
local COL_MUTED    = 0x007D8798
local COL_FOLDER   = 0x0057A8FF
local COL_FILE     = 0x00F4F7FB
local COL_CROSS    = 0x0057A8FF
local COL_CIRCLE   = 0x00FF6177

local function fb_set(fb, x, y, color)
    if x < 0 or y < 0 or x >= UI_W or y >= UI_H then
        return
    end

    write32(fb + ((y * UI_W + x) * 4), color)
end

local function fb_rect_slow(fb, x, y, w, h, color)
    if x < 0 then w = w + x; x = 0 end
    if y < 0 then h = h + y; y = 0 end
    if x + w > UI_W then w = UI_W - x end
    if y + h > UI_H then h = UI_H - y end

    if w <= 0 or h <= 0 then return end

    for yy = 0, h - 1 do
        local addr = fb + (((y + yy) * UI_W + x) * 4)
        local xx = 0

        while xx + 1 < w do
            local pair =
                (color & 0xFFFFFFFF) |
                ((color & 0xFFFFFFFF) << 32)

            write64(addr + xx * 4, pair)
            xx = xx + 2
        end

        if xx < w then
            write32(addr + xx * 4, color)
        end
    end
end

local function fb_rect_gray(ui, fb, x, y, w, h, byte)
    if ui.memset then
        if x < 0 then w = w + x; x = 0 end
        if y < 0 then h = h + y; y = 0 end
        if x + w > UI_W then w = UI_W - x end
        if y + h > UI_H then h = UI_H - y end

        if w <= 0 or h <= 0 then return end

        for yy = 0, h - 1 do
            local addr =
                fb + (((y + yy) * UI_W + x) * 4)

            ui.memset(addr, byte, w * 4)
        end
    else
        local c =
            byte |
            (byte << 8) |
            (byte << 16) |
            (byte << 24)

        fb_rect_slow(fb, x, y, w, h, c)
    end
end

local function fb_clear(ui, fb)
    if ui.memset then
        ui.memset(fb, 0x0D, UI_FB_SIZE)
    else
        fb_rect_slow(fb, 0, 0, UI_W, UI_H, COL_BG)
    end
end

local function fb_hline(fb, x, y, w, color)
    fb_rect_slow(fb, x, y, w, 2, color)
end

local function fb_vline(fb, x, y, h, color)
    fb_rect_slow(fb, x, y, 2, h, color)
end

local function fb_char(fb, x, y, ch_byte, color, scale)
    local glyph = glyph_for_byte(ch_byte)

    for row = 0, 6 do
        local bits = glyph[row + 1]

        for col = 0, 4 do
            local mask = 1 << (4 - col)

            if (bits & mask) ~= 0 then
                fb_rect_slow(
                    fb,
                    x + col * scale,
                    y + row * scale,
                    scale,
                    scale,
                    color
                )
            end
        end
    end
end

local function fb_text(fb, x, y, text, color, scale, max_chars)
    text = tostring(text or "")
    local count = 0
    local cx = x

    for i = 1, #text do
        if max_chars and count >= max_chars then break end

        local b = string.byte(text, i)
        fb_char(fb, cx, y, b, color, scale)

        cx = cx + 6 * scale
        count = count + 1
    end

    return cx
end

local function text_width(text, scale)
    return #tostring(text or "") * 6 * scale
end

local function fit_name(name, max_chars)
    name = tostring(name or "")

    if #name <= max_chars then
        return name
    end

    if max_chars <= 3 then
        return string.sub(name, 1, max_chars)
    end

    return string.sub(name, 1, max_chars - 3) .. "..."
end

local function draw_folder_icon(fb, x, y, selected)
    local c = selected and COL_SELECTED or COL_FOLDER

    fb_rect_slow(fb, x + 2, y + 3, 15, 7, c)
    fb_rect_slow(fb, x, y + 9, 34, 22, c)
    fb_rect_slow(fb, x + 3, y + 12, 28, 16, COL_PANEL2)
end

local function draw_file_icon(fb, x, y, selected)
    local c = selected and COL_SELECTED or COL_FILE

    fb_hline(fb, x + 5, y + 2, 24, c)
    fb_hline(fb, x + 5, y + 30, 24, c)
    fb_vline(fb, x + 5, y + 2, 30, c)
    fb_vline(fb, x + 29, y + 9, 23, c)

    fb_hline(fb, x + 21, y + 2, 8, c)
    fb_vline(fb, x + 21, y + 2, 8, c)
    fb_hline(fb, x + 21, y + 9, 8, c)
end

local function draw_circle_outline(fb, cx, cy, r, color)
    local x = r
    local y = 0
    local err = 1 - r

    local function oct(px, py)
        fb_set(fb, cx + px, cy + py, color)
        fb_set(fb, cx + py, cy + px, color)
        fb_set(fb, cx - py, cy + px, color)
        fb_set(fb, cx - px, cy + py, color)
        fb_set(fb, cx - px, cy - py, color)
        fb_set(fb, cx - py, cy - px, color)
        fb_set(fb, cx + py, cy - px, color)
        fb_set(fb, cx + px, cy - py, color)
    end

    while x >= y do
        for t = -1, 1 do
            oct(x + t, y)
        end

        y = y + 1

        if err < 0 then
            err = err + 2 * y + 1
        else
            x = x - 1
            err = err + 2 * (y - x) + 1
        end
    end
end

local function draw_diag(fb, x1, y1, x2, y2, color)
    local dx = math.abs(x2 - x1)
    local sx = x1 < x2 and 1 or -1
    local dy = -math.abs(y2 - y1)
    local sy = y1 < y2 and 1 or -1
    local err = dx + dy

    while true do
        fb_rect_slow(fb, x1 - 1, y1 - 1, 3, 3, color)

        if x1 == x2 and y1 == y2 then break end

        local e2 = 2 * err

        if e2 >= dy then
            err = err + dy
            x1 = x1 + sx
        end

        if e2 <= dx then
            err = err + dx
            y1 = y1 + sy
        end
    end
end

local function draw_cross_button(fb, cx, cy)
    draw_circle_outline(fb, cx, cy, 17, COL_CROSS)
    draw_diag(fb, cx - 7, cy - 7, cx + 7, cy + 7, COL_CROSS)
    draw_diag(fb, cx + 7, cy - 7, cx - 7, cy + 7, COL_CROSS)
end

local function draw_circle_button(fb, cx, cy)
    draw_circle_outline(fb, cx, cy, 17, COL_CIRCLE)
    draw_circle_outline(fb, cx, cy, 9, COL_CIRCLE)
end

local function format_size_ui(n)
    if not n or n == 0 then
        return "0 B"
    elseif n >= 1024 * 1024 * 1024 then
        return string.format("%.2f GB", n / (1024 * 1024 * 1024))
    elseif n >= 1024 * 1024 then
        return string.format("%.2f MB", n / (1024 * 1024))
    elseif n >= 1024 then
        return string.format("%.2f KB", n / 1024)
    end

    return tostring(n) .. " B"
end

local function path_display(path)
    path = tostring(path or "/")
    local max_chars = 92

    if #path <= max_chars then
        return path
    end

    return "..." .. string.sub(path, #path - max_chars + 4)
end

local ROW_H = 56
local LIST_X = 56
local LIST_Y = 232
local LIST_W = UI_W - 112
local LIST_BOTTOM = 948
local MAX_VISIBLE =
    math.floor((LIST_BOTTOM - LIST_Y) / ROW_H)

function browser_status_text(state)
    local entries = state.entries or {}
    local count = #entries

    return state.status or
        tostring(count) ..
        (count == 1 and " ITEM" or " ITEMS")
end

function clear_list_row(ui, fb, y)
    -- The main framebuffer clear uses byte 0x0D, so use the same native
    -- memset-backed fill here. This is dramatically faster than repainting
    -- the whole 1920x1080 framebuffer in Lua.
    fb_rect_gray(
        ui, fb,
        LIST_X, y - 3,
        LIST_W, ROW_H - 4,
        0x0D
    )
end

function render_entry_row(ui, fb, state, idx)
    local entries = state.entries or {}
    local e = entries[idx]

    if not e then return end

    local row = idx - state.scroll
    if row < 0 or row >= MAX_VISIBLE then
        return
    end

    local y = LIST_Y + row * ROW_H
    local selected = idx == state.cursor

    clear_list_row(ui, fb, y)

    if selected then
        -- Keep the selection visibly green without repainting a huge colored
        -- rectangle pixel-by-pixel. The narrow accent and all row content
        -- are green, while the row itself uses a fast native gray fill.
        fb_rect_gray(
            ui, fb,
            LIST_X, y - 3,
            LIST_W, ROW_H - 4,
            0x18
        )

        fb_rect_slow(
            fb,
            LIST_X, y - 3,
            5, ROW_H - 4,
            COL_SELECTED
        )
    end

    if e.is_dir then
        draw_folder_icon(fb, 76, y + 8, selected)
    else
        draw_file_icon(fb, 78, y + 8, selected)
    end

    local name_color
    if selected then
        name_color = COL_SELECTED
    elseif e.is_dir then
        name_color = COL_FOLDER
    else
        name_color = COL_FILE
    end

    local shown = fit_name(e.name, 76)

    fb_text(
        fb, 130, y + 15,
        shown, name_color, 3, 76
    )

    local size =
        e.is_dir and "<DIR>" or
        format_size_ui(e.data_length)

    local sw = text_width(size, 2)

    fb_text(
        fb,
        1810 - sw,
        y + 18,
        size,
        selected and COL_SELECTED or
            (e.is_dir and COL_FOLDER or COL_FILE),
        2,
        nil
    )
end

function render_footer_status(ui, fb, state)
    -- Only repaint the left status region; controller legends on the right
    -- remain untouched.
    fb_rect_gray(
        ui, fb,
        40, 1004,
        1180, 50,
        0x15
    )

    fb_text(
        fb, 56, 1022,
        fit_name(browser_status_text(state), 88),
        COL_MUTED, 2, 88
    )
end

local function render_browser(ui, fb, state)
    fb_clear(ui, fb)

    -- Header and footer panels.
    fb_rect_gray(ui, fb, 0, 0, UI_W, 170, 0x15)
    fb_rect_gray(ui, fb, 0, 990, UI_W, 90, 0x15)

    -- Accent line.
    fb_rect_slow(fb, 0, 168, UI_W // 2, 3, COL_PINK)
    fb_rect_slow(fb, UI_W // 2, 168, UI_W // 2, 3, COL_CYAN)

    -- Title.
    fb_text(
        fb, 56, 38,
        "USB FILE BROWSER",
        COL_CYAN, 5, nil
    )

    local sub = "EXFAT"
    if state.volume_label and state.volume_label ~= "" then
        sub = sub .. "  |  " .. state.volume_label
    end

    if state.capacity_text then
        sub = sub .. "  |  " .. state.capacity_text
    end

    fb_text(fb, 58, 91, sub, COL_MUTED, 2, 100)

    -- Path container.
    fb_rect_gray(ui, fb, 54, 126, UI_W - 108, 34, 0x20)
    fb_text(
        fb, 68, 134,
        path_display(state.path),
        COL_TEXT, 2, 92
    )

    -- Column headers.
    fb_text(fb, 112, 201, "NAME", COL_MUTED, 2, nil)
    fb_text(fb, 1650, 201, "SIZE", COL_MUTED, 2, nil)
    fb_hline(fb, 56, 224, UI_W - 112, COL_PANEL2)

    local entries = state.entries or {}
    local count = #entries

    if count == 0 then
        fb_text(
            fb, 92, 278,
            "THIS FOLDER IS EMPTY",
            COL_MUTED, 3, nil
        )
    else
        for row = 0, MAX_VISIBLE - 1 do
            local idx = state.scroll + row

            if idx > count then break end

            render_entry_row(ui, fb, state, idx)
        end
    end

    -- Scrollbar.
    if count > MAX_VISIBLE then
        local track_y = LIST_Y
        local track_h = LIST_BOTTOM - LIST_Y
        local thumb_h =
            math.floor(MAX_VISIBLE * track_h / count)

        if thumb_h < 28 then thumb_h = 28 end

        local max_scroll = count - MAX_VISIBLE + 1
        local denom = math.max(1, max_scroll - 1)
        local thumb_y =
            track_y +
            math.floor(
                (state.scroll - 1) *
                (track_h - thumb_h) /
                denom
            )

        fb_rect_gray(
            ui, fb,
            1850, track_y,
            7, track_h,
            0x20
        )

        fb_rect_slow(
            fb,
            1850, thumb_y,
            7, thumb_h,
            COL_CYAN
        )
    end

    -- Footer left: status + discreet Options exit.
    fb_text(
        fb, 56, 1022,
        fit_name(browser_status_text(state), 88),
        COL_MUTED, 2, 88
    )

    fb_text(
        fb, 56, 1052,
        "OPTIONS  EXIT",
        COL_MUTED, 2, nil
    )

    -- Bottom-right requested controls.
    local cy = 1038

    draw_cross_button(fb, 1512, cy)
    fb_text(
        fb, 1542, cy - 7,
        "ENTER",
        COL_WHITE, 2, nil
    )

    draw_circle_button(fb, 1705, cy)
    fb_text(
        fb, 1735, cy - 7,
        "BACK",
        COL_WHITE, 2, nil
    )
end

function render_back_only_screen(
    ui,
    fb,
    title,
    filename,
    line1,
    line2,
    accent
)
    fb_clear(ui, fb)

    accent = accent or COL_PINK

    fb_rect_gray(
        ui, fb,
        0, 0,
        UI_W, 170,
        0x15
    )

    fb_rect_gray(
        ui, fb,
        0, 990,
        UI_W, 90,
        0x15
    )

    fb_rect_slow(
        fb,
        0, 168,
        UI_W,
        3,
        accent
    )

    fb_text(
        fb,
        56, 42,
        tostring(title or "NOTICE"),
        accent,
        5,
        70
    )

    if filename and filename ~= "" then
        fb_rect_gray(
            ui, fb,
            54, 126,
            UI_W - 108,
            34,
            0x20
        )

        fb_text(
            fb,
            68, 134,
            fit_name(filename, 92),
            COL_TEXT,
            2,
            92
        )
    end

    if line1 and line1 ~= "" then
        fb_text(
            fb,
            140, 410,
            fit_name(line1, 92),
            COL_WHITE,
            3,
            92
        )
    end

    if line2 and line2 ~= "" then
        fb_text(
            fb,
            140, 470,
            fit_name(line2, 92),
            COL_MUTED,
            2,
            92
        )
    end

    -- Exactly one control hint on this screen: Circle / Back.
    local cy = 1038

    draw_circle_button(
        fb,
        1705,
        cy
    )

    fb_text(
        fb,
        1735,
        cy - 7,
        "BACK",
        COL_WHITE,
        2,
        nil
    )
end

function render_launch_screen(
    ui,
    fb,
    filename
)
    fb_clear(ui, fb)

    fb_rect_gray(
        ui, fb,
        0, 0,
        UI_W, 170,
        0x15
    )

    fb_rect_slow(
        fb,
        0, 168,
        UI_W,
        3,
        COL_SELECTED
    )

    fb_text(
        fb,
        56, 42,
        "LAUNCHING LUA PAYLOAD",
        COL_SELECTED,
        5,
        70
    )

    fb_text(
        fb,
        140, 420,
        fit_name(
            filename or "PAYLOAD.LUA",
            88
        ),
        COL_WHITE,
        3,
        88
    )

    fb_text(
        fb,
        140, 480,
        "HANDING CONTROL TO PAYLOAD...",
        COL_MUTED,
        2,
        88
    )
end

-- ============================================================
-- Native Pad + VideoOut
-- ============================================================

local PAD_UP      = 0x00000010
local PAD_DOWN    = 0x00000040
local PAD_CIRCLE  = 0x00002000
local PAD_CROSS   = 0x00004000
local PAD_OPTIONS = 0x00000008

-- Runtime state offsets used by the validated framebuffer
-- examples.  The original EU build and supplied US update build share the
-- same runtime-compatible offsets.  The base US application build does not
-- contain the native-call gadget at this location, so the US profile is
-- gated by a tiny text fingerprint before these offsets are used.


local BUILD_ID_EU = string.char(67, 85, 83, 65, 48, 51, 52, 57, 50)
local BUILD_ID_US = string.char(67, 85, 83, 65, 48, 51, 52, 55, 52)

local EBOOT_OFFSETS = {
    [BUILD_ID_EU] = {
        name = "EU build",
        gs_thread = 0x057F89B0,
        vidout    = 0x02D695D0,
        pad_gadget = 0x31AA9,
        gadget_word = 0x21C3D3FF
    },
    [BUILD_ID_US] = {
        name = "US update build",
        gs_thread = 0x057F89B0,
        vidout    = 0x02D695D0,
        pad_gadget = 0x31AA9,
        gadget_word = 0x21C3D3FF
    }
}

local function select_eboot_offsets()
    local title = tostring(TITLE_ID)
    local o = EBOOT_OFFSETS[title]

    if not o then
        return nil, "unsupported TITLE_ID: " .. title
    end

    if type(EBOOT_BASE) ~= "number" or EBOOT_BASE == 0 then
        return nil, "EBOOT_BASE unavailable for " .. o.name
    end

    if o.gadget_word then
        local ok, word = pcall(read32, EBOOT_BASE + o.pad_gadget)
        word = ok and (word & 0xFFFFFFFF) or nil

        if word ~= o.gadget_word then
            return nil,
                o.name ..
                " did not match the native-call fingerprint; " ..
                "expected " .. hex32(o.gadget_word) ..
                ", got " .. tostring(word and hex32(word) or word)
        end
    end

    return o, nil
end

local function signed32(v)
    v = v & 0xFFFFFFFF
    if v >= 0x80000000 then
        return v - 0x100000000
    end
    return v
end

local function load_module(load_fn, name)
    if not load_fn then return nil end

    local ok, h = pcall(
        load_fn,
        name,
        0, 0, 0, 0, 0, 0
    )

    if not ok or type(h) ~= "number" then
        return nil
    end

    if h <= 0 or (h & 0x80000000) ~= 0 then
        return nil
    end

    return h
end

local function resolve_fn(handle, name)
    if not handle then return nil end

    local addr = dlsym(handle, name)
    if not addr or addr == 0 then return nil end

    return func_wrap(addr)
end

local function try_video_open(fn)
    if not fn then return -1 end

    local types = {0xFF, 0, 1, 2}

    for _, t in ipairs(types) do
        local ok, raw = pcall(fn, t, 0, 0, 0)

        if ok and type(raw) == "number" then
            -- VideoOut handles are signed 32-bit values, but they are NOT
            -- fd-like small integers. Large positive handles are valid.
            local h = signed32(raw)

            if h >= 0 then
                log("sceVideoOutOpen type=" ..
                    string.format("0x%X", t) ..
                    " -> handle=" .. tostring(h) ..
                    " (" .. hex32(h) .. ")")
                return h
            end
        end
    end

    return -1
end

local function get_user_id(load_fn)
    local h =
        load_module(load_fn, "libSceUserService.sprx")

    if not h then
        if type(USER_ID) == "number" and USER_ID >= 0 then
            return USER_ID
        end

        return -1
    end

    local get_initial =
        resolve_fn(h, "sceUserServiceGetInitialUser")

    if not get_initial then
        if type(USER_ID) == "number" and USER_ID >= 0 then
            return USER_ID
        end

        return -1
    end

    local p = malloc(4)
    zero_mem(p, 4)

    local ok, ret =
        pcall(
            get_initial,
            p,
            0, 0, 0, 0, 0
        )

    local user_id =
        read32(p) & 0xFFFFFFFF

    log("sceUserServiceGetInitialUser -> " ..
        tostring(ret) ..
        (type(ret) == "number"
            and (" (" .. hex32(ret) .. ")")
            or "") ..
        ", user=" .. tostring(user_id))

    if ok and ret == 0 then
        return user_id
    end

    if type(USER_ID) == "number" and USER_ID >= 0 then
        return USER_ID
    end

    return -1
end

-- ============================================================
-- Native controller wait loop
-- ============================================================
--
-- This path uses one native GetHandle/Read flow:
--
--   Lua resolves/passes:
--     scePadInit
--     scePadGetHandle
--     scePadRead
--     sceKernelUsleep
--     userId
--
--   Native main-thread helper:
--     scePadInit()
--     scePadGetHandle(userId, 0, 0)
--     loop:
--       scePadRead(handle, pad_buf, 1)
--       raw = *(u32*)pad_buf
--       reject raw bit31
--       return on a D-Pad/CROSS/CIRCLE/OPTIONS edge
--
-- There is NO alternate controller path here.
-- Input is intentionally limited to the native GetHandle/Read flow.
--
-- The first 0x30 bytes are the native-call trampoline; _start begins
-- at RX + 0x30.
local NATIVE_PAD_WAIT_HEX =
    "534889f34889f84889d74889ce4c89c24c89c94c8b4424104c8b4c2418ffd05bc3662e0f1f8400000000000f1f440000554157415641554154534881eca80000004d89cd4c89c348894c24184889d54989ff4885f674190f57c00f1104244c89ff31d231c94531c04531c9e890ffffff41be010000f04885ed0f84250100000f57c00f1104244531e44c89ff4889ee4c89ea31c94531c04531c9e861ffffff4989c54585ed0f98c048837c2418000f94c108c10f85eb0000004181e5ffffff7fbde20400004531f6eb0e660f1f440000ffcd0f84aa0000000f57c00f294424200f294424300f294424400f294424500f294424600f294424700f298424800000000f298424900000000f11042441b8010000004c89ff488b7424184c89ea488d4c24204531c9e8d5feffff85c07e268b44242085c0781e25ffff1f0041f7d44489e121c141be010000004189c4f7c158600000754c4885db0f8472ffffff0f57c00f110424baa00f00004c89ff4889de31c94531c04531c9e883feffffe94effffffb9010000f0488d81ffffffef4881c1ffffff8f4585f64989ce4c0f45f0eb034189ce4c89f04881c4a80000005b415c415d415e415f5dc3"

local NATIVE_PAD_WAIT_ENTRY = 0x30
local function map_native_pad_wait()
    if type(jit_malloc) ~= "function" or
       type(jit_write_buffer) ~= "function" or
       type(jit_read32) ~= "function" or
       type(jit_read64) ~= "function" or
       type(jit_sceKernelJitCreateSharedMemory) ~= "function" or
       type(jit_sceKernelJitCreateAliasOfSharedMemory) ~= "function" or
       type(jit_sceKernelJitMapSharedMemory) ~= "function" or
       type(jit_send_recv_fd) ~= "function" or
       type(write_shellcode) ~= "function" then
        return nil, "JIT helpers unavailable"
    end

    if type(NEW_JIT_SOCK) ~= "number" or
       type(NEW_MAIN_SOCK) ~= "number" then
        return nil, "JIT fd-pass sockets unavailable"
    end

    local main_jit_map = sceKernelJitMapSharedMemory
    if type(main_jit_map) ~= "function" then
        local a = dlsym(LIBKERNEL_HANDLE, "sceKernelJitMapSharedMemory")
        if not a or a == 0 then
            return nil, "sceKernelJitMapSharedMemory unresolved"
        end
        main_jit_map = func_wrap(a)
    end

    local PROT_READ = 1
    local PROT_WRITE = 2
    local PROT_EXEC = 4
    local JIT_SIZE = 0x10000

    local bfd = jit_malloc(8)
    local rwfd = jit_malloc(8)
    local rxfd = jit_malloc(8)
    local rwa = jit_malloc(8)
    local rxa = malloc(8)
    local nm = jit_malloc(8)

    if not bfd or not rwfd or not rxfd or
       not rwa or not rxa or not nm then
        return nil, "native pad JIT allocation failed"
    end

    jit_write_buffer(nm, "npad")

    local r = jit_sceKernelJitCreateSharedMemory(
        nm, JIT_SIZE, 7, bfd
    )
    if r ~= 0 then
        return nil, "JitCreateSharedMemory failed: " .. tostring(r)
    end

    r = jit_sceKernelJitCreateAliasOfSharedMemory(
        jit_read32(bfd), PROT_READ | PROT_WRITE, rwfd
    )
    if r ~= 0 then
        return nil, "JitCreateAlias RW failed: " .. tostring(r)
    end

    r = jit_sceKernelJitCreateAliasOfSharedMemory(
        jit_read32(bfd), PROT_READ | PROT_EXEC, rxfd
    )
    if r ~= 0 then
        return nil, "JitCreateAlias RX failed: " .. tostring(r)
    end

    r = jit_sceKernelJitMapSharedMemory(
        jit_read32(rwfd), PROT_READ | PROT_WRITE, rwa
    )
    if r ~= 0 then
        return nil, "JitMapSharedMemory RW failed: " .. tostring(r)
    end

    local rw = jit_read64(rwa)

    local mfd = jit_send_recv_fd(
        jit_read32(rxfd), NEW_JIT_SOCK, NEW_MAIN_SOCK
    )
    if type(mfd) ~= "number" or mfd < 0 then
        return nil, "native pad RX fd pass failed: " .. tostring(mfd)
    end

    zero_mem(rxa, 8)
    r = main_jit_map(mfd, PROT_READ | PROT_EXEC, rxa)
    if r ~= 0 then
        return nil, "main JitMapSharedMemory RX failed: " .. tostring(r)
    end

    local rx = read64(rxa)
    if not rx or rx == 0 then
        return nil, "native pad RX mapping returned null"
    end

    write_shellcode(rw, NATIVE_PAD_WAIT_HEX)

    return rx + NATIVE_PAD_WAIT_ENTRY, nil
end

local function init_ui(load_fn, usleep_fn)
    local ui = {
        video_h = -1,
        video_taken_over = false,
        pad_h = -1,
        usleep_fn = usleep_fn,
        pad_owned = false,
        vmem = 0,
        phys = 0,
        frame = 0
    }

    -- libc memory primitives. memset accelerates flat fills; memcpy keeps
    -- the inactive framebuffer synchronized with the currently displayed
    -- frame so cursor moves only need to repaint two rows.
    local libc_h =
        load_module(load_fn, "libSceLibcInternal.sprx")

    if libc_h then
        ui.memset = resolve_fn(libc_h, "memset")
        ui.memcpy = resolve_fn(libc_h, "memcpy")
    end

    -- VideoOut.
    local video_hmod =
        load_module(load_fn, "libSceVideoOut.sprx")

    ui.vid_open =
        resolve_fn(video_hmod, "sceVideoOutOpen")

    ui.vid_close =
        resolve_fn(video_hmod, "sceVideoOutClose")

    ui.vid_reg =
        resolve_fn(video_hmod, "sceVideoOutRegisterBuffers")

    ui.vid_flip =
        resolve_fn(video_hmod, "sceVideoOutSubmitFlip")

    ui.vid_rate =
        resolve_fn(video_hmod, "sceVideoOutSetFlipRate")

    ui.vid_evt =
        resolve_fn(video_hmod, "sceVideoOutAddFlipEvent")

    if not ui.vid_open or
       not ui.vid_reg or
       not ui.vid_flip then
        return nil, "VideoOut symbols unavailable"
    end

    ui.video_h = try_video_open(ui.vid_open)

    -- If VideoOut is already owned by the game, use the same validated
    -- host takeover sequence as the framebuffer examples.
    if ui.video_h < 0 then
        -- Select the known EU/US patch profile before touching host
        -- VideoOut state.  This prevents the US app0 EBOOT from receiving
        -- patch0 offsets.
        local eboot_o, eboot_err = select_eboot_offsets()
        if not eboot_o then
            return nil,
                "VideoOut busy; " .. tostring(eboot_err)
        end

        local base = EBOOT_BASE

        log("using EBOOT offset profile: " .. eboot_o.name)

        local emu_vid =
            signed32(read32(base + eboot_o.vidout))

        local gs_thread =
            read64(base + eboot_o.gs_thread)

        log("VideoOut busy; host state:")
        log("  emu_vid   = " .. tostring(emu_vid) ..
            " (" .. hex32(emu_vid) .. ")")
        log("  gs_thread = " .. tostring(gs_thread))

        -- The hardware-tested framebuffer examples treat EBOOT_VIDOUT
        -- as a signed 32-bit VideoOut handle. It may be a large positive
        -- value (for example 0x4E100000); unlike file descriptors there is
        -- no <0x10000 requirement.
        if emu_vid < 0 then
            return nil,
                "host VideoOut handle is negative/invalid: " ..
                tostring(emu_vid) .. " (" .. hex32(emu_vid) .. ")"
        end

        if not gs_thread or gs_thread == 0 then
            return nil,
                "host graphics thread failed sanity check"
        end

        local cancel_addr =
            dlsym(LIBKERNEL_HANDLE, "scePthreadCancel")

        local cancel_fn =
            cancel_addr and cancel_addr ~= 0
            and func_wrap(cancel_addr)
            or nil

        if not cancel_fn or not ui.vid_close then
            return nil,
                "host takeover functions unavailable"
        end

        local ok_cancel, cancel_ret =
            pcall(cancel_fn, gs_thread)

        log("  scePthreadCancel -> " ..
            tostring(cancel_ret) ..
            (type(cancel_ret) == "number"
                and (" (" .. hex32(cancel_ret) .. ")")
                or ""))

        if usleep_fn then
            pcall(usleep_fn, 300000)
        end

        local ok_close, close_ret =
            pcall(ui.vid_close, emu_vid)

        log("  sceVideoOutClose(host) -> " ..
            tostring(close_ret) ..
            (type(close_ret) == "number"
                and (" (" .. hex32(close_ret) .. ")")
                or ""))

        if usleep_fn then
            pcall(usleep_fn, 100000)
        end

        ui.video_h = try_video_open(ui.vid_open)
        ui.video_taken_over = ui.video_h >= 0

        if not ui.video_taken_over then
            log("  VideoOut reopen failed after host takeover")
        end
    end

    if ui.video_h < 0 then
        return nil, "sceVideoOutOpen failed"
    end

    -- native display timing:
    -- create a kernel equeue and attach VideoOut flip events. Every frame
    -- will SubmitFlip and then block in sceKernelWaitEqueue.
    local create_eq_addr =
        dlsym(LIBKERNEL_HANDLE, "sceKernelCreateEqueue")

    local wait_eq_addr =
        dlsym(LIBKERNEL_HANDLE, "sceKernelWaitEqueue")

    local delete_eq_addr =
        dlsym(LIBKERNEL_HANDLE, "sceKernelDeleteEqueue")

    if create_eq_addr and create_eq_addr ~= 0 and
       wait_eq_addr and wait_eq_addr ~= 0 and
       ui.vid_evt then

        ui.create_eq = func_wrap(create_eq_addr)
        ui.wait_eq = func_wrap(wait_eq_addr)

        if delete_eq_addr and delete_eq_addr ~= 0 then
            ui.delete_eq = func_wrap(delete_eq_addr)
        end

        local eq_p = malloc(8)
        zero_mem(eq_p, 8)

        local ok_eq, eq_ret =
            pcall(
                ui.create_eq,
                eq_p,
                "usbfb",
                0, 0, 0, 0
            )

        if ok_eq and eq_ret == 0 then
            ui.eq = read64(eq_p)

            if ui.eq and ui.eq ~= 0 then
                local ok_fe, fe_ret =
                    pcall(
                        ui.vid_evt,
                        ui.eq,
                        ui.video_h,
                        0,
                        0, 0, 0
                    )

                log("sceVideoOutAddFlipEvent -> " ..
                    tostring(fe_ret) ..
                    (type(fe_ret) == "number"
                        and (" (" .. hex32(fe_ret) .. ")")
                        or ""))

                if not ok_fe or fe_ret ~= 0 then
                    ui.eq = 0
                end
            end
        end

        if ui.eq and ui.eq ~= 0 then
            ui.flip_evt = malloc(64)
            ui.flip_cnt = malloc(4)
            zero_mem(ui.flip_evt, 64)
            zero_mem(ui.flip_cnt, 4)

            log("flip equeue ready: " ..
                tostring(ui.eq))
        else
            log("flip equeue creation/registration failed; continuing unsynchronised")
        end
    else
        log("flip equeue symbols unavailable; continuing unsynchronised")
    end

    -- Direct-memory framebuffer allocation.
    local alloc_addr =
        dlsym(
            LIBKERNEL_HANDLE,
            "sceKernelAllocateDirectMemory"
        )

    local map_addr =
        dlsym(
            LIBKERNEL_HANDLE,
            "sceKernelMapDirectMemory"
        )

    local release_addr =
        dlsym(
            LIBKERNEL_HANDLE,
            "sceKernelReleaseDirectMemory"
        )

    local munmap_addr =
        dlsym(
            LIBKERNEL_HANDLE,
            "munmap"
        )

    if not munmap_addr or munmap_addr == 0 then
        munmap_addr =
            dlsym(
                LIBKERNEL_HANDLE,
                "sceKernelMunmap"
            )
    end

    if not alloc_addr or alloc_addr == 0 or
       not map_addr or map_addr == 0 then
        return nil, "direct-memory functions unavailable"
    end

    ui.alloc_dm = func_wrap(alloc_addr)
    ui.map_dm = func_wrap(map_addr)

    if release_addr and release_addr ~= 0 then
        ui.release_dm = func_wrap(release_addr)
    end

    if munmap_addr and munmap_addr ~= 0 then
        ui.munmap = func_wrap(munmap_addr)
    end

    local phys_p = malloc(8)
    local vmem_p = malloc(8)

    zero_mem(phys_p, 8)
    zero_mem(vmem_p, 8)

    local ok_alloc, ar = pcall(
        ui.alloc_dm,
        0,
        0x300000000,
        UI_FB_TOTAL,
        0x200000,
        3,
        phys_p
    )

    if not ok_alloc or ar ~= 0 then
        return nil,
            "sceKernelAllocateDirectMemory failed: " ..
            tostring(ar)
    end

    ui.phys = read64(phys_p)

    local ok_map, mr = pcall(
        ui.map_dm,
        vmem_p,
        UI_FB_TOTAL,
        0x33,
        0,
        ui.phys,
        0x200000
    )

    if not ok_map or mr ~= 0 then
        return nil,
            "sceKernelMapDirectMemory failed: " ..
            tostring(mr)
    end

    ui.vmem = read64(vmem_p)

    if not ui.vmem or ui.vmem == 0 then
        return nil, "mapped framebuffer pointer is null"
    end

    ui.fb0 = ui.vmem
    ui.fb1 = ui.vmem + UI_FB_ALIGNED

    local attr = malloc(64)
    local fbs = malloc(16)

    zero_mem(attr, 64)
    zero_mem(fbs, 16)

    write32(attr + 0, 0x80000000)
    write32(attr + 4, 1)
    write32(attr + 12, UI_W)
    write32(attr + 16, UI_H)
    write32(attr + 20, UI_W)

    write64(fbs + 0, ui.fb0)
    write64(fbs + 8, ui.fb1)

    local ok_reg, rr = pcall(
        ui.vid_reg,
        ui.video_h,
        0,
        fbs,
        2,
        attr,
        0
    )

    if not ok_reg or rr ~= 0 then
        return nil,
            "sceVideoOutRegisterBuffers failed: " ..
            tostring(rr)
    end

    if ui.vid_rate then
        local ok_fr, fr_ret =
            pcall(
                ui.vid_rate,
                ui.video_h,
                0,
                0, 0, 0, 0
            )

        log("sceVideoOutSetFlipRate(0) -> " ..
            tostring(fr_ret) ..
            (type(fr_ret) == "number"
                and (" (" .. hex32(fr_ret) .. ")")
                or ""))
    end

    -- Clear both buffers before first use.
    fb_clear(ui, ui.fb0)
    fb_clear(ui, ui.fb1)

    -- Native pad setup.
    local pad_hmod =
        load_module(load_fn, "libScePad.sprx")

    if not pad_hmod then
        return nil, "libScePad.sprx failed to load"
    end

    ui.pad_init_addr =
        dlsym(pad_hmod, "scePadInit")
    ui.pad_get_addr =
        dlsym(pad_hmod, "scePadGetHandle")
    ui.pad_read_addr =
        dlsym(pad_hmod, "scePadRead")

    if not ui.pad_init_addr or ui.pad_init_addr == 0 or
       not ui.pad_get_addr or ui.pad_get_addr == 0 or
       not ui.pad_read_addr or ui.pad_read_addr == 0 then
        return nil, "required pad symbols unavailable"
    end

    local user_id = get_user_id(load_fn)

    if user_id < 0 then
        return nil, "could not obtain initial user id"
    end

    ui.pad_user_id = user_id

    local wait_entry, wait_err =
        map_native_pad_wait()

    if not wait_entry then
        return nil,
            "native pad wait map failed: " ..
            tostring(wait_err)
    end

    ui.pad_wait_addr = wait_entry
    ui.pad_wait_fn = func_wrap(wait_entry)
    local eboot_o, eboot_err = select_eboot_offsets()
    if not eboot_o then
        return nil,
            "native pad offsets unavailable: " .. tostring(eboot_err)
    end

    ui.pad_gadget =
        EBOOT_BASE + eboot_o.pad_gadget
    ui.pad_usleep_addr =
        dlsym(
            LIBKERNEL_HANDLE,
            "sceKernelUsleep"
        )

    log("native pad path ready")
    log("  userId   = " ..
        tostring(ui.pad_user_id) ..
        " (" .. hex32(ui.pad_user_id) .. ")")
    log("  gadget   = " ..
        tostring(ui.pad_gadget))
    log("  wait RX  = " ..
        tostring(ui.pad_wait_addr))

    log("GUI framebuffer ready")
    log("  video handle = " .. tostring(ui.video_h))
    log("  pad handle   = " .. tostring(ui.pad_h))
    log("  framebuffer  = " .. tostring(ui.vmem))

    return ui, nil
end

function ui_next_fb(ui)
    local idx = ui.frame & 1
    return (idx == 0) and ui.fb0 or ui.fb1
end

function ui_front_fb(ui)
    -- ui.frame is incremented after SubmitFlip, so frame-1 is the currently
    -- displayed framebuffer.
    local idx = (ui.frame - 1) & 1
    return (idx == 0) and ui.fb0 or ui.fb1
end

function ui_draw_next(ui, state)
    -- True double buffering: NEVER paint the buffer currently being scanned
    -- out. Render the complete next frame into the inactive buffer, then
    -- ui_flip_sync() submits that buffer atomically on the next flip event.
    render_browser(ui, ui_next_fb(ui), state)
end

function ui_sync_backbuffer(ui)
    if not ui.memcpy or ui.frame <= 0 then
        return false
    end

    local src = ui_front_fb(ui)
    local dst = ui_next_fb(ui)

    local ok =
        pcall(
            ui.memcpy,
            dst,
            src,
            UI_FB_SIZE
        )

    return ok
end

function ui_draw_cursor_move(
    ui,
    state,
    old_cursor,
    old_status_text,
    new_status_text
)
    local fb = ui_next_fb(ui)

    -- Because the inactive buffer is synchronized after every flip, only
    -- these two rows differ for an ordinary Up/Down navigation event.
    render_entry_row(
        ui, fb, state, old_cursor
    )

    if state.cursor ~= old_cursor then
        render_entry_row(
            ui, fb, state, state.cursor
        )
    end

    if old_status_text ~= new_status_text then
        render_footer_status(ui, fb, state)
    end
end

function ui_flip_sync(ui)
    local idx = ui.frame & 1

    local ok, ret = pcall(
        ui.vid_flip,
        ui.video_h,
        idx,
        1,
        ui.frame,
        0,
        0
    )

    if not ok then
        return false,
            "sceVideoOutSubmitFlip threw: " ..
            tostring(ret)
    end

    if type(ret) == "number" and ret ~= 0 then
        return false,
            "sceVideoOutSubmitFlip returned " ..
            tostring(ret) ..
            " (" .. hex32(ret) .. ")"
    end

    -- Exact frame cadence: after every SubmitFlip, block for the flip event.
    if ui.eq and ui.eq ~= 0 and
       ui.wait_eq and
       ui.flip_evt and
       ui.flip_cnt then

        zero_mem(ui.flip_evt, 64)
        zero_mem(ui.flip_cnt, 4)

        local ok_w, wr =
            pcall(
                ui.wait_eq,
                ui.eq,
                ui.flip_evt,
                1,
                ui.flip_cnt,
                0,
                0
            )

        if not ok_w then
            return false,
                "sceKernelWaitEqueue threw: " ..
                tostring(wr)
        end

        if type(wr) == "number" and wr ~= 0 then
            return false,
                "sceKernelWaitEqueue returned " ..
                tostring(wr) ..
                " (" .. hex32(wr) .. ")"
        end
    end

    ui.frame = ui.frame + 1
    return true, nil
end

function ui_present_back_only(
    ui,
    title,
    filename,
    line1,
    line2,
    accent
)
    render_back_only_screen(
        ui,
        ui_next_fb(ui),
        title,
        filename,
        line1,
        line2,
        accent
    )

    local ok, err =
        ui_flip_sync(ui)

    if not ok then
        return false, err
    end

    ui_sync_backbuffer(ui)

    while true do
        local pressed =
            ui_read_buttons(ui)

        if (pressed & PAD_CIRCLE) ~= 0 then
            return true, nil
        end
    end
end

function ui_present_launching(
    ui,
    filename
)
    render_launch_screen(
        ui,
        ui_next_fb(ui),
        filename
    )

    local ok, err =
        ui_flip_sync(ui)

    if ok then
        ui_sync_backbuffer(ui)
    end

    return ok, err
end

ui_read_buttons = function(ui)
    if not ui.pad_wait_fn then
        return 0
    end

    -- This call stays inside native x86-64 code while waiting for input.
    -- That matches the menu execution model much more closely than
    -- polling from Lua or from a helper pthread.
    local ok, raw_ret =
        pcall(
            ui.pad_wait_fn,
            ui.pad_gadget,
            ui.pad_init_addr,
            ui.pad_get_addr,
            ui.pad_read_addr,
            ui.pad_usleep_addr or 0,
            ui.pad_user_id
        )

    if not ok or type(raw_ret) ~= "number" then
        log("native pad wait invocation failed: " ..
            tostring(raw_ret))
        return 0
    end

    local ret =
        raw_ret & 0xFFFFFFFF

    if ret == 0x80000000 then
        log("native pad wait: only intercepted samples during window")
        return 0
    end

    if ret == 0xE0000000 then
        -- Valid non-intercepted samples existed, but no navigation button
        -- was pressed during the wait window.
        return 0
    end

    if ret == 0xF0000001 then
        log("native pad wait: scePadGetHandle/read setup failed")
        return 0
    end

    local buttons =
        ret & 0x001FFFFF

    if buttons ~= 0 then
        log("native edge -> " ..
            hex32(buttons))
    end

    return buttons
end

local function cleanup_ui(ui)
    if not ui then return end

    if ui.delete_eq and
       ui.eq and ui.eq ~= 0 then
        pcall(
            ui.delete_eq,
            ui.eq,
            0, 0, 0, 0, 0
        )
        ui.eq = 0
    end

    if ui.vid_close and ui.video_h >= 0 then
        pcall(ui.vid_close, ui.video_h)
    end

    if ui.munmap and
       ui.vmem and ui.vmem ~= 0 then
        pcall(
            ui.munmap,
            ui.vmem,
            UI_FB_TOTAL
        )
    end

    if ui.release_dm and
       ui.phys and ui.phys ~= 0 then
        pcall(
            ui.release_dm,
            ui.phys,
            UI_FB_TOTAL
        )
    end
end

-- ============================================================
-- USB cleanup
-- ============================================================

local function cleanup_usb(io)
    if not io then return end

    if io.out_opened then
        fs_close(io.ioctl_fn, io.fd, SLOT_OUT)
    end

    if io.in_opened then
        fs_close(io.ioctl_fn, io.fd, SLOT_IN)
    end

    if io.fs_initialized then
        local p = malloc(4)
        zero_mem(p, 4)
        ioctl_call(io.ioctl_fn, io.fd, USB_FS_UNINIT, p)
    end

    if io.claimed then
        ioctl_call(
            io.ioctl_fn,
            io.fd,
            USB_RELEASE_INTERFACE,
            make_iface_arg(io.iface)
        )
    end

    if valid_fd(io.fd) then
        pcall(sceKernelClose, io.fd)
    end
end

-- ============================================================
-- Browser state / navigation
-- ============================================================

local function make_dir_from_entry(parent_path, e)
    return {
        is_root = false,
        path = path_join(parent_path, e.name),
        name = e.name,
        first_cluster = e.first_cluster,
        data_length = e.data_length,
        no_fat_chain = e.no_fat_chain
    }
end

local function make_browser_state(
    entries,
    path,
    volume_label,
    capacity_text
)
    return {
        entries = entries or {},
        path = path or "/",
        cursor = (#(entries or {}) > 0) and 1 or 0,
        scroll = 1,
        status = nil,
        volume_label = volume_label or "",
        capacity_text = capacity_text or ""
    }
end

local function clamp_scroll(state)
    local count = #state.entries

    if count == 0 then
        state.cursor = 0
        state.scroll = 1
        return
    end

    if state.cursor < 1 then state.cursor = 1 end
    if state.cursor > count then state.cursor = count end

    if state.cursor < state.scroll then
        state.scroll = state.cursor
    end

    if state.cursor >=
       state.scroll + MAX_VISIBLE then
        state.scroll =
            state.cursor - MAX_VISIBLE + 1
    end

    local max_scroll =
        math.max(1, count - MAX_VISIBLE + 1)

    if state.scroll > max_scroll then
        state.scroll = max_scroll
    end
end

-- ============================================================
-- MAIN
-- ============================================================

log("graphical exFAT payload browser started")
log("PLATFORM = " .. tostring(PLATFORM))
log("FW_VERSION = " .. tostring(FW_VERSION))
log("TITLE_ID = " .. tostring(TITLE_ID))
log("")

local ok_init, init_err = pcall(init_dlsym)
if not ok_init then
    log("init_dlsym failed: " .. tostring(init_err))
    return
end

-- Terminate any existing dialog immediately after init_dlsym(), before any native
-- VideoOut or pad setup. Leaving the loader/message-dialog state active can
-- leave controller reports system-intercepted (raw bit31 = 0x80000000).
if type(sceMsgDialogTerminate) == "function" then
    local ok_md, md_ret = pcall(sceMsgDialogTerminate)
    log("sceMsgDialogTerminate -> " ..
        tostring(md_ret) ..
        (type(md_ret) == "number"
            and (" (" .. hex32(md_ret) .. ")")
            or "") ..
        ", pcall=" .. tostring(ok_md))
else
    log("WARNING: sceMsgDialogTerminate unavailable")
end

local ioctl_addr =
    dlsym(LIBKERNEL_HANDLE, "sceKernelIoctl")

if not ioctl_addr or ioctl_addr == 0 then
    ioctl_addr =
        dlsym(LIBKERNEL_HANDLE, "ioctl")
end

local load_addr =
    dlsym(
        LIBKERNEL_HANDLE,
        "sceKernelLoadStartModule"
    )

if not ioctl_addr or ioctl_addr == 0 or
   not load_addr or load_addr == 0 then
    log("required libkernel symbols unavailable")
    return
end

local ioctl_fn = func_wrap(ioctl_addr)
local load_fn = func_wrap(load_addr)

local usleep_fn = nil
local usleep_addr =
    dlsym(
        LIBKERNEL_HANDLE,
        "sceKernelUsleep"
    )

if usleep_addr and usleep_addr ~= 0 then
    usleep_fn = func_wrap(usleep_addr)
end

-- Discover the currently attached mass-storage stick.
local dev = discover_mass_storage(ioctl_fn)

if not dev then
    log("No USB mass-storage device found.")
    notify("USB File Browser: no USB drive found")
    return
end

local ok_open, fd =
    pcall(
        sceKernelOpen,
        dev.control,
        2,
        0
    )

if not ok_open or not valid_fd(fd) then
    log("control O_RDWR open failed: " ..
        tostring(fd) .. " (" .. hex32(fd) .. ")")
    return
end

local io = {
    ioctl_fn = ioctl_fn,
    usleep_fn = usleep_fn,
    fd = fd,
    iface = dev.iface,
    claimed = false,
    fs_initialized = false,
    out_opened = false,
    in_opened = false
}

local iface_arg =
    make_iface_arg(dev.iface)

if ioctl_call(
    ioctl_fn,
    fd,
    USB_IFACE_DRIVER_ACTIVE,
    iface_arg
) == 0 then

    log("kernel USB driver active; detaching interface " ..
        tostring(dev.iface))

    if ioctl_call(
        ioctl_fn,
        fd,
        USB_IFACE_DRIVER_DETACH,
        iface_arg
    ) ~= 0 then
        log("driver detach failed")
        cleanup_usb(io)
        return
    end
end

if ioctl_call(
    ioctl_fn,
    fd,
    USB_CLAIM_INTERFACE,
    make_iface_arg(dev.iface)
) ~= 0 then
    log("interface claim failed")
    cleanup_usb(io)
    return
end

io.claimed = true

local endpoints =
    malloc(USB_FS_ENDPOINT_SIZE * 2)

zero_mem(
    endpoints,
    USB_FS_ENDPOINT_SIZE * 2
)

local fs_init = malloc(0x10)
zero_mem(fs_init, 0x10)

write64(fs_init + 0x00, endpoints)
set_u8(fs_init, 0x08, 2)

if ioctl_call(
    ioctl_fn,
    fd,
    USB_FS_INIT,
    fs_init
) ~= 0 then
    log("USB_FS_INIT failed")
    cleanup_usb(io)
    return
end

io.fs_initialized = true
io.endpoints = endpoints

io.out_opened =
    fs_open(
        ioctl_fn,
        fd,
        SLOT_OUT,
        dev.ep_out
    )

io.in_opened =
    fs_open(
        ioctl_fn,
        fd,
        SLOT_IN,
        dev.ep_in
    )

if not io.out_opened or not io.in_opened then
    cleanup_usb(io)
    return
end

io.out_pp = malloc(8)
io.out_len = malloc(4)
io.in_pp = malloc(8)
io.in_len = malloc(4)

local last_lba, block_size, cap_err =
    scsi_read_capacity(io)

if not block_size then
    log("READ CAPACITY failed: " ..
        tostring(cap_err))
    cleanup_usb(io)
    return
end

io.block_size = block_size
io.max_blocks_per_read =
    math.floor(
        MAX_USBFS_BYTES /
        block_size
    )

if io.max_blocks_per_read < 1 then
    log("logical block size exceeds USB_FS buffer")
    cleanup_usb(io)
    return
end

local partition_lba, boot, find_err =
    find_exfat_volume(io)

if not partition_lba then
    log("exFAT discovery failed: " ..
        tostring(find_err))
    cleanup_usb(io)
    return
end

local g, geom_err =
    parse_exfat_geometry(
        partition_lba,
        boot,
        block_size
    )

if not g then
    log("exFAT geometry failed: " ..
        tostring(geom_err))
    cleanup_usb(io)
    return
end

local read_fat =
    make_fat_reader(io, g)

local root_dir = {
    is_root = true,
    path = "/",
    name = "/",
    first_cluster = g.root_cluster,
    data_length = nil,
    no_fat_chain = false
}

local root_entries, root_meta, root_err =
    read_directory_entries(
        io,
        g,
        read_fat,
        root_dir
    )

if not root_entries then
    log("root directory read failed: " ..
        tostring(root_err))
    cleanup_usb(io)
    return
end

local total_bytes =
    (last_lba + 1) * block_size

local capacity_text =
    string.format(
        "%.2f GB",
        total_bytes /
        (1024 * 1024 * 1024)
    )

local volume_label =
    root_meta.volume_label or "USB"

log("USB ready for GUI:")
log("  volume = " .. tostring(volume_label))
log("  root entries = " .. tostring(#root_entries))
log("  capacity = " .. capacity_text)

-- Start native framebuffer UI.
local ui, ui_err =
    init_ui(load_fn, usleep_fn)

if not ui then
    log("GUI initialization failed: " ..
        tostring(ui_err))
    notify(
        "USB File Browser GUI failed: " ..
        tostring(ui_err)
    )
    cleanup_usb(io)
    return
end

local state =
    make_browser_state(
        root_entries,
        "/",
        volume_label,
        capacity_text
    )

local current_dir = root_dir
local stack = {}
local done = false
local dirty = true

state.status =
    tostring(#root_entries) ..
    (#root_entries == 1 and " ITEM" or " ITEMS")

-- Render a complete initial frame into the next scanout buffer, then flip
-- to it. From this point onward the other buffer is always our backbuffer.
ui_draw_next(ui, state)

local initial_flip_ok, initial_flip_err =
    ui_flip_sync(ui)

if not initial_flip_ok then
    log("Initial VideoOut flip failed: " ..
        tostring(initial_flip_err))
    cleanup_usb(io)
    cleanup_ui(ui)
    return
end

-- Keep the inactive framebuffer identical to the displayed one while we wait
-- for input. Cursor movement can then modify only two rows.
ui_sync_backbuffer(ui)

dirty = false

while not done do
    local old_state = state
    local old_cursor = state.cursor
    local old_scroll = state.scroll
    local old_status_text = browser_status_text(state)
    local fast_cursor_move = false

    local pressed = ui_read_buttons(ui)

    if (pressed & PAD_OPTIONS) ~= 0 then
        done = true

    elseif (pressed & PAD_DOWN) ~= 0 then
        if state.cursor > 0 and
           state.cursor < #state.entries then
            state.cursor = state.cursor + 1
            state.status = nil
            clamp_scroll(state)
            fast_cursor_move =
                (state == old_state and
                 state.scroll == old_scroll)
            dirty = true
        end

    elseif (pressed & PAD_UP) ~= 0 then
        if state.cursor > 1 then
            state.cursor = state.cursor - 1
            state.status = nil
            clamp_scroll(state)
            fast_cursor_move =
                (state == old_state and
                 state.scroll == old_scroll)
            dirty = true
        end

    elseif (pressed & PAD_CROSS) ~= 0 then
        if state.cursor > 0 then
            local e =
                state.entries[state.cursor]

            if e and e.is_dir then
                local child =
                    make_dir_from_entry(
                        current_dir.path,
                        e
                    )

                local child_entries,
                      child_meta,
                      child_err =
                    read_directory_entries(
                        io,
                        g,
                        read_fat,
                        child
                    )

                if child_entries then
                    stack[#stack + 1] = {
                        dir = current_dir,
                        state = state
                    }

                    current_dir = child

                    state =
                        make_browser_state(
                            child_entries,
                            child.path,
                            volume_label,
                            capacity_text
                        )

                    state.status =
                        tostring(#child_entries) ..
                        (#child_entries == 1
                            and " ITEM"
                            or " ITEMS")

                    dirty = true
                else
                    state.status =
                        "OPEN FAILED: " ..
                        tostring(child_err)

                    dirty = true
                end

            elseif e then
                if not is_lua_filename(e.name) then
                    local ok_modal, modal_err =
                        ui_present_back_only(
                            ui,
                            "CANNOT EXECUTE",
                            e.name,
                            "THIS FILE WILL NOT EXECUTE.",
                            "ONLY .LUA FILES CAN BE LAUNCHED.",
                            COL_PINK
                        )

                    if not ok_modal then
                        log(
                            "non-Lua modal failed: " ..
                            tostring(modal_err)
                        )
                        done = true
                    else
                        -- Repaint the browser after Circle / Back.
                        ui_draw_next(ui, state)

                        local back_ok, back_err =
                            ui_flip_sync(ui)

                        if not back_ok then
                            log(
                                "browser restore flip failed: " ..
                                tostring(back_err)
                            )
                            done = true
                        else
                            ui_sync_backbuffer(ui)
                        end
                    end

                    dirty = false

                else
                    local full_path =
                        path_join(
                            current_dir.path,
                            e.name
                        )

                    log(
                        "reading Lua payload from USB: " ..
                        full_path ..
                        " (" ..
                        tostring(e.data_length or 0) ..
                        " bytes)"
                    )

                    local source, read_err =
                        read_file_contents(
                            io,
                            g,
                            read_fat,
                            e
                        )

                    if not source then
                        log(
                            "Lua payload read failed: " ..
                            tostring(read_err)
                        )

                        local ok_modal =
                            ui_present_back_only(
                                ui,
                                "LUA READ ERROR",
                                e.name,
                                "THE LUA FILE COULD NOT BE READ.",
                                fit_name(
                                    tostring(read_err),
                                    86
                                ),
                                COL_PINK
                            )

                        if not ok_modal then
                            done = true
                        else
                            ui_draw_next(ui, state)

                            local back_ok =
                                ui_flip_sync(ui)

                            if back_ok then
                                ui_sync_backbuffer(ui)
                            else
                                done = true
                            end
                        end

                        dirty = false

                    else
                        local chunk_name =
                            "@usb:" ..
                            full_path

                        local chunk, compile_err =
                            compile_usb_lua(
                                source,
                                chunk_name
                            )

                        if not chunk then
                            log(
                                "Lua compile failed: " ..
                                tostring(compile_err)
                            )

                            local ok_modal =
                                ui_present_back_only(
                                    ui,
                                    "LUA COMPILE ERROR",
                                    e.name,
                                    "THIS LUA FILE COULD NOT BE COMPILED.",
                                    fit_name(
                                        tostring(compile_err),
                                        86
                                    ),
                                    COL_PINK
                                )

                            if not ok_modal then
                                done = true
                            else
                                ui_draw_next(ui, state)

                                local back_ok =
                                    ui_flip_sync(ui)

                                if back_ok then
                                    ui_sync_backbuffer(ui)
                                else
                                    done = true
                                end
                            end

                            dirty = false

                        else
                            -- Compilation succeeded while the browser still
                            -- owns its UI and USB transport. Show a final
                            -- handoff screen, then release both before
                            -- executing the payload so it starts cleanly.
                            ui_present_launching(
                                ui,
                                e.name
                            )

                            log(
                                "launching USB Lua payload: " ..
                                full_path
                            )

                            cleanup_usb(io)
                            cleanup_ui(ui)

                            local ok_run, run_err =
                                pcall(chunk)

                            if not ok_run then
                                log(
                                    "USB Lua payload runtime error: " ..
                                    tostring(run_err)
                                )

                                pcall(
                                    send_notification,
                                    "Lua payload error: " ..
                                    tostring(run_err)
                                )
                            else
                                log(
                                    "USB Lua payload returned normally: " ..
                                    full_path
                                )
                            end

                            -- Launch is a one-way browser handoff. If the
                            -- payload returns, do not run browser cleanup a
                            -- second time against released resources.
                            return
                        end
                    end
                end
            end
        end

    elseif (pressed & PAD_CIRCLE) ~= 0 then
        if #stack > 0 then
            local prev =
                stack[#stack]

            stack[#stack] = nil
            current_dir = prev.dir
            state = prev.state
            state.status =
                tostring(#state.entries) ..
                (#state.entries == 1
                    and " ITEM"
                    or " ITEMS")

            clamp_scroll(state)
            dirty = true
        else
            state.status = "ALREADY AT USB ROOT"
            dirty = true
        end
    end


    if dirty then
        if fast_cursor_move and ui.memcpy then
            -- Fast hover path: the inactive buffer already mirrors the
            -- current screen, so repaint only the row losing selection and
            -- the row gaining selection.
            ui_draw_cursor_move(
                ui,
                state,
                old_cursor,
                old_status_text,
                browser_status_text(state)
            )
        else
            -- Folder changes, scroll-window changes and status-heavy actions
            -- still use a complete backbuffer render.
            ui_draw_next(ui, state)
        end

        local flip_ok, flip_err =
            ui_flip_sync(ui)

        if not flip_ok then
            log("VideoOut synchronized flip failed: " ..
                tostring(flip_err))
            done = true
        else
            -- Do this after the new frame is already visible. Native memcpy
            -- is fast and prepares the other framebuffer before the next
            -- controller event arrives.
            ui_sync_backbuffer(ui)
        end

        dirty = false
    end
end

-- Always release USB ownership before leaving.
cleanup_usb(io)

-- Close the UI resources last.
cleanup_ui(ui)

send_notification(
    "USB browser closed. Unplug/replug USB to restore mass storage."
)

log("Browser exited")
