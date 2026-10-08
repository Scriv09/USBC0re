# USBC0re

A graphical USB file browser and Lua payload launcher for PS4/PS5 built on top of [LuaC0re](https://github.com/Gezine/Luac0re), which allows the user to boot lua payloads directly from the usb drive instead of needing to be connected to a network.

# Requirements

* PS4 or PS5 console
* [LuaC0re](https://github.com/Gezine/Luac0re) set up and working.
* Star Wars Racer Revenge — US (CUSA03474) or EU (CUSA03492) disc or digital.
* USB has to be plugged into console before running the USBC0re payload.
* USB has to be in exFAT format.

# Usage

Send the payload to your console using RemoteLuaLoader.

Alternatively, rename the payload to auto.lua, decrypt your Luac0re save file, and place the payload inside the lua folder.

Once the payload is in place, re-encrypt the save file and transfer it back to your console.

# Credits

* [Gezine](https://github.com/Gezine/Luac0re) — LuaC0re framework and JIT exploit
* [shahrilnet](https://github.com/shahrilnet) & [null_ptr](https://github.com/n0llptr) - Code references from remote_lua_loader
* [ChampionLeake](https://github.com/ChampionLeake) - PS2 Star Wars Racer Revenge exploit writeup on psdevwiki
* [McCaulay](https://github.com/McCaulay) - [mast1c0re](https://mccaulay.co.uk/mast1c0re-part-2-arbitrary-ps2-code-execution/) writeup and Okage reference implementation
* [CTurt](https://github.com/CTurt) - mast1c0re writeup

# Disclaimer

For research and educational purposes only. Use at your own risk.
