# Roblox Studio Bytecode Cases

Use `studio_25_cases.luau` as a ModuleScript in Roblox Studio or in the environment you use to compile/dump bytecode. Only dump bytecode for scripts you own or are allowed to inspect.

## Workflow

1. Create a ModuleScript in Roblox Studio.
2. Paste the full contents of `studio_25_cases.luau` into it.
3. Dump that ModuleScript bytecode as base64.
4. Copy `bytecode-input.template.json` to `.live/roblox-bytecode.json`.
5. Paste your base64 into the `b` field.
6. Decode it:

```powershell
python .live\save_b64.py .live\roblox-bytecode.json
```

7. Test the decompiler:

```powershell
cargo run -p xtask -- decompile .live\studio_25_cases.luauc
cargo run -p xtask -- disasm .live\studio_25_cases.luauc
cargo run -p xtask -- cfg .live\studio_25_cases.luauc
```

If you split the cases into separate ModuleScripts, use the same JSON format with one entry per script name.
