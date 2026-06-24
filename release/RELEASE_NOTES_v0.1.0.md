# luau-disassembler v0.1.0

First Windows release of `luau-disassembler`.

## Included

- `luau-server.exe`: localhost-only HTTP API for Luau bytecode analysis.
- `example.luau`: Luau client example for `/health`, `/disassemble`, and `/decompile`.
- `smoke-test.ps1`: verifies the packaged server starts and answers `/health`.

## Capabilities

- Parses Luau bytecode versions 3 through 11.
- Automatically normalizes Roblox-encoded opcode bytes when detected.
- Serves resolved disassembly through `POST /disassemble`.
- Serves best-effort Luau reconstruction through `POST /decompile`.
- Returns structured JSON errors for malformed requests, parse failures, timeouts, and caught panics.
- Enforces loopback binding, a 16 MiB request limit, and a 10 second analysis budget.

## Windows quick start

```powershell
.\bin\luau-server.exe
.\smoke-test.ps1
```

Default server address:

```text
http://127.0.0.1:7331
```

## Verification

Built with:

```powershell
cargo build -p luau-server --release
```

Verified with:

```powershell
cargo test --workspace
```

Use this tool only on bytecode you own or are explicitly allowed to inspect.
