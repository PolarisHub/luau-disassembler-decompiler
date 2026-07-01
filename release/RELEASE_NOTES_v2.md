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
- Recovers many common Luau control-flow shapes into structured `if`, loop, `break`, and `return` output instead of raw `goto`/`::L` labels.
- Prints safer Luau source for keyword table keys and discarded side-effect expressions.
- Includes readability improvements for table reconstruction, method/function formatting, float literals, and generated local names.
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
cargo clippy --workspace --all-targets
.\release\smoke-test.ps1
```

The release test suite also covers the Roblox in-game bytecode fixtures under
`roblox-studio-cases/in_game`, asserting that they decompile without raw labels/gotos and
that the generated Luau recompiles.

Use this tool only on bytecode you own or are explicitly allowed to inspect.
