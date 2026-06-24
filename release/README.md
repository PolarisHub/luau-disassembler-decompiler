# luau-disassembler v0.1.0 Windows release

This folder is the first Windows release package for `luau-disassembler`.

## Files

- `bin/luau-server.exe` - production release build of the localhost HTTP server.
- `example.luau` - Luau-side example client for calling the server.
- `smoke-test.ps1` - quick local health check for the packaged executable.
- `RELEASE_NOTES_v0.1.0.md` - notes to paste into the GitHub release.

## Run

```powershell
.\bin\luau-server.exe
```

The server listens on:

```text
http://127.0.0.1:7331
```

You can choose another loopback port:

```powershell
.\bin\luau-server.exe 127.0.0.1:9000
```

The server refuses non-loopback addresses by design. Keep it behind localhost and put any
public access behind an explicit reverse proxy that you control.

## Check

In another terminal:

```powershell
.\smoke-test.ps1
```

Expected health response:

```json
{"bytecode_versions":{"max":11,"min":3},"service":"luau-server","status":"ok"}
```

## API

`GET /health`

Returns server status and supported Luau bytecode versions.

`POST /disassemble`

Body:

```json
{"bytecode":"<base64 luau bytecode>","options":{"include_disassembly":true}}
```

`POST /decompile`

Body:

```json
{"bytecode":"<base64 luau bytecode>","options":{"include_disassembly":false}}
```

Use this only on bytecode you own or are explicitly allowed to inspect.
