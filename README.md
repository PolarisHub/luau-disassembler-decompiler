# luau-disassembler

Converts Luau bytecode (the compiled chunk, raw bytes) into a resolved disassembly and a
best-effort Luau reconstruction, served over a localhost HTTP API. **Bytecode in, analysis
out.**

This is a reverse-engineering / program-analysis tool for inspecting compiled Luau you are
allowed to inspect (your own scripts, CTF artifacts, research).

## Supported bytecode versions

The reader supports the full range the Luau VM accepts: **bytecode versions 3–11**
(`LBC_BYTECODE_MIN`..`MAX`) and type-info versions 1–3. Unsupported version bytes are
rejected with a clear error; the version-0 "compile error" sentinel is surfaced as the
embedded message. The test corpus is compiled at **version 7** (`LBC_VERSION_TARGET`, the
stable default) with one version-11 sample to exercise feedback-vector parsing.

## The spec is the Luau source, not memory

The bytecode format is not guessed. It is transcribed from these files of the
[luau-lang/luau](https://github.com/luau-lang/luau) repository at tag **0.726**, vendored
under [`reference/luau-0.726/`](reference/luau-0.726):

| File | What it pins |
|------|--------------|
| `Common/include/Luau/Bytecode.h` | opcodes (`LOP_*`), field macros, constant tags, capture types, proto flags, version constants |
| `Common/include/Luau/BytecodeUtils.h` | `getOpLength` (which opcodes carry an AUX word) and the CFG helpers (`isJumpD`, `getJumpTarget`, …) |
| `VM/src/lvmload.cpp` | `luau_load` — the exact deserialization order (the reader's spec) |
| `Bytecode/src/BytecodeBuilder.cpp` | the writer and the `dumpInstruction`/`dumpConstant` text format we match |

## Roblox (obfuscated) bytecode

Roblox ships production bytecode in the standard Luau format but **encodes the opcode byte**
of every instruction (`encoded = realOp * 227 mod 256`) — so a raw `getscriptbytecode` dump
decodes to garbage opcodes under the open-source numbering. The reader handles this
automatically: [`parse_normalized`](crates/luau-bytecode/src/lib.rs) brute-forces the opcode
**decode multiplier** per chunk (the inverse, `203`, for current Roblox; `1` for normal
bytecode, which is then left untouched) and rewrites opcodes to the standard numbering before
analysis. The multiplier is reported back as `opcode_multiplier` in the server response (with
a diagnostic). Because it's detected per file rather than hard-coded, it survives Roblox
opcode-shuffle changes. `DUPTABLE` constant templates (`TABLE_WITH_CONSTANTS`, ubiquitous in
config modules) are reconstructed into real table literals.

## Architecture

A Cargo workspace, layered so each level is testable on its own; dependencies point one way
(`server → decompile → ir → disasm → bytecode`; `bytecode` depends on nothing external):

- **[`luau-bytecode`](crates/luau-bytecode)** — the reader. Bytes → a typed, validated
  `Module`. Every read is bounds-checked; the parser never panics, never reads out of
  bounds, and never allocates on an unchecked length field.
- **[`luau-disasm`](crates/luau-disasm)** — `Module` → a resolved instruction listing
  (constants inlined, imports as dotted paths, NAMECALL methods, jump labels, PC numbers).
  Output matches `luau-compile --text` instruction-for-instruction.
- **[`luau-ir`](crates/luau-ir)** — control-flow graph, dominators, post-dominators, and
  natural-loop (back-edge) detection.
- **[`luau-decompile`](crates/luau-decompile)** — IR → reconstructed Luau (AST, then
  printed).
- **[`luau-server`](crates/luau-server)** — the loopback HTTP server. Thin: it only wires
  the above together and handles I/O, limits, and errors.
- **[`xtask`](crates/xtask)** — developer CLI for eyeballing output.

## Building and testing

```sh
cargo build --workspace
cargo test  --workspace      # reader fuzz, disasm oracle, CFG, decompile round-trip, server e2e
cargo clippy --workspace --all-targets
```

### The compiler oracle

Correctness is checked against the real Luau compiler. Download the 0.726 Windows binaries
into `tools/` (git-ignored), then compile the corpus:

```sh
# tools/luau-compile.exe must exist (from the luau-lang/luau 0.726 release)
bash scripts/compile-corpus.sh        # corpus/src/*.luau -> corpus/bytecode/*.luauc (+ reference text)
```

The disassembler is snapshot-tested against its own golden files
(`corpus/expected-disasm/`) **and** diffed against `luau-compile --text`
(`corpus/expected-text/`). The decompiler's straight-line output is round-tripped: it is
recompiled with the real compiler and required to produce valid bytecode.

## Running the server

```sh
cargo run -p luau-server                 # binds 127.0.0.1:7331
cargo run -p luau-server -- 127.0.0.1:9000
```

It binds **loopback only** and refuses any non-loopback address. Limits: 16 MiB max body,
10 s per-request analysis budget, and a `catch_unwind` backstop so a bug becomes a
structured `500`, never a crash.

### Endpoints

`GET /health`
```json
{ "status": "ok", "service": "luau-server", "bytecode_versions": { "min": 3, "max": 11 } }
```

`POST /disassemble` — body `{ "bytecode": "<base64>", "options": { "include_disassembly": true } }`
```json
{
  "version": 7,
  "types_version": 3,
  "main_proto": 1,
  "proto_count": 2,
  "protos": [
    { "index": 0, "name": "classify", "num_params": 1, "num_upvalues": 0,
      "is_vararg": false, "max_stack_size": 2, "line_defined": 1,
      "instruction_count": 9, "listing": "    0       LOADN R1 0  ; line 2\n..." }
  ],
  "diagnostics": []
}
```

`POST /decompile` — body `{ "bytecode": "<base64>", "options": { "include_disassembly": false } }`
```json
{
  "source": "-- Decompiled by luau-decompile.\n\nlocal calc\ncalc = function(x, y)\n ...",
  "partial": false,
  "per_proto": [ { "index": 0, "name": "calc", "partial": false, "notes": [] } ],
  "diagnostics": []
}
```

### Errors

Any failure is a structured JSON error with an appropriate status — never a raw 500 or a
stack trace:

```json
{ "error": { "stage": "parse", "message": "at byte 3: unexpected end of input ...", "offset": 3 } }
```

Stages: `request` (bad JSON/base64/route, 400/404/405), `parse` (malformed bytecode, 400,
with a byte `offset`), `compile-error-input` (the input was a compiler error blob),
`timeout` (408), `internal` (500, panic backstop).

### Quick CLI inspection

```sh
cargo run -p xtask -- disasm    corpus/bytecode/03_if_else.luauc
cargo run -p xtask -- cfg       corpus/bytecode/04_while.luauc
cargo run -p xtask -- decompile corpus/bytecode/02_arith.luauc
```

## Status and known limits of the decompiler

The reader, disassembler, and CFG/IR are complete and verified:

- **Reader** — full version 3–11 deserialization, structural + operand validation, and a
  fuzz harness (truncated / random / mutated input never panics, hangs, or over-allocates).
- **Disassembler** — matches `luau-compile --text` across the whole corpus, including AUX
  handling (the PC stays synced across imports, NAMECALL, SETLIST, generic-for, …).
- **CFG/IR** — basic blocks, dominators, post-dominators, and back-edge/loop detection.

The decompiler reconstructs both expressions and control-flow structure:

- **Expressions:** arithmetic, concatenation, comparisons, table constructors and
  reads/writes, field access, method calls (`NAMECALL → obj:m(args)`), calls, multiple
  returns, varargs, globals/imports/upvalues, and nested closures. Values are materialized
  into named temporaries, then reduced to a fixpoint by sound passes that never reorder a
  side effect or drop a captured/escaping value:
  - **table-literal reconstruction** — a `NEWTABLE`/`DUPTABLE` plus its consecutive
    `SETLIST`/`SETTABLEKS` fills fold back into a literal (`t = {10, 20, key = v}`), nesting
    recursively;
  - **per-definition copy propagation** — a register reused for several unrelated values has
    each definition inlined independently, collapsing the materialize-everything temporaries
    (`TweenService:Create(part, info, {CFrame = cf}):Play()` instead of four scratch locals);
  - **dead-store elimination** for values nothing observes.
- **Closures:** nested functions are fully reconstructed, and each upvalue is resolved to the
  **name of the local it captured in the enclosing function** — across multiple levels of
  nesting (a grandchild that closes over a parent's upvalue still gets the right name) — so
  closures read `localPlayer:WaitForChild(…)`, not `u0:WaitForChild(…)`. Captured locals,
  upvalue writes, and globals are never inlined or eliminated (their mutations are observable
  to other closures).
- **Structure:** `if`/`elseif`/`else`, `while`, `repeat … until`, numeric `for`, generic
  `for` (with `pairs`/`ipairs`), and `break` are recovered as native Luau. Loop variables get
  their debug names (or stable synthesized ones). A **structural round-trip test** recompiles
  every fully-structured proto and asserts the control-flow shape (count of for/while/if
  constructs) matches the original — proof the recovery is faithful, not just compilable.
- **Short-circuits:** `a and b`, `a or c`, and the `z = a and b or c` ternary (recovered
  from its conditional-write diamond) all come back as expressions.
- **Honest fallback:** control flow that still doesn't match a pattern (irreducible flow,
  unusual `and/or` shapes) is emitted with `::label::`/`goto` and the proto is flagged
  `partial: true` — reflecting the real control flow rather than guessing. All 18 corpus
  files currently reconstruct fully (no fallback).
- Names come from debug info when present; otherwise stable synthesized names (`pN` for
  params, `vN` for locals, `i`/`j`/`k` for loops) plus the recovery heuristics below.

### Readability heuristics (name recovery)

When bytecode is stripped or obfuscated, synthesized `vN` locals are renamed from the
expression they hold. Renaming a local is always semantics-preserving, so this is applied
aggressively but guarded: a register is only renamed when it holds **one logical value** (a
single definition, or a refinement chain like `x = a.b; x = x.c`), and derived names are
de-duplicated against every in-scope name and Luau keyword. Field/method chains compiled
into register reuse are first folded back together. Examples (from stripped bytecode):

```lua
-- before                              -- after
v0 = game:GetService("Players")        Players = game:GetService("Players")
v2 = require(game.RS.MyModule)         MyModule = require(game.RS.MyModule)
v3 = require(game.RS.MyModule)         MyModule_doThing = require(game.RS.MyModule).doThing
v3 = v3.doThing
v4 = Instance.new("Part")              part = Instance.new("Part")
v5 = Players.LocalPlayer               character = Players.LocalPlayer.Character
v5 = v5.Character
v7 = workspace:GetChildren()           children = workspace:GetChildren()
v6 = #v7                               count = #children
```

Beyond defining-expression rules, two **context** rules use how a value is *used*:
tuple-returning calls name their destinations (`local ok, result = pcall(f)`,
`local key, value = next(t)`), and a temporary later stored into a field is named after it
(`x = …; obj.Health = x` → `health`). Boolean-shaped values are named by their test
(`x ~= nil` → `hasX`, `#t == 0` → `isEmpty`).

The rule catalogs (require/modules, services & instances, Roblox runtime/networking/
DataStore, Luau stdlib, OOP, method results, datatype constructors, signals, value shapes,
…) were generated by two multi-agent brainstorms (≈385 heuristics) and are kept in
[reference/decompiler-heuristics.json](reference/decompiler-heuristics.json) and
[reference/decompiler-heuristics-v2.json](reference/decompiler-heuristics-v2.json) along with
the correctness pitfalls the implementation respects (e.g. globals and closure-captured
locals are never inlined or eliminated; comparison-negation only mirrors the compiler's own
branch choice).

See `per_proto[].notes` in the `/decompile` response for the specific uncertainties in each
function.

## License

MIT — see [LICENSE](LICENSE). Vendored Luau source under `reference/` is MIT-licensed by the
Luau authors.
