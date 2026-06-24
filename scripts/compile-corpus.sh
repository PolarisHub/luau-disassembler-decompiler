#!/usr/bin/env bash
# Compile the .luau corpus into checked-in bytecode + reference disassembly using the
# vendored luau-compile oracle (Luau 0.726). See memory/luau-oracle-commands.md.
#
# We pin bytecode VERSION 7 (LBC_VERSION_TARGET) for the main corpus: it is the stable,
# non-experimental target and produces no feedback-vector noise. One sample is also
# compiled at the default version 11 to exercise the reader's full version range.
#
# -O1 (default optimization) and -g2 (full debug info: local + upvalue names) match how
# real scripts are typically shipped while keeping names available for readable output.
set -euo pipefail

cd "$(dirname "$0")/.."

LUAU="./tools/luau-compile.exe"
V7_FLAGS="--fflags=LuauEmitCallFeedback=false,LuauCompileUdataDirect=false,LuauIntegerType2=false"

mkdir -p corpus/bytecode corpus/expected-text corpus/bytecode-v11 corpus/bytecode-stripped

for src in corpus/src/*.luau; do
	name="$(basename "$src" .luau)"
	"$LUAU" --binary -O1 -g2 $V7_FLAGS "$src" > "corpus/bytecode/$name.luauc"
	"$LUAU" --text   -O1 -g2 $V7_FLAGS "$src" > "corpus/expected-text/$name.txt"
	# Stripped (-g0): no local/upvalue names, so the decompiler must synthesize and the
	# name-derivation heuristics get exercised.
	"$LUAU" --binary -O1 -g0 $V7_FLAGS "$src" > "corpus/bytecode-stripped/$name.luauc"
done

# A single version-11 (default flags) sample so the reader is exercised on feedback vectors.
"$LUAU" --binary -O1 -g2 corpus/src/01_literals.luau > corpus/bytecode-v11/01_literals.luauc

echo "Compiled $(ls corpus/bytecode/*.luauc | wc -l) corpus files at v7 (+1 at v11)."
echo "Version bytes:"
for f in corpus/bytecode/01_literals.luauc corpus/bytecode-v11/01_literals.luauc; do
	printf '  %s -> 0x%s\n' "$f" "$(head -c1 "$f" | xxd -p)"
done
