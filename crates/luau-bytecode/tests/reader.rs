//! Reader correctness against the real compiled corpus, plus the robustness/fuzz harness.

use std::fs;
use std::path::PathBuf;

use luau_bytecode::opcode::{insn_op, Opcode};
use luau_bytecode::{parse, parse_and_validate, Constant, ErrorKind};

fn corpus_dir() -> PathBuf {
    // tests run with CWD = crate dir; the corpus lives at the workspace root.
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("corpus")
}

fn read_bytecode(rel: &str) -> Vec<u8> {
    let path = corpus_dir().join(rel);
    fs::read(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

fn push_varint(out: &mut Vec<u8>, mut value: u64) {
    while value >= 0x80 {
        out.push(((value as u8) & 0x7f) | 0x80);
        value >>= 7;
    }
    out.push(value as u8);
}

fn push_u32(out: &mut Vec<u8>, value: u32) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn abc(op: Opcode, a: u8, b: u8, c: u8) -> u32 {
    (op as u32) | ((a as u32) << 8) | ((b as u32) << 16) | ((c as u32) << 24)
}

fn ad(op: Opcode, a: u8, d: i16) -> u32 {
    (op as u32) | ((a as u32) << 8) | (((d as u16) as u32) << 16)
}

fn push_string_table(out: &mut Vec<u8>, strings: &[&str]) {
    push_varint(out, strings.len() as u64);
    for string in strings {
        push_varint(out, string.len() as u64);
        out.extend_from_slice(string.as_bytes());
    }
}

fn push_minimal_proto(
    out: &mut Vec<u8>,
    max_stack: u8,
    num_params: u8,
    code: &[u32],
    constants: impl FnOnce(&mut Vec<u8>),
) {
    out.push(max_stack);
    out.push(num_params);
    out.push(0); // num upvalues
    out.push(0); // is vararg
    out.push(0); // flags
    push_varint(out, 0); // type-info size

    push_varint(out, code.len() as u64);
    for &word in code {
        push_u32(out, word);
    }

    constants(out);

    push_varint(out, 0); // child protos
    push_varint(out, 0); // line defined
    push_varint(out, 0); // debug name
    out.push(0); // no line info
    out.push(0); // no debug info
}

fn version8_integer_blob() -> Vec<u8> {
    let mut out = vec![8, 1]; // bytecode version, type-info version
    push_string_table(&mut out, &[]);
    push_varint(&mut out, 1); // proto count
    push_minimal_proto(
        &mut out,
        1,
        0,
        &[ad(Opcode::LOADK, 0, 0), abc(Opcode::RETURN, 0, 2, 0)],
        |out| {
            push_varint(out, 1);
            out.push(luau_bytecode::constant_tag::INTEGER);
            out.push(0); // positive
            push_varint(out, 42);
        },
    );
    push_varint(&mut out, 0); // main proto
    out
}

fn version9_udata_blob() -> Vec<u8> {
    let mut out = vec![9, 1]; // bytecode version, type-info version
    push_string_table(&mut out, &["object", "Foo"]);
    push_varint(&mut out, 1); // proto count
    push_minimal_proto(
        &mut out,
        1,
        0,
        &[
            abc(Opcode::GETGLOBAL, 0, 0, 0),
            0, // K0: "object"
            abc(Opcode::GETUDATAKS, 0, 0, 0),
            0x1234_0001, // low 16 bits are K1; high 16 bits are cached slot
            abc(Opcode::RETURN, 0, 2, 0),
        ],
        |out| {
            push_varint(out, 2);
            out.push(luau_bytecode::constant_tag::STRING);
            push_varint(out, 1);
            out.push(luau_bytecode::constant_tag::STRING);
            push_varint(out, 2);
        },
    );
    push_varint(&mut out, 0); // main proto
    out
}

fn version10_class_shape_blob() -> Vec<u8> {
    let mut out = vec![10, 1]; // bytecode version, type-info version
    push_string_table(&mut out, &["MyClass", "Health", "Damage"]);
    push_varint(&mut out, 1); // proto count
    push_minimal_proto(&mut out, 1, 0, &[abc(Opcode::RETURN, 0, 1, 0)], |out| {
        push_varint(out, 4);
        out.push(luau_bytecode::constant_tag::STRING);
        push_varint(out, 1);
        out.push(luau_bytecode::constant_tag::STRING);
        push_varint(out, 2);
        out.push(luau_bytecode::constant_tag::STRING);
        push_varint(out, 3);
        out.push(luau_bytecode::constant_tag::CLASS_SHAPE);
        push_varint(out, 0); // class name constant
        push_varint(out, 1); // properties
        push_varint(out, 1); // methods
        push_varint(out, 1); // property member: Health
        push_varint(out, 2); // method member: Damage
    });
    push_varint(&mut out, 0); // main proto
    out
}

fn corpus_files() -> Vec<PathBuf> {
    let dir = corpus_dir().join("bytecode");
    let mut files: Vec<PathBuf> = fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("read_dir {}: {e}", dir.display()))
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().map(|x| x == "luauc").unwrap_or(false))
        .collect();
    files.sort();
    assert!(
        !files.is_empty(),
        "no corpus bytecode found; run scripts/compile-corpus.sh"
    );
    files
}

#[test]
fn parses_and_validates_whole_corpus() {
    for path in corpus_files() {
        let bytes = fs::read(&path).unwrap();
        let module =
            parse_and_validate(&bytes).unwrap_or_else(|e| panic!("{}: {e}", path.display()));

        assert_eq!(module.version, 7, "{} should be v7", path.display());
        assert!(
            (module.main_proto as usize) < module.protos.len(),
            "{}: main proto index out of range",
            path.display()
        );
        // Every proto's instruction stream should have decoded cleanly during validation;
        // re-confirm there is at least one proto with at least one instruction.
        assert!(
            module.protos.iter().any(|p| !p.code.is_empty()),
            "{}",
            path.display()
        );
    }
}

#[test]
fn reads_known_constants_from_literals() {
    // 01_literals.luau ends with a string "hello" and a small-int 42 etc. The main proto
    // (or one of the protos) must carry the "hello" string constant.
    let bytes = read_bytecode("bytecode/01_literals.luauc");
    let module = parse_and_validate(&bytes).unwrap();

    let has_hello = module.protos.iter().any(|p| {
        p.constants.iter().any(|c| match c {
            Constant::String(sref) => module.resolve(*sref).as_deref() == Some("hello"),
            _ => false,
        })
    });
    assert!(has_hello, "expected a 'hello' string constant somewhere");
}

#[test]
fn reads_version_11_sample() {
    // The default-flags sample is bytecode version 11 and carries feedback vectors; the
    // reader must accept it and parse those.
    let bytes = read_bytecode("bytecode-v11/01_literals.luauc");
    let module = parse_and_validate(&bytes).unwrap();
    assert_eq!(module.version, 11);
}

#[test]
fn reads_version_8_integer_constants() {
    let module = parse_and_validate(&version8_integer_blob()).unwrap();
    assert_eq!(module.version, 8);
    assert_eq!(module.types_version, 1);
    assert_eq!(module.protos.len(), 1);
    assert_eq!(
        module.protos[0].constants,
        vec![Constant::Integer(42)],
        "v8 added LBC_CONSTANT_INTEGER"
    );
}

#[test]
fn reads_version_9_udata_field_opcodes() {
    let module = parse_and_validate(&version9_udata_blob()).unwrap();
    assert_eq!(module.version, 9);
    assert_eq!(module.types_version, 1);
    assert_eq!(insn_op(module.protos[0].code[2]), Opcode::GETUDATAKS as u8);
}

#[test]
fn reads_version_10_class_shape_constants() {
    let module = parse_and_validate(&version10_class_shape_blob()).unwrap();
    assert_eq!(module.version, 10);
    assert_eq!(module.types_version, 1);
    assert_eq!(
        module.protos[0].constants[3],
        Constant::ClassShape {
            name: 0,
            num_properties: 1,
            num_methods: 1,
            members: vec![1, 2],
        },
        "v10 added LBC_CONSTANT_CLASS_SHAPE"
    );
}

#[test]
fn rejects_unsupported_version_cleanly() {
    let module = parse(&[0x02, 0x00]);
    assert!(matches!(
        module.unwrap_err().kind,
        ErrorKind::UnsupportedVersion { got: 2, .. }
    ));
}

#[test]
fn surfaces_compile_error_sentinel() {
    // Version byte 0 => the rest is a compile-error message.
    let mut blob = vec![0u8];
    blob.extend_from_slice(b"oops: bad syntax");
    let err = parse(&blob).unwrap_err();
    match err.kind {
        ErrorKind::CompileError { message } => assert_eq!(message, "oops: bad syntax"),
        other => panic!("expected CompileError, got {other:?}"),
    }
}

#[test]
fn detects_and_reverses_roblox_opcode_encoding() {
    use luau_bytecode::opcode::{insn_op, Opcode};
    use luau_bytecode::{detect_opcode_multiplier, normalize_opcodes};

    let bytes = read_bytecode("bytecode/06_numeric_for.luauc");
    let original = parse_and_validate(&bytes).unwrap();

    // Standard bytecode needs no remap.
    assert_eq!(detect_opcode_multiplier(&original), 1);

    // Simulate Roblox: encode each instruction's opcode byte as op*227 mod 256
    // (227 is the inverse of the 203 decode multiplier).
    let mut enc = original.clone();
    for proto in &mut enc.protos {
        let mut pc = 0;
        while pc < proto.code.len() {
            let real = insn_op(proto.code[pc]);
            let len = Opcode::from_u8(real).unwrap().length().max(1);
            let encoded = (real as u32).wrapping_mul(227) & 0xff;
            proto.code[pc] = (proto.code[pc] & 0xffff_ff00) | encoded;
            pc += len;
        }
    }

    // It is detected and reversed back to the original opcodes.
    assert_eq!(detect_opcode_multiplier(&enc), 203);
    let mut restored = enc.clone();
    assert_eq!(normalize_opcodes(&mut restored), 203);
    for (a, b) in original.protos.iter().zip(restored.protos.iter()) {
        assert_eq!(
            a.code, b.code,
            "opcodes should be restored to standard numbering"
        );
    }
}

#[test]
fn truncation_never_panics() {
    // Every prefix of every valid corpus blob must parse to Ok or a clean Err, never panic.
    for path in corpus_files() {
        let bytes = fs::read(&path).unwrap();
        for len in 0..=bytes.len() {
            // The full thing should be Ok; shorter prefixes are usually Err. Either is fine
            // as long as we don't panic, hang, or over-allocate.
            let _ = parse_and_validate(&bytes[..len]);
        }
    }
}

#[test]
fn random_and_mutated_input_never_panics() {
    // Deterministic xorshift so the test is reproducible without an RNG dependency.
    let mut state: u64 = 0x9E3779B97F4A7C15;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };

    // Pure random buffers of various sizes.
    for _ in 0..2000 {
        let len = (next() % 256) as usize;
        let buf: Vec<u8> = (0..len).map(|_| (next() & 0xff) as u8).collect();
        let _ = parse_and_validate(&buf);
    }

    // Bit/byte mutations of a valid blob: flip random bytes and re-parse.
    let valid = read_bytecode("bytecode/10_tables.luauc");
    for _ in 0..5000 {
        let mut buf = valid.clone();
        let flips = 1 + (next() % 8) as usize;
        for _ in 0..flips {
            let idx = (next() as usize) % buf.len();
            buf[idx] = (next() & 0xff) as u8;
        }
        let _ = parse_and_validate(&buf);
    }
}
