//! The typed result of parsing a Luau bytecode chunk. Everything is resolved to indices
//! and values; raw instruction words are kept (in `Proto::code`) for the disassembler.

use std::borrow::Cow;

// Version constants, from `enum LuauBytecodeTag` in Bytecode.h.
pub const LBC_VERSION_MIN: u8 = 3;
pub const LBC_VERSION_MAX: u8 = 11;
pub const LBC_VERSION_TARGET: u8 = 7;
pub const LBC_TYPE_VERSION_MIN: u8 = 1;
pub const LBC_TYPE_VERSION_MAX: u8 = 3;

// Constant table tags, from `enum LuauBytecodeTag`.
pub mod constant_tag {
    pub const NIL: u8 = 0;
    pub const BOOLEAN: u8 = 1;
    pub const NUMBER: u8 = 2;
    pub const STRING: u8 = 3;
    pub const IMPORT: u8 = 4;
    pub const TABLE: u8 = 5;
    pub const CLOSURE: u8 = 6;
    pub const VECTOR: u8 = 7;
    pub const TABLE_WITH_CONSTANTS: u8 = 8;
    pub const INTEGER: u8 = 9;
    pub const CLASS_SHAPE: u8 = 10;
}

// Capture types, from `enum LuauCaptureType`.
pub mod capture_type {
    pub const VAL: u8 = 0;
    pub const REF: u8 = 1;
    pub const UPVAL: u8 = 2;
}

// Proto flags, from `enum LuauProtoFlag`.
pub mod proto_flag {
    pub const NATIVE_MODULE: u8 = 1 << 0;
    pub const NATIVE_COLD: u8 = 1 << 1;
    pub const NATIVE_FUNCTION: u8 = 1 << 2;
    pub const INLINABLE: u8 = 1 << 3;
}

/// A reference to the string table. Luau encodes string ids as 1-based, with 0 meaning
/// "no string". We store the resolved 0-based index, or `None` for the 0 sentinel.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct StringRef(pub Option<usize>);

impl StringRef {
    pub fn index(self) -> Option<usize> {
        self.0
    }
}

/// The whole deserialized chunk.
#[derive(Debug, Clone)]
pub struct Module {
    pub version: u8,
    /// 0 when `version < 4` (no type-info block exists for those versions).
    pub types_version: u8,
    /// Raw bytes of each interned string. Luau strings are byte strings, not guaranteed
    /// UTF-8, so we keep them as bytes and convert lossily only for display.
    pub strings: Vec<Vec<u8>>,
    pub protos: Vec<Proto>,
    pub main_proto: u32,
}

impl Module {
    /// The bytes of a string by 0-based index, if in range.
    pub fn string_bytes(&self, idx: usize) -> Option<&[u8]> {
        self.strings.get(idx).map(|v| v.as_slice())
    }

    /// A string resolved through a `StringRef`, lossily as UTF-8 for display. `None` for
    /// the 0 sentinel; `Some("<bad string id>")` would never happen because parse validates.
    pub fn resolve(&self, s: StringRef) -> Option<Cow<'_, str>> {
        s.0.and_then(|i| self.strings.get(i))
            .map(|b| String::from_utf8_lossy(b))
    }
}

#[derive(Debug, Clone)]
pub struct Proto {
    pub max_stack_size: u8,
    pub num_params: u8,
    pub num_upvalues: u8,
    pub is_vararg: bool,
    /// Present from version 4; 0 for older versions.
    pub flags: u8,
    /// Raw type-info block (version >= 4). We keep the bytes verbatim; decoding the type
    /// language is out of scope for the reader.
    pub type_info: Vec<u8>,
    /// Raw instruction words. Variable-length decoding happens in the disassembler.
    pub code: Vec<u32>,
    pub constants: Vec<Constant>,
    pub child_protos: Vec<u32>,
    pub line_defined: u32,
    pub debug_name: StringRef,
    pub line_info: Option<LineInfo>,
    pub debug_info: Option<DebugInfo>,
    /// Feedback-vector slot PCs (version >= 11). Kind is always LFT_CALLTARGET.
    pub feedback: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Constant {
    Nil,
    Boolean(bool),
    Number(f64),
    Vector {
        x: f32,
        y: f32,
        z: f32,
        w: f32,
    },
    /// Index into the module string table.
    String(StringRef),
    /// `id` is the packed import id; `path` holds the `count` constant-table indices
    /// (each a string constant in this proto) that make up the dotted path.
    Import {
        id: u32,
        count: u8,
        path: Vec<u32>,
    },
    /// Table template: array of constant-table indices used as keys.
    Table {
        keys: Vec<u32>,
    },
    /// Table template with pre-filled values: (key constant index, value constant index or
    /// -1 for "no value").
    TableWithConstants {
        entries: Vec<(u32, i32)>,
    },
    /// Closure built from a child proto (index into the module proto table).
    Closure {
        proto: u32,
    },
    ClassShape {
        name: u32,
        num_properties: u32,
        num_methods: u32,
        members: Vec<u32>,
    },
    Integer(i64),
}

/// Decoded line-number information for a proto.
#[derive(Debug, Clone)]
pub struct LineInfo {
    pub line_gap_log2: u8,
    /// Accumulated per-instruction byte offsets (length == proto.code's instruction count).
    pub line_info: Vec<u8>,
    /// Accumulated baseline lines, one per `1 << line_gap_log2` interval.
    pub abs_line_info: Vec<i32>,
}

impl LineInfo {
    /// The source line for an instruction PC, per the VM's `luaG_getline`:
    /// `abslineinfo[pc >> linegaplog2] + lineinfo[pc]`.
    pub fn line_for_pc(&self, pc: usize) -> Option<i32> {
        let base = *self.abs_line_info.get(pc >> self.line_gap_log2)?;
        let delta = *self.line_info.get(pc)? as i32;
        Some(base.wrapping_add(delta))
    }
}

#[derive(Debug, Clone)]
pub struct DebugInfo {
    pub locals: Vec<LocalVar>,
    pub upvalues: Vec<StringRef>,
}

#[derive(Debug, Clone)]
pub struct LocalVar {
    pub name: StringRef,
    pub start_pc: u32,
    pub end_pc: u32,
    pub reg: u8,
}
