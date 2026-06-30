//! Typed error for the reader. Every fallible read returns one of these; the reader
//! never panics on hostile input.

use core::fmt;

/// A reader error, always carrying the byte offset where the problem was detected so
/// the server can report it. `offset` is the position in the original byte slice.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error {
    pub offset: usize,
    pub kind: ErrorKind,
}

impl Error {
    pub fn new(offset: usize, kind: ErrorKind) -> Self {
        Error { offset, kind }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ErrorKind {
    /// Tried to read past the end of the buffer. `needed` bytes from `offset`, but only
    /// `available` remained.
    UnexpectedEof { needed: usize, available: usize },

    /// A varint used more continuation bytes than its target type can hold. Real Luau
    /// bytecode never does this; we reject it rather than silently truncating or looping.
    VarIntTooLong { max_bytes: usize },

    /// The version byte is outside the supported range. The embedded values mirror
    /// `LBC_VERSION_MIN`/`MAX` from Bytecode.h.
    UnsupportedVersion { got: u8, min: u8, max: u8 },

    /// The type-info version byte is outside `LBC_TYPE_VERSION_MIN..=MAX`.
    UnsupportedTypesVersion { got: u8, min: u8, max: u8 },

    /// The bytecode is an error sentinel: version byte 0 means the rest of the buffer is
    /// a UTF-8 compile-error message produced by the Luau compiler.
    CompileError { message: String },

    /// An unknown constant tag was encountered (not one of LBC_CONSTANT_*).
    UnknownConstantTag { tag: u8 },

    /// An instruction's opcode byte did not decode to any opcode we support. The stream
    /// is no longer decodable past this point (we can't know the instruction length).
    UnknownOpcode { op: u8 },

    /// A string-table reference (1-based id) pointed outside the table.
    StringIndexOutOfRange { id: u32, count: u32 },

    /// A constant-table reference pointed outside the proto's constant table.
    ConstantIndexOutOfRange { index: u32, count: u32 },

    /// A register operand addressed a slot outside the proto's declared frame
    /// (`max_stack_size`).
    RegisterIndexOutOfRange { index: u32, count: u32 },

    /// A child-proto / closure reference pointed outside the proto table.
    ProtoIndexOutOfRange { index: u32, count: u32 },

    /// `nups` disagreed with the number of upvalue names in the debug block
    /// (lvmload asserts `sizeupvalues == nups`).
    UpvalueCountMismatch { nups: u8, debug: u32 },

    /// A declared count would require allocating more than the input could possibly
    /// justify (e.g. a length field larger than the remaining bytes). This is the
    /// "never allocate based on an unchecked length field" guard.
    ImplausibleLength {
        what: &'static str,
        count: u64,
        remaining: usize,
    },
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "at byte {}: ", self.offset)?;
        match &self.kind {
            ErrorKind::UnexpectedEof { needed, available } => write!(
                f,
                "unexpected end of input (needed {needed} bytes, {available} available)"
            ),
            ErrorKind::VarIntTooLong { max_bytes } => {
                write!(f, "varint longer than {max_bytes} bytes")
            }
            ErrorKind::UnsupportedVersion { got, min, max } => write!(
                f,
                "unsupported bytecode version {got} (supported [{min}..{max}])"
            ),
            ErrorKind::UnsupportedTypesVersion { got, min, max } => write!(
                f,
                "unsupported type-info version {got} (supported [{min}..{max}])"
            ),
            ErrorKind::CompileError { message } => {
                write!(f, "input is a compile-error blob: {message}")
            }
            ErrorKind::UnknownConstantTag { tag } => write!(f, "unknown constant tag {tag}"),
            ErrorKind::UnknownOpcode { op } => write!(f, "unknown opcode {op}"),
            ErrorKind::StringIndexOutOfRange { id, count } => {
                write!(f, "string id {id} out of range (table has {count})")
            }
            ErrorKind::ConstantIndexOutOfRange { index, count } => {
                write!(f, "constant index {index} out of range (proto has {count})")
            }
            ErrorKind::RegisterIndexOutOfRange { index, count } => {
                write!(f, "register {index} out of range (frame has {count} slots)")
            }
            ErrorKind::ProtoIndexOutOfRange { index, count } => {
                write!(f, "proto index {index} out of range ({count} protos)")
            }
            ErrorKind::UpvalueCountMismatch { nups, debug } => write!(
                f,
                "upvalue count mismatch: proto declares {nups}, debug info has {debug}"
            ),
            ErrorKind::ImplausibleLength {
                what,
                count,
                remaining,
            } => write!(
                f,
                "{what} count {count} exceeds {remaining} remaining bytes"
            ),
        }
    }
}

impl std::error::Error for Error {}

pub type Result<T> = core::result::Result<T, Error>;
