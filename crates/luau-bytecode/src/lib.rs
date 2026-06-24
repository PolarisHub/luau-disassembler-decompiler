//! `luau-bytecode`: an exact, validated reader for Luau bytecode (the compiled chunk).
//!
//! Bytes in, a typed [`Module`] out. This crate does no analysis — it only deserializes
//! and validates, mirroring `VM/src/lvmload.cpp` from Luau 0.726. The input is untrusted,
//! so every read is bounds-checked and every fallible operation returns [`Result`]: the
//! reader never panics, never reads out of bounds, and never allocates on an unchecked
//! length field.
//!
//! Supported bytecode versions: [`LBC_VERSION_MIN`]..=[`LBC_VERSION_MAX`] (3..=11).

mod error;
mod model;
mod parse;
mod reader;
mod validate;

pub mod opcode;

pub use error::{Error, ErrorKind, Result};
pub use model::*;
pub use parse::parse;
pub use validate::validate;

/// Parse and then validate a chunk in one call.
pub fn parse_and_validate(data: &[u8]) -> Result<Module> {
    let module = parse(data)?;
    validate(&module)?;
    Ok(module)
}
