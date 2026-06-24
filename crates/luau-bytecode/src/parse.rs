//! Deserialize a Luau bytecode chunk into a [`Module`].
//!
//! This follows `loadsafe` in `VM/src/lvmload.cpp` field-for-field and in the same order.
//! Where the VM trusts the compiler and does an unchecked index (e.g. `protos[fid]`), we
//! validate instead, because our input is untrusted. Comments call out each such spot.

use crate::error::{Error, ErrorKind, Result};
use crate::model::*;
use crate::reader::Cursor;

/// Parse a complete bytecode chunk.
pub fn parse(data: &[u8]) -> Result<Module> {
    let mut p = Parser {
        cur: Cursor::new(data),
        string_count: 0,
        proto_count: 0,
    };
    p.parse_module()
}

struct Parser<'a> {
    cur: Cursor<'a>,
    string_count: u32,
    proto_count: u32,
}

impl<'a> Parser<'a> {
    fn err(&self, kind: ErrorKind) -> Error {
        Error::new(self.cur.offset(), kind)
    }

    fn parse_module(&mut self) -> Result<Module> {
        let version = self.cur.u8()?;

        // Version 0 is the sentinel: the rest of the buffer is a compile-error message.
        if version == 0 {
            let rest = self.cur.take_rest();
            return Err(Error::new(
                0,
                ErrorKind::CompileError {
                    message: String::from_utf8_lossy(rest).into_owned(),
                },
            ));
        }

        if version < LBC_VERSION_MIN || version > LBC_VERSION_MAX {
            return Err(Error::new(
                0,
                ErrorKind::UnsupportedVersion {
                    got: version,
                    min: LBC_VERSION_MIN,
                    max: LBC_VERSION_MAX,
                },
            ));
        }

        // Type-info version exists only from bytecode version 4.
        let mut types_version = 0u8;
        if version >= 4 {
            types_version = self.cur.u8()?;
            if types_version < LBC_TYPE_VERSION_MIN || types_version > LBC_TYPE_VERSION_MAX {
                return Err(self.err(ErrorKind::UnsupportedTypesVersion {
                    got: types_version,
                    min: LBC_TYPE_VERSION_MIN,
                    max: LBC_TYPE_VERSION_MAX,
                }));
            }
        }

        // String table.
        let string_count = self.cur.varint()?;
        self.cur.guard_count(string_count, 1, "strings")?;
        self.string_count = string_count;
        let mut strings = Vec::with_capacity(string_count as usize);
        for _ in 0..string_count {
            let len = self.cur.varint()?;
            let bytes = self.cur.take(len as usize)?;
            strings.push(bytes.to_vec());
        }

        // Userdata type-remapping table (type-info version 3 only). We don't need the
        // mapping for disassembly/decompilation, but we must consume it to stay in sync:
        // a u8 index terminated by 0, each non-zero index followed by a string ref.
        if types_version == 3 {
            loop {
                let index = self.cur.u8()?;
                if index == 0 {
                    break;
                }
                let _name = self.read_string_ref()?;
            }
        }

        // Proto table.
        let proto_count = self.cur.varint()?;
        self.cur.guard_count(proto_count, 1, "protos")?;
        self.proto_count = proto_count;
        let mut protos = Vec::with_capacity(proto_count as usize);
        for _ in 0..proto_count {
            protos.push(self.parse_proto(version, types_version)?);
        }

        // Main proto index. The VM does `protos[mainid]` unchecked; we validate.
        let main_proto = self.cur.varint()?;
        if main_proto >= proto_count {
            return Err(self.err(ErrorKind::ProtoIndexOutOfRange {
                index: main_proto,
                count: proto_count,
            }));
        }

        Ok(Module {
            version,
            types_version,
            strings,
            protos,
            main_proto,
        })
    }

    /// Read a 1-based string id (0 => none), validating it against the table size.
    fn read_string_ref(&mut self) -> Result<StringRef> {
        let id = self.cur.varint()?;
        if id == 0 {
            return Ok(StringRef(None));
        }
        if id - 1 >= self.string_count {
            return Err(self.err(ErrorKind::StringIndexOutOfRange {
                id,
                count: self.string_count,
            }));
        }
        Ok(StringRef(Some((id - 1) as usize)))
    }

    fn parse_proto(&mut self, version: u8, types_version: u8) -> Result<Proto> {
        let max_stack_size = self.cur.u8()?;
        let num_params = self.cur.u8()?;
        let num_upvalues = self.cur.u8()?;
        let is_vararg = self.cur.u8()? != 0;

        let mut flags = 0u8;
        let mut type_info = Vec::new();
        if version >= 4 {
            flags = self.cur.u8()?;
            // typesversion is guaranteed to be 1, 2, or 3 here (validated above). All three
            // encode the block as a varint size followed by that many raw bytes.
            let type_size = self.cur.varint()?;
            if type_size > 0 {
                type_info = self.cur.take(type_size as usize)?.to_vec();
            }
        }

        // Instructions: sizecode words of 4 bytes each.
        let size_code = self.cur.varint()?;
        self.cur.guard_count(size_code, 4, "code")?;
        let mut code = Vec::with_capacity(size_code as usize);
        for _ in 0..size_code {
            code.push(self.cur.u32()?);
        }

        // Constants.
        let size_k = self.cur.varint()?;
        self.cur.guard_count(size_k, 1, "constants")?;
        let mut constants = Vec::with_capacity(size_k as usize);
        for _ in 0..size_k {
            constants.push(self.parse_constant(size_k)?);
        }

        // Child protos: indices into the module proto table.
        let size_p = self.cur.varint()?;
        self.cur.guard_count(size_p, 1, "child protos")?;
        let mut child_protos = Vec::with_capacity(size_p as usize);
        for _ in 0..size_p {
            let fid = self.cur.varint()?;
            if fid >= self.proto_count {
                return Err(self.err(ErrorKind::ProtoIndexOutOfRange {
                    index: fid,
                    count: self.proto_count,
                }));
            }
            child_protos.push(fid);
        }

        let line_defined = self.cur.varint()?;
        let debug_name = self.read_string_ref()?;

        // Line info (optional).
        let line_info = if self.cur.u8()? != 0 {
            Some(self.parse_line_info(size_code)?)
        } else {
            None
        };

        // Debug info (optional): locals and upvalue names.
        let debug_info = if self.cur.u8()? != 0 {
            let size_locvars = self.cur.varint()?;
            self.cur.guard_count(size_locvars, 4, "locals")?;
            let mut locals = Vec::with_capacity(size_locvars as usize);
            for _ in 0..size_locvars {
                let name = self.read_string_ref()?;
                let start_pc = self.cur.varint()?;
                let end_pc = self.cur.varint()?;
                let reg = self.cur.u8()?;
                locals.push(LocalVar {
                    name,
                    start_pc,
                    end_pc,
                    reg,
                });
            }

            let size_upvalues = self.cur.varint()?;
            // lvmload asserts sizeupvalues == nups; treat a mismatch as malformed.
            if size_upvalues != num_upvalues as u32 {
                return Err(self.err(ErrorKind::UpvalueCountMismatch {
                    nups: num_upvalues,
                    debug: size_upvalues,
                }));
            }
            self.cur.guard_count(size_upvalues, 1, "upvalues")?;
            let mut upvalues = Vec::with_capacity(size_upvalues as usize);
            for _ in 0..size_upvalues {
                upvalues.push(self.read_string_ref()?);
            }

            Some(DebugInfo { locals, upvalues })
        } else {
            None
        };

        // Feedback vector (version >= 11).
        let mut feedback = Vec::new();
        if version >= 11 {
            let count = self.cur.varint()?;
            self.cur.guard_count(count, 2, "feedback slots")?;
            for _ in 0..count {
                let _slot_type = self.cur.u8()?; // always LFT_CALLTARGET (0)
                let pc = self.cur.varint()?;
                feedback.push(pc);
            }
        }

        Ok(Proto {
            max_stack_size,
            num_params,
            num_upvalues,
            is_vararg,
            flags,
            type_info,
            code,
            constants,
            child_protos,
            line_defined,
            debug_name,
            line_info,
            debug_info,
            feedback,
        })
    }

    fn parse_constant(&mut self, size_k: u32) -> Result<Constant> {
        let tag = self.cur.u8()?;
        let constant = match tag {
            constant_tag::NIL => Constant::Nil,
            constant_tag::BOOLEAN => Constant::Boolean(self.cur.u8()? != 0),
            constant_tag::NUMBER => Constant::Number(self.cur.f64()?),
            constant_tag::VECTOR => Constant::Vector {
                x: self.cur.f32()?,
                y: self.cur.f32()?,
                z: self.cur.f32()?,
                w: self.cur.f32()?,
            },
            constant_tag::STRING => Constant::String(self.read_string_ref()?),
            constant_tag::IMPORT => {
                // Packed: top 2 bits are the path length, then three 10-bit constant-table
                // indices (id0/id1/id2), per luaV_getimport.
                let id = self.cur.u32()?;
                let count = (id >> 30) as u8;
                let parts = [(id >> 20) & 1023, (id >> 10) & 1023, id & 1023];
                let mut path = Vec::with_capacity(count as usize);
                for &k in parts.iter().take(count as usize) {
                    self.check_const_index(k, size_k)?;
                    path.push(k);
                }
                Constant::Import { id, count, path }
            }
            constant_tag::TABLE => {
                let keys_len = self.cur.varint()?;
                self.cur.guard_count(keys_len, 1, "table template keys")?;
                let mut keys = Vec::with_capacity(keys_len as usize);
                for _ in 0..keys_len {
                    let key = self.cur.varint()?;
                    self.check_const_index(key, size_k)?;
                    keys.push(key);
                }
                Constant::Table { keys }
            }
            constant_tag::TABLE_WITH_CONSTANTS => {
                let keys_len = self.cur.varint()?;
                self.cur.guard_count(keys_len, 5, "table template entries")?;
                let mut entries = Vec::with_capacity(keys_len as usize);
                for _ in 0..keys_len {
                    let key = self.cur.varint()?;
                    self.check_const_index(key, size_k)?;
                    let value = self.cur.i32()?;
                    if value >= 0 {
                        self.check_const_index(value as u32, size_k)?;
                    }
                    entries.push((key, value));
                }
                Constant::TableWithConstants { entries }
            }
            constant_tag::CLOSURE => {
                let fid = self.cur.varint()?;
                if fid >= self.proto_count {
                    return Err(self.err(ErrorKind::ProtoIndexOutOfRange {
                        index: fid,
                        count: self.proto_count,
                    }));
                }
                Constant::Closure { proto: fid }
            }
            constant_tag::CLASS_SHAPE => {
                let name = self.cur.varint()?;
                self.check_const_index(name, size_k)?;
                let num_properties = self.cur.varint()?;
                let num_methods = self.cur.varint()?;
                let num_members = num_methods
                    .checked_add(num_properties)
                    .ok_or_else(|| self.err(ErrorKind::ImplausibleLength {
                        what: "class members",
                        count: num_methods as u64 + num_properties as u64,
                        remaining: self.cur.remaining(),
                    }))?;
                self.cur.guard_count(num_members, 1, "class members")?;
                let mut members = Vec::with_capacity(num_members as usize);
                for _ in 0..num_members {
                    let mid = self.cur.varint()?;
                    self.check_const_index(mid, size_k)?;
                    members.push(mid);
                }
                Constant::ClassShape {
                    name,
                    num_properties,
                    num_methods,
                    members,
                }
            }
            constant_tag::INTEGER => {
                let is_negative = self.cur.u8()? != 0;
                let magnitude = self.cur.varint64()?;
                // Two's-complement negation, matching `(int64_t)(~magnitude + 1)`.
                let value = if is_negative {
                    (!magnitude).wrapping_add(1) as i64
                } else {
                    magnitude as i64
                };
                Constant::Integer(value)
            }
            other => return Err(self.err(ErrorKind::UnknownConstantTag { tag: other })),
        };
        Ok(constant)
    }

    fn check_const_index(&self, index: u32, size_k: u32) -> Result<()> {
        if index >= size_k {
            return Err(self.err(ErrorKind::ConstantIndexOutOfRange {
                index,
                count: size_k,
            }));
        }
        Ok(())
    }

    fn parse_line_info(&mut self, size_code: u32) -> Result<LineInfo> {
        let line_gap_log2 = self.cur.u8()?;
        // Clamp the shift so hostile inputs can't trigger a shift-overflow panic. Real
        // bytecode uses small gaps, so this never changes a valid decode.
        let gap = line_gap_log2.min(31) as u32;

        // intervals = ((sizecode - 1) >> gap) + 1, but guard the sizecode == 0 case.
        let intervals: u32 = if size_code == 0 {
            0
        } else {
            ((size_code - 1) >> gap) + 1
        };

        // sizecode delta bytes, accumulated with u8 wraparound (matches `uint8_t lastoffset`).
        self.cur.guard_count(size_code, 1, "line deltas")?;
        let mut line_info = Vec::with_capacity(size_code as usize);
        let mut last_offset: u8 = 0;
        for _ in 0..size_code {
            last_offset = last_offset.wrapping_add(self.cur.u8()?);
            line_info.push(last_offset);
        }

        // intervals baseline lines, accumulated as i32.
        self.cur.guard_count(intervals, 4, "abs line info")?;
        let mut abs_line_info = Vec::with_capacity(intervals as usize);
        let mut last_line: i32 = 0;
        for _ in 0..intervals {
            last_line = last_line.wrapping_add(self.cur.i32()?);
            abs_line_info.push(last_line);
        }

        Ok(LineInfo {
            line_gap_log2: gap as u8,
            line_info,
            abs_line_info,
        })
    }
}
