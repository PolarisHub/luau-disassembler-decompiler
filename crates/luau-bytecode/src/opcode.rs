//! Opcodes and instruction-word field extraction.
//!
//! The opcode list, its order (the enum discriminant IS the on-the-wire opcode byte), the
//! field macros, and the per-opcode word length / control-flow predicates are transcribed
//! directly from `Common/include/Luau/Bytecode.h` and `Common/include/Luau/BytecodeUtils.h`
//! of Luau 0.726. Do not reorder: the values are baked into bytecode.

/// Generates the `Opcode` enum plus `from_u8` and `name`, keeping the byte value and the
/// name in one place so they can never drift apart.
macro_rules! define_opcodes {
    ($($name:ident = $val:literal),+ $(,)?) => {
        // Names mirror the LOP_* identifiers (e.g. FORGPREP_INEXT) on purpose so they line
        // up with Bytecode.h and `luau-compile --text` output.
        #[allow(non_camel_case_types)]
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        #[repr(u8)]
        pub enum Opcode {
            $($name = $val),+
        }

        impl Opcode {
            /// Decode the low byte of an instruction word. Returns `None` for values that
            /// are not a real opcode (>= LOP__COUNT), which the disassembler renders as a
            /// `data`/unknown line rather than guessing.
            pub fn from_u8(b: u8) -> Option<Opcode> {
                match b {
                    $($val => Some(Opcode::$name),)+
                    _ => None,
                }
            }

            /// The mnemonic, matching the LOP_* name without the prefix (what
            /// `luau-compile --text` prints).
            pub fn name(self) -> &'static str {
                match self {
                    $(Opcode::$name => stringify!($name),)+
                }
            }
        }
    };
}

// Order copied verbatim from enum LuauOpcode in Bytecode.h (0-based).
define_opcodes! {
    NOP = 0,
    BREAK = 1,
    LOADNIL = 2,
    LOADB = 3,
    LOADN = 4,
    LOADK = 5,
    MOVE = 6,
    GETGLOBAL = 7,
    SETGLOBAL = 8,
    GETUPVAL = 9,
    SETUPVAL = 10,
    CLOSEUPVALS = 11,
    GETIMPORT = 12,
    GETTABLE = 13,
    SETTABLE = 14,
    GETTABLEKS = 15,
    SETTABLEKS = 16,
    GETTABLEN = 17,
    SETTABLEN = 18,
    NEWCLOSURE = 19,
    NAMECALL = 20,
    CALL = 21,
    RETURN = 22,
    JUMP = 23,
    JUMPBACK = 24,
    JUMPIF = 25,
    JUMPIFNOT = 26,
    JUMPIFEQ = 27,
    JUMPIFLE = 28,
    JUMPIFLT = 29,
    JUMPIFNOTEQ = 30,
    JUMPIFNOTLE = 31,
    JUMPIFNOTLT = 32,
    ADD = 33,
    SUB = 34,
    MUL = 35,
    DIV = 36,
    MOD = 37,
    POW = 38,
    ADDK = 39,
    SUBK = 40,
    MULK = 41,
    DIVK = 42,
    MODK = 43,
    POWK = 44,
    AND = 45,
    OR = 46,
    ANDK = 47,
    ORK = 48,
    CONCAT = 49,
    NOT = 50,
    MINUS = 51,
    LENGTH = 52,
    NEWTABLE = 53,
    DUPTABLE = 54,
    SETLIST = 55,
    FORNPREP = 56,
    FORNLOOP = 57,
    FORGLOOP = 58,
    FORGPREP_INEXT = 59,
    FASTCALL3 = 60,
    FORGPREP_NEXT = 61,
    NATIVECALL = 62,
    GETVARARGS = 63,
    DUPCLOSURE = 64,
    PREPVARARGS = 65,
    LOADKX = 66,
    JUMPX = 67,
    FASTCALL = 68,
    COVERAGE = 69,
    CAPTURE = 70,
    SUBRK = 71,
    DIVRK = 72,
    FASTCALL1 = 73,
    FASTCALL2 = 74,
    FASTCALL2K = 75,
    FORGPREP = 76,
    JUMPXEQKNIL = 77,
    JUMPXEQKB = 78,
    JUMPXEQKN = 79,
    JUMPXEQKS = 80,
    IDIV = 81,
    IDIVK = 82,
    GETUDATAKS = 83,
    SETUDATAKS = 84,
    NAMECALLUDATA = 85,
    NEWCLASSMEMBER = 86,
    CALLFB = 87,
    CMPPROTO = 88,
}

impl Opcode {
    /// Number of 32-bit words the instruction occupies (1, or 2 if it carries an AUX word).
    /// Transcribed from `getOpLength` in BytecodeUtils.h. Getting this wrong desyncs the
    /// program counter, so it is the single most important table in the reader.
    pub fn length(self) -> usize {
        use Opcode::*;
        match self {
            GETGLOBAL | SETGLOBAL | GETIMPORT | GETTABLEKS | SETTABLEKS | NAMECALL | JUMPIFEQ
            | JUMPIFLE | JUMPIFLT | JUMPIFNOTEQ | JUMPIFNOTLE | JUMPIFNOTLT | NEWTABLE
            | SETLIST | FORGLOOP | LOADKX | FASTCALL2 | FASTCALL2K | FASTCALL3 | JUMPXEQKNIL
            | JUMPXEQKB | JUMPXEQKN | JUMPXEQKS | GETUDATAKS | SETUDATAKS | NAMECALLUDATA
            | NEWCLASSMEMBER | CALLFB | CMPPROTO => 2,
            _ => 1,
        }
    }

    /// Whether the instruction is followed by an AUX data word.
    pub fn has_aux(self) -> bool {
        self.length() == 2
    }

    /// `isJumpD`: the signed D field is a jump offset (target = pc + D + 1).
    pub fn is_jump_d(self) -> bool {
        use Opcode::*;
        matches!(
            self,
            JUMP | JUMPIF
                | JUMPIFNOT
                | JUMPIFEQ
                | JUMPIFLE
                | JUMPIFLT
                | JUMPIFNOTEQ
                | JUMPIFNOTLE
                | JUMPIFNOTLT
                | FORNPREP
                | FORNLOOP
                | FORGPREP
                | FORGLOOP
                | FORGPREP_INEXT
                | FORGPREP_NEXT
                | JUMPBACK
                | JUMPXEQKNIL
                | JUMPXEQKB
                | JUMPXEQKN
                | JUMPXEQKS
                | CMPPROTO
        )
    }

    /// `isFastCall`: C is a jump offset to the following CALL (target = pc + C + 2).
    pub fn is_fastcall(self) -> bool {
        use Opcode::*;
        matches!(self, FASTCALL | FASTCALL1 | FASTCALL2 | FASTCALL2K | FASTCALL3)
    }

    /// `isSkipC`: LOADB optionally jumps by C (target = pc + C + 1 when C != 0).
    pub fn is_skip_c(self) -> bool {
        matches!(self, Opcode::LOADB)
    }

    /// `isFallthrough`: false for instructions that unconditionally divert control.
    pub fn is_fallthrough(self) -> bool {
        use Opcode::*;
        !matches!(self, RETURN | JUMP | JUMPBACK | JUMPX)
    }

    /// `isLoopJump`: back-edge instructions used as loop safepoints.
    pub fn is_loop_jump(self) -> bool {
        use Opcode::*;
        matches!(self, JUMPBACK | FORGLOOP | FORNLOOP)
    }
}

// --- Instruction-word field extraction (LUAU_INSN_* macros) -----------------------------

#[inline]
pub fn insn_op(insn: u32) -> u8 {
    (insn & 0xff) as u8
}

#[inline]
pub fn insn_a(insn: u32) -> u8 {
    ((insn >> 8) & 0xff) as u8
}

#[inline]
pub fn insn_b(insn: u32) -> u8 {
    ((insn >> 16) & 0xff) as u8
}

#[inline]
pub fn insn_c(insn: u32) -> u8 {
    ((insn >> 24) & 0xff) as u8
}

/// Signed 16-bit D field: arithmetic shift of the whole word right by 16.
#[inline]
pub fn insn_d(insn: u32) -> i32 {
    (insn as i32) >> 16
}

/// Signed 24-bit E field: arithmetic shift of the whole word right by 8.
#[inline]
pub fn insn_e(insn: u32) -> i32 {
    (insn as i32) >> 8
}

// --- AUX-word field extraction (LUAU_INSN_AUX_* macros) ---------------------------------

#[inline]
pub fn aux_a(aux: u32) -> u8 {
    (aux & 0xff) as u8
}

#[inline]
pub fn aux_b(aux: u32) -> u8 {
    ((aux >> 8) & 0xff) as u8
}

/// 24-bit constant index (JUMPXEQKN/S).
#[inline]
pub fn aux_kv(aux: u32) -> u32 {
    aux & 0x00ff_ffff
}

/// 1-bit constant value (JUMPXEQKB).
#[inline]
pub fn aux_kb(aux: u32) -> bool {
    aux & 0x1 != 0
}

/// 1-bit negation flag (JUMPXEQK* family).
#[inline]
pub fn aux_not(aux: u32) -> bool {
    aux >> 31 != 0
}

/// 16-bit constant index (udata ops).
#[inline]
pub fn aux_kv16(aux: u32) -> u32 {
    aux & 0xffff
}

/// Cached slot in the high 16 bits (udata ops).
#[inline]
pub fn aux_slot(aux: u32) -> u32 {
    aux >> 16
}

/// `getJumpTarget` from BytecodeUtils.h. Returns the absolute target PC for instructions
/// that branch, or `None` for ones that do not. `pc` is the index of the instruction's
/// header word.
pub fn jump_target(insn: u32, pc: usize) -> Option<usize> {
    let op = Opcode::from_u8(insn_op(insn))?;
    let pc = pc as i64;
    let target = if op.is_jump_d() {
        pc + insn_d(insn) as i64 + 1
    } else if op.is_fastcall() {
        pc + insn_c(insn) as i64 + 2
    } else if op.is_skip_c() && insn_c(insn) != 0 {
        pc + insn_c(insn) as i64 + 1
    } else if op == Opcode::JUMPX {
        pc + insn_e(insn) as i64 + 1
    } else {
        return None;
    };
    if target < 0 {
        None
    } else {
        Some(target as usize)
    }
}
