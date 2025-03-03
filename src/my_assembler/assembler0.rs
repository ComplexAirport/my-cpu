#![allow(unused)]

/*!
Our assembly language has 6 token types

### Instruction
- **add**
- **jump** \
etc.

### Memory address
- **0x000be04f05**
- **0xFFFFFFFFFF**
etc.

### Register
- **r5** (register 5)
- **accu** (accumulator register)
etc.

### Flag
- **zero** (zero flag)
- **overflow** (overflow flag)
- **sign** (sign flag)

### Immediate - int
- **1569**
- **-45**
etc.

### Immediate - float
- **40.45**
- **-3.14**
etc.
*/

pub use crate::my_assembler::text_loc::{Source, CharLoc};
pub use crate::my_assembler::base_assembler::{*};
use phf::phf_map;
use crate::my_assembler::error::Assembler0Error;
use crate::my_assembler::text_loc::pretty_loc;

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub enum TokenVal {
    Instr(CPUInstr),
    MemAddr(RamAddr),
    Register(usize),
    Flag(CPUFlag),
    ImmInt(ImmType),
    ImmFloat(FloatType)
}



/// Maps instruction strings to [`CPUInstr`]
static INSTRS: phf::Map<&'static str, CPUInstr> = phf_map! {
    "halt" => CPUInstr::Halt,
    "set" => CPUInstr::Set,
    "add" => CPUInstr::Add,
    "sub" => CPUInstr::Sub,
    "mul" => CPUInstr::Mul,
    "mod" => CPUInstr::Mod,
    "div" => CPUInstr::Div,
    "fadd" => CPUInstr::FAdd,
    "fsub" => CPUInstr::FSub,
    "fmul" => CPUInstr::FMul,
    "fdiv" => CPUInstr::FDiv,
    "and" => CPUInstr::And,
    "or" => CPUInstr::Or,
    "xor" => CPUInstr::Xor,
    "not" => CPUInstr::Not,
    "b_and" => CPUInstr::BitwiseAnd,
    "b_or" => CPUInstr::BitwiseOr,
    "b_xor" => CPUInstr::BitwiseXor,
    "b_not" => CPUInstr::BitwiseNot,
    "shl" => CPUInstr::Shl,
    "shr" => CPUInstr::Shr,
    "jump" => CPUInstr::Jump,
    "jump_if" => CPUInstr::JumpIf,
    "jump_if_not" => CPUInstr::JumpIfNot,
    "jump_if_greater" => CPUInstr::JumpIfGreater,
    "jump_if_less" => CPUInstr::JumpIfLess,
    "jump_if_equal" => CPUInstr::JumpIfEqual,
};


/// Maps flag strings to [`CPUFlag`]
static FLAGS: phf::Map<&'static str, CPUFlag> = phf_map! {
    "overflow" => CPUFlag::Overflow,
    "zero" => CPUFlag::Zero,
    "sign" => CPUFlag::Sign
};


/// Maps register strings to [`usize`] (register number)
static REGS: phf::Map<&'static str, usize> = phf_map! {
    "r0" => 0,
    "r1" => 1,
    "r2" => 2,
    "r3" => 3,
    "r4" => 4,
    "r5" => 5,
    "r6" => 6,
    "r7" => 7,
    "accu" => GEN_REG_COUNT,
};



#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct Token<'a> {
    value: TokenVal,
    start_pos: CharLoc<'a>,
    end_pos: CharLoc<'a>
}

impl<'a> Token<'a> {
    pub fn new(value: TokenVal, start_pos: CharLoc<'a>, end_pos: CharLoc<'a>) -> Self {
        Self { value, start_pos, end_pos }
    }
}



pub struct Lexer<'a> {
    /// Represents the source of the "program"
    source: &'a Source,

    /// Represents the current position the lexer is at
    curr_pos: CharLoc<'a>,

    /// Usually represents the start position of current token (which is not created yet, it's
    /// temporarily stored in `curr_tok`
    last_pos: CharLoc<'a>,

    /// The resulting tokens
    tokens: Vec<Token<'a>>,

    /// Represents the current temporary token which is not completely created yet
    curr_tok: String
}


impl<'a> Lexer<'a> {
    const WHITESPACE: &'static str = "\t\r\n ";
    const DIGITS: &'static str = "0123456789";
    const DIGITS_DOT: &'static str = ".0123456789";
    const HEX_CHARS: &'static str = "0123456789abcdefABCDEF";


    pub fn new(source: &'a Source) -> Self {
        Self {
            source,
            curr_pos: CharLoc::from(source),
            last_pos: CharLoc::from(source),
            tokens: Vec::new(),
            curr_tok: String::new()
        }
    }

    /// Read through the source and return the list of tokens
    /// - consumes `self`
    pub fn read_tokens(mut self) -> Result<Vec<Token<'a>>, Assembler0Error> {
        while let Some(ch) = self.curr_pos.ch() {
            if self.matches_char(Self::WHITESPACE) || ch == ';' {
                self.check_for_word()?;
                self.inc();
                self.update_loc();
                continue
            }

            if ch == '0' && self.curr_tok.is_empty() { // It may be a memory address or a number
                self.update_loc();
                self.gen_num_or_addr()?;
                self.update_loc();
            }

            else if self.matches_char(Self::DIGITS_DOT) && self.curr_tok.is_empty() {
                self.update_loc();
                self.gen_num()?;
                self.update_loc();
            }

            else {
                self.curr_tok.push(ch);
            }

            self.inc();
        }
        self.check_for_word()?;
        Ok(self.tokens)
    }

    /// Checks for a word in `self.curr_tok` \
    /// This method may be called, for example, when the lexer encounters a space or a newline
    /// It will check is `self.curr_tok` is empty and if it's not, ...todo
    fn check_for_word(&mut self) -> Result<(), Assembler0Error> {
        if self.curr_tok.is_empty() {
            return Ok(());
        }

        let tok = self.curr_tok.clone();

        if let Some(instr) = INSTRS.get(tok.as_str()) {
            self.push_tok(TokenVal::Instr(*instr));
        }
        else if let Some(reg) = REGS.get(tok.as_str()) {
            self.push_tok(TokenVal::Register(*reg));
        }
        else if let Some(flag) = FLAGS.get(tok.as_str()) {
            self.push_tok(TokenVal::Flag(*flag));
        }
        else {
            println!("{:?}", self.curr_tok);
            return Err(Assembler0Error::UnexpectedToken(self.get_pos_info()));
        }

        Ok(())
    }


    /// Sets the `last_pos` to current position
    fn set_last_pos(&mut self) {
        self.last_pos = self.curr_pos;
    }

    /// Generates an integer, float or a memory address,
    /// Since they all may start with 0 \
    /// Example: \
    /// memory address: 0xFFFFFFFFFF \
    /// integer: 0 \
    /// float: 0.15
    fn gen_num_or_addr(&mut self) -> Result<(), Assembler0Error> {
        /// Check if its memory address
        if let Some(next) = self.curr_pos.next_ch(1) {
            if next == 'X' || next == 'x' {
                self.curr_pos.inc(2); // Skip the "0x" part
                Ok(self.gen_addr()?)
            } else {
                Ok(self.gen_num()?)
            }
        } else {
            Ok(self.gen_num()?)
        }
    }


    /// Generates a number token (integer or float)
    fn gen_num(&mut self) -> Result<(), Assembler0Error> {
        let ch = self.curr_pos.ch().unwrap();

        let mut has_dot = ch == '.';
        let mut num = String::from(ch);

        self.inc();

        while let Some(ch) = self.curr_pos.ch() {
            if !self.matches_char(Self::DIGITS_DOT) {
                break
            }

            if ch == '.' {
                if has_dot {
                    return Err(Assembler0Error::UnexpectedNumberDot(self.get_pos_info()))
                } else {
                    has_dot = true;
                }
            }

            num.push(ch);
            self.inc();
        }
        self.inc();

        if has_dot {
            let v: FloatType = num.parse().unwrap();
            self.push_tok(TokenVal::ImmFloat(v));
        } else {
            let v: ImmType = num.parse().unwrap();
            self.push_tok(TokenVal::ImmInt(v));
        }

        Ok(())
    }

    /// Generates a memory address token
    fn gen_addr(&mut self) -> Result<(), Assembler0Error> {
        let mut addr = String::new();

        while let Some(ch) = self.curr_pos.ch() {
            if !self.matches_char(Self::HEX_CHARS) {
                break
            }

            addr.push(ch);
            self.inc();

            if addr.len() > 16 {
                return Err(Assembler0Error::AddressTooLong(self.get_pos_info()))
            }
        }

        if addr.is_empty() {
            return Err(Assembler0Error::ExpectedAddress(self.get_pos_info()));
        }

        let addr: usize = usize::from_str_radix(addr.as_str(), 16).unwrap();
        self.push_tok(TokenVal::MemAddr(RamAddr(addr)));

        Ok(())
    }

    /// Returns `true` if current character is inside chars
    fn matches_char(&self, chars: &str) -> bool {
        if let Some(ch) = self.curr_pos.ch() {
            if chars.contains(ch) {
                true
            } else {
                false
            }
        } else {
            false
        }
    }


    /// Does `self.curr_pos.inc(1)`
    fn inc(&mut self) {
        self.curr_pos.inc(1);
    }

    /// This method:
    /// 1. Updates `last_loc`
    /// 2. Sets `curr_tok` to ""
    fn update_loc(&mut self) {
        self.set_last_pos();
        self.curr_tok = String::new();
    }

    /// Returns the current location information string for error messages
    fn get_pos_info(&mut self) -> String {
        pretty_loc(&self.curr_pos)
    }

    /// Creates a [`Token`] from [`TokenVal`] and pushes it to the result tokens
    fn push_tok(&mut self, val: TokenVal) {
        self.tokens.push(Token::new(val, self.last_pos, self.curr_pos));
    }
}

