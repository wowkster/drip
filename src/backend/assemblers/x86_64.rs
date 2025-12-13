use std::collections::BTreeMap;

use crate::middle::lir::{self, RegisterId};

pub struct Assembler<'a> {
    output: String,
    function: &'a lir::FunctionDefinition,
    stack_frame_register_offset_map: &'a BTreeMap<RegisterId, usize>,
}

impl<'a> Assembler<'a> {
    pub fn new(
        function: &'a lir::FunctionDefinition,
        stack_frame_register_offset_map: &'a BTreeMap<RegisterId, usize>,
    ) -> Self {
        Self {
            output: String::new(),
            function,
            stack_frame_register_offset_map,
        }
    }

    pub fn into_output(self) -> String {
        self.output
    }

    fn push_line(&mut self, string: impl AsRef<str>) {
        self.output.push_str(string.as_ref());
        self.output.push('\n');
    }

    pub fn emit(&mut self, string: impl AsRef<str>) {
        self.output.push_str("    ");
        self.push_line(string);
    }

    pub fn global_label(&mut self, name: &str) {
        self.push_line(format!("global {name}"));
        self.push_line(format!("{name}:"));
    }

    pub fn label(&mut self, name: impl AsRef<str>) {
        self.push_line(format!("{}:", name.as_ref()));
    }

    pub fn comment(&mut self, comment: impl AsRef<str>) {
        self.emit(format!("; {}", comment.as_ref()));
    }

    pub fn function_prologue(&mut self, stack_frame_size: usize) {
        self.emit("push rbp");
        self.emit("mov rbp, rsp");
        self.emit(format!("sub rsp, {stack_frame_size}"));
    }

    pub fn function_epilogue(&mut self) {
        self.push_line(".exit:");
        self.emit("mov rsp, rbp");
        self.emit("pop rbp");
        self.emit("ret");
    }

    pub fn load_operand(
        &mut self,
        destination: X86FullRegister,
        source: lir::Operand,
    ) -> X86Register {
        match source {
            lir::Operand::Immediate(lir::Immediate::Bool(value)) => {
                self.emit(format!("xor {destination}, {destination}"));
                self.emit(format!("mov {}, {}", destination.as_8_bit(), value as u8));
                destination.as_8_bit()
            }
            lir::Operand::Immediate(lir::Immediate::Int(value, width)) => {
                if width != lir::IntegerWidth::I64 {
                    self.emit(format!("xor {destination}, {destination}"));
                }

                let sized = match width {
                    lir::IntegerWidth::I8 => destination.as_8_bit(),
                    lir::IntegerWidth::I16 => destination.as_16_bit(),
                    lir::IntegerWidth::I32 => destination.as_32_bit(),
                    lir::IntegerWidth::I64 => destination.as_64_bit(),
                };

                self.emit(format!("mov {sized}, {value}"));

                sized
            }
            lir::Operand::Immediate(
                imm @ (lir::Immediate::AnonymousStaticLabel(_)
                | lir::Immediate::NamedStaticLabel(_)
                | lir::Immediate::FunctionLabel(_)),
            ) => {
                self.emit(format!("mov {destination}, {imm}"));
                destination.as_64_bit()
            }
            lir::Operand::Immediate(lir::Immediate::Float(..)) => {
                todo!("xmm registers")
            }
            lir::Operand::Register(reg_id) => {
                let ty = &self.function.registers[&reg_id].ty;
                let sized = destination.with_size_bytes(ty.layout().size);

                match ty {
                    lir::Type::Integer(width) => {
                        if *width != lir::IntegerWidth::I64 {
                            self.emit(format!("xor {destination}, {destination}"));
                        }
                    }
                    lir::Type::Float(_) => todo!("xmm registers"),
                    lir::Type::Struct(_) | lir::Type::Array(_, _) => unreachable!(),
                    _ => {}
                }

                self.emit(format!(
                    "mov {sized}, [rbp - {}]",
                    self.stack_frame_register_offset_map[&reg_id]
                ));

                sized
            }
        }
    }

    pub fn store_operand(&mut self, destination: RegisterId, source: X86FullRegister) {
        let ty = &self.function.registers[&destination].ty;
        let sized = source.with_size_bytes(ty.layout().size);

        match ty {
            lir::Type::Float(_) => todo!("xmm registers"),
            lir::Type::Struct(_) | lir::Type::Array(_, _) => unreachable!(),
            _ => {
                self.emit(format!(
                    "mov [rbp - {}], {}",
                    self.stack_frame_register_offset_map[&destination], sized
                ));
            }
        }
    }

    /// Loads the memory address of the temporary register on the stack into the destination
    pub fn load_register_address(&mut self, destination: X86FullRegister, source: lir::RegisterId) {
        self.emit(format!(
            "lea {destination}, [rbp - {}]",
            self.stack_frame_register_offset_map[&source]
        ));
    }
}

/// General Purpose Register 64-bit
#[derive(Debug, Clone, Copy, PartialEq, Eq, strum::Display)]
#[strum(serialize_all = "lowercase")]
pub enum X86FullRegister {
    Rax,
    Rbx,
    Rcx,
    Rdx,
    Rsi,
    Rdi,
    Rbp,
    Rsp,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
}

impl X86FullRegister {
    #[track_caller]
    pub fn with_size_bytes(self, size: usize) -> X86Register {
        match size {
            8 => self.as_64_bit(),
            4 => self.as_32_bit(),
            2 => self.as_16_bit(),
            1 => self.as_8_bit(),
            size => panic!("invalid size in bytes {size}"),
        }
    }

    pub fn as_64_bit(self) -> X86Register {
        match self {
            Self::Rax => X86Register::Rax,
            Self::Rbx => X86Register::Rbx,
            Self::Rcx => X86Register::Rcx,
            Self::Rdx => X86Register::Rdx,
            Self::Rsi => X86Register::Rsi,
            Self::Rdi => X86Register::Rdi,
            Self::Rbp => X86Register::Rbp,
            Self::Rsp => X86Register::Rsp,
            Self::R8 => X86Register::R8,
            Self::R9 => X86Register::R9,
            Self::R10 => X86Register::R10,
            Self::R11 => X86Register::R11,
            Self::R12 => X86Register::R12,
            Self::R13 => X86Register::R13,
            Self::R14 => X86Register::R14,
            Self::R15 => X86Register::R15,
        }
    }

    pub fn as_32_bit(self) -> X86Register {
        match self {
            Self::Rax => X86Register::Eax,
            Self::Rbx => X86Register::Ebx,
            Self::Rcx => X86Register::Ecx,
            Self::Rdx => X86Register::Edx,
            Self::Rsi => X86Register::Esi,
            Self::Rdi => X86Register::Edi,
            Self::Rbp => X86Register::Ebp,
            Self::Rsp => X86Register::Esp,
            Self::R8 => X86Register::R8d,
            Self::R9 => X86Register::R9d,
            Self::R10 => X86Register::R10d,
            Self::R11 => X86Register::R11d,
            Self::R12 => X86Register::R12d,
            Self::R13 => X86Register::R13d,
            Self::R14 => X86Register::R14d,
            Self::R15 => X86Register::R15d,
        }
    }

    pub fn as_16_bit(self) -> X86Register {
        match self {
            Self::Rax => X86Register::Ax,
            Self::Rbx => X86Register::Bx,
            Self::Rcx => X86Register::Cx,
            Self::Rdx => X86Register::Dx,
            Self::Rsi => X86Register::Si,
            Self::Rdi => X86Register::Di,
            Self::Rbp => X86Register::Bp,
            Self::Rsp => X86Register::Sp,
            Self::R8 => X86Register::R8w,
            Self::R9 => X86Register::R9w,
            Self::R10 => X86Register::R10w,
            Self::R11 => X86Register::R11w,
            Self::R12 => X86Register::R12w,
            Self::R13 => X86Register::R13w,
            Self::R14 => X86Register::R14w,
            Self::R15 => X86Register::R15w,
        }
    }

    pub fn as_8_bit(self) -> X86Register {
        match self {
            Self::Rax => X86Register::Al,
            Self::Rbx => X86Register::Bl,
            Self::Rcx => X86Register::Cl,
            Self::Rdx => X86Register::Dl,
            Self::Rsi => X86Register::Sil,
            Self::Rdi => X86Register::Dil,
            Self::Rbp => X86Register::Bpl,
            Self::Rsp => X86Register::Spl,
            Self::R8 => X86Register::R8b,
            Self::R9 => X86Register::R9b,
            Self::R10 => X86Register::R10b,
            Self::R11 => X86Register::R11b,
            Self::R12 => X86Register::R12b,
            Self::R13 => X86Register::R13b,
            Self::R14 => X86Register::R14b,
            Self::R15 => X86Register::R15b,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, strum::Display)]
#[strum(serialize_all = "lowercase")]
#[rustfmt::skip]
pub enum X86Register {
    // 64-bit
    Rax, Rbx, Rcx, Rdx,
    Rsi, Rdi, Rbp, Rsp,
    R8, R9, R10, R11, R12, R13, R14, R15,

    // 32-bit
    Eax, Ebx, Ecx, Edx,
    Esi, Edi, Ebp, Esp,
    R8d, R9d, R10d, R11d, R12d, R13d, R14d, R15d,

    // 16-bit
    Ax, Bx, Cx, Dx,
    Si, Di, Bp, Sp,
    R8w, R9w, R10w, R11w, R12w, R13w, R14w, R15w,

    // 8-bit low
    Al, Bl, Cl, Dl,
    Sil, Dil, Bpl, Spl,
    R8b, R9b, R10b, R11b, R12b, R13b, R14b, R15b,

    // 8-bit high (only for legacy GPRs)
    Ah, Bh, Ch, Dh
}
