use colored::Colorize;
use itertools::Itertools;

use crate::{index::Index, middle::lir};

pub fn pretty_print_lir(function: &lir::FunctionDefinition) {
    print!(
        "{} {}{}",
        "fn".magenta(),
        function.symbol_name.value().blue(),
        "(".white()
    );

    print!(
        "{}",
        function
            .struct_return
            .iter()
            .map(|sret| format!("sret {}", sret.to_string()))
            .chain(function.arguments.iter().map(|arg| arg.to_string()))
            .join(", ")
            .white()
    );

    println!("{}", ") {".white());

    for block in function.blocks.values() {
        println!("{}", format!("{}:", block.id).bright_red());

        for instruction in &block.instructions {
            print!("    ");

            println!("{instruction}");
        }
    }

    println!("{}", "}".white())
}

impl core::fmt::Display for lir::Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            lir::Instruction::LoadMem {
                destination,
                source,
            } => write!(
                f,
                "{destination} {} {} {source}",
                "=".white(),
                "load".cyan()
            ),
            lir::Instruction::StoreMem {
                destination,
                source,
            } => {
                write!(
                    f,
                    "{} {destination} {} {source}",
                    "store".cyan(),
                    "<-".white()
                )
            }
            lir::Instruction::AllocStack { destination, ty } => {
                write!(f, "{destination} {} {} {ty}", "=".white(), "alloc".cyan())
            }
            lir::Instruction::GetStructElementPointer {
                destination,
                source,
                ty,
                index,
            } => write!(
                f,
                "{destination} {} {} {source}, {}, {}",
                "=".white(),
                "get_struct_element_ptr".cyan(),
                lir::Type::Struct(ty.clone()),
                index.to_string().purple()
            ),
            lir::Instruction::GetArrayElementPointer {
                destination,
                source,
                ty,
                index,
            } => write!(
                f,
                "{destination} {} {} {source}, {ty}, {}",
                "=".white(),
                "get_array_element_ptr".cyan(),
                index.to_string().purple()
            ),
            lir::Instruction::IntegerCast {
                kind,
                destination,
                operand,
            } => write!(
                f,
                "{destination} {} {} {operand}",
                "=".white(),
                format!("{kind}").cyan()
            ),
            lir::Instruction::UnaryOperation {
                operator,
                destination,
                operand,
            } => {
                write!(
                    f,
                    "{destination} {} {} {operand}",
                    "=".white(),
                    operator.to_string().white()
                )
            }
            lir::Instruction::BinaryOperation {
                operator,
                destination,
                lhs,
                rhs,
            } => {
                write!(
                    f,
                    "{destination} {} {lhs} {} {rhs}",
                    "=".white(),
                    operator.to_string().white()
                )
            }
            lir::Instruction::Branch {
                condition,
                positive,
                negative,
            } => {
                write!(
                    f,
                    "{} {condition} {} {}",
                    "br".cyan(),
                    positive.to_string().blue(),
                    negative.to_string().blue()
                )
            }
            lir::Instruction::Jump { destination } => {
                write!(f, "{} {}", "jmp".cyan(), destination.to_string().blue())
            }
            lir::Instruction::Return { value: Some(value) } => {
                write!(f, "{} {value}", "ret".cyan())
            }
            lir::Instruction::Return { value: _ } => {
                write!(f, "{}", "ret".cyan())
            }
            lir::Instruction::FunctionCall {
                target,
                arguments,
                destination,
            } => {
                if let Some(dest) = destination {
                    write!(f, "{dest} = ")?;
                }
                write!(
                    f,
                    "{} {target}({}",
                    "call".cyan(),
                    arguments.iter().map(|op| op.to_string()).join(", ").white()
                )?;

                write!(f, ")")
            }
            lir::Instruction::Phi {
                destination,
                sources,
            } => {
                write!(
                    f,
                    "{destination} {} {}{}",
                    "=".white(),
                    "phi".bright_green(),
                    "(".white(),
                )?;

                write!(
                    f,
                    "{}",
                    sources
                        .iter()
                        .map(|(block, reg)| format!("{} -> {reg}", block.to_string().blue(),))
                        .join(", ")
                        .white()
                )?;

                write!(f, "{}", ")".white())
            }
            lir::Instruction::Copy {
                destination,
                source,
            } => {
                write!(f, "{} = {} {}", destination, "copy".bright_green(), source)
            }
            lir::Instruction::Comment(text) => {
                write!(f, "{} {}", ";".bright_black(), text.bright_black())
            }
        }
    }
}

impl core::fmt::Display for lir::RegisterId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", format!("%{}", self.index()).yellow())
    }
}

impl core::fmt::Display for lir::BlockId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, ".label_{}", self.index())
    }
}

impl core::fmt::Display for lir::Immediate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            lir::Immediate::Int(value, _) => write!(f, "{value}"),
            lir::Immediate::Float(value, _) => write!(f, "{value}"),
            lir::Immediate::Bool(value) => write!(f, "{value}"),
            lir::Immediate::AnonymousStaticLabel(value) => {
                write!(f, "__$static_alloc_{}", value.index())
            }
            lir::Immediate::NamedStaticLabel(s) | lir::Immediate::FunctionLabel(s) => {
                write!(f, "{}", s.value())
            }
        }
    }
}

impl core::fmt::Display for lir::Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            lir::Operand::Immediate(immediate) => write!(f, "{}", immediate.to_string().purple()),
            lir::Operand::Register(register_id) => write!(f, "{register_id}"),
        }
    }
}

impl core::fmt::Display for lir::Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            lir::Type::Integer(integer_width) => write!(
                f,
                "{}",
                match integer_width {
                    lir::IntegerWidth::I8 => "i8",
                    lir::IntegerWidth::I16 => "i16",
                    lir::IntegerWidth::I32 => "i32",
                    lir::IntegerWidth::I64 => "i64",
                }
            ),
            lir::Type::Float(float_width) => write!(
                f,
                "{}",
                match float_width {
                    lir::FloatWidth::F32 => "f32",
                    lir::FloatWidth::F64 => "f64",
                }
            ),
            lir::Type::Pointer => write!(f, "ptr"),
            lir::Type::Struct(fields) => {
                write!(f, "{{ ")?;
                for (i, field) in fields.0.iter().enumerate() {
                    write!(f, "{field}")?;

                    if i != fields.0.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, " }}")
            }
            lir::Type::Array(ty, length) => write!(f, "[{ty}; {length}]"),
        }
    }
}
