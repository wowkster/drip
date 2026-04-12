use std::{collections::BTreeMap, path::Path, process::Command};

use itertools::Itertools;

use crate::{
    backend::{
        CodegenOptions,
        assemblers::x86_64::{Assembler, X86FullRegister},
        targets::CodeGenerator,
    },
    frontend::ast::{BinaryOperatorKind, UnaryOperatorKind},
    index::Index,
    middle::lir,
};

pub struct CodeGeneratorX86_64LinuxGnu;

impl CodeGenerator for CodeGeneratorX86_64LinuxGnu {
    fn translate_to_asm(&self, module: &lir::Module, options: &CodegenOptions) -> String {
        // TODO: remove unused static labels
        let static_strings = module
            .static_strings
            .iter()
            .map(|(id, symbol)| {
                format!(
                    r#"__$static_alloc_{}: db {}"#,
                    id.index(),
                    format_nasm_string(symbol.value())
                )
            })
            .join("\n");

        let static_definitions = module
            .static_definitions
            .iter()
            .map(|(_, definition)| {
                format!(
                    "alignb {}\n{}: resb {}",
                    definition.layout.alignment.max(8),
                    definition.symbol_name.value(),
                    definition.layout.size
                )
            })
            .join("\n");

        let function_bodies = module
            .function_definitions
            .values()
            .map(|f| codegen_function(f, options))
            .join("\n\n");

        format!(
            indoc::indoc! {r#"
            global _start

            bits 64
            section .text

            ; program entrypoint
            _start:
                call main

                ; exit syscall using code passed in rax
                mov rdi, rax
                mov rax, 60
                syscall

            ; user code
            {0}

            ; built-in functions
            {1}

            ; readonly static data
            section .rodata

            ; utf-8 strings
            {2}

            ; zeroed static data
            section .bss
            align 4096

            ; definitions
            {3}
            "#
            },
            function_bodies,
            include_str!("./x86_64-linux-gnu_core.s"),
            static_strings,
            static_definitions,
        )
    }

    fn create_assembler_command(
        &self,
        input_file: &Path,
        output_file: &Path,
    ) -> std::process::Command {
        let mut cmd = Command::new("nasm");

        cmd.args([
            "-f",
            "elf64",
            "-g",
            "-o",
            output_file
                .to_str()
                .expect("Could not convert output_file to string"),
            input_file
                .to_str()
                .expect("Could not convert input_file to string"),
        ]);

        cmd
    }

    fn create_linker_command(
        &self,
        input_file: &Path,
        output_file: &Path,
    ) -> std::process::Command {
        let mut cmd = Command::new("ld.lld");

        cmd.args([
            "--nostdlib",
            "-x",
            "-g",
            "-e",
            "_start",
            "-o",
            output_file
                .to_str()
                .expect("Could not convert output_file to string"),
            input_file
                .to_str()
                .expect("Could not convert input_file to string"),
        ]);

        cmd
    }
}

fn format_nasm_string(string: &str) -> String {
    let mut parts = Vec::new();

    let mut last = 0;
    for (index, matched) in string.match_indices(['\n', '\r', '\0']) {
        if last != index {
            parts.push(format!("\"{}\"", &string[last..index]));
        }

        for b in matched.bytes() {
            parts.push(format!("0x{b:X}"));
        }

        last = index + matched.len();
    }
    if last < string.len() {
        parts.push(format!("\"{}\"", &string[last..]));
    }

    parts.join(", ")
}

fn codegen_function(function: &lir::FunctionDefinition, options: &CodegenOptions) -> String {
    const ARG_REGS: &[X86FullRegister] = &[
        X86FullRegister::Rdi,
        X86FullRegister::Rsi,
        X86FullRegister::Rdx,
        X86FullRegister::R10,
        X86FullRegister::R8,
        X86FullRegister::R9,
    ];

    let mut stack_frame_register_offset_map = BTreeMap::new();
    let mut stack_frame_size = 0;

    for reg in function.registers.values() {
        stack_frame_size = lir::align_to(
            stack_frame_size + reg.ty.layout().size,
            reg.ty.layout().alignment,
        );
        stack_frame_register_offset_map.insert(reg.id, stack_frame_size);
    }

    /* Assembly output */

    let mut assembler = Assembler::new(function, &stack_frame_register_offset_map);

    assembler.global_label(function.symbol_name.value());
    assembler.function_prologue(stack_frame_size);

    /* Move the function arguments into the stack registers */

    if let Some(sret_reg) = function.struct_return {
        assembler.emit(format!(
            "; store sret arg {} into its stack register",
            strip_ansi_escapes::strip_str(sret_reg.to_string())
        ));
        assembler.emit(format!(
            "mov [rbp - {}], {}",
            stack_frame_register_offset_map[&sret_reg], ARG_REGS[0],
        ));
    }

    let starting_arg_index = if function.struct_return.is_some() {
        1
    } else {
        0
    };

    for (i, arg) in function.arguments.iter().enumerate() {
        let ty = &function.registers[&arg].ty;

        assembler.emit(format!(
            "; store arg {} into its stack register",
            strip_ansi_escapes::strip_str(arg.to_string())
        ));
        assembler.emit(format!(
            "mov [rbp - {}], {}",
            stack_frame_register_offset_map[arg],
            ARG_REGS[starting_arg_index + i].with_size_bytes(ty.layout().size),
        ));
    }
    
    // TODO: move arguments passed on the stack into local registers

    /* Intermediate Blocks */

    for block in function.blocks.values() {
        assembler.label(block.id.to_string());

        for instruction in block.instructions.iter() {
            assembler.comment(strip_ansi_escapes::strip_str(instruction.to_string()));

            match instruction {
                lir::Instruction::LoadMem {
                    destination,
                    source,
                } => {
                    assembler.load_operand(X86FullRegister::Rax, *source);
                    
                    let ty = &function.registers[destination].ty;
                    let sized_reg = X86FullRegister::Rax.with_size_bytes(ty.layout().size);

                    assembler.emit(format!("mov {sized_reg}, [rax]"));
                    assembler.store_operand(*destination, X86FullRegister::Rax);
                }
                lir::Instruction::StoreMem {
                    destination,
                    source,
                } => {
                    let sized_reg = assembler.load_operand(X86FullRegister::Rax, *source);
                    assembler.load_operand(X86FullRegister::Rcx, *destination);
                    assembler.emit(format!("mov [rcx], {sized_reg}"));
                }
                lir::Instruction::AllocStack { destination, ty } => {
                    assembler.emit(format!(
                        "sub rsp, {}",
                        lir::align_to(ty.layout().size, ty.layout().alignment)
                    ));
                    assembler.store_operand(*destination, X86FullRegister::Rsp);
                }
                lir::Instruction::GetStructElementPointer {
                    destination,
                    source,
                    ty,
                    index,
                } => {
                    assembler.load_operand(X86FullRegister::Rax, *source);
                    assembler.emit(format!("lea rax, [rax + {}]", ty.offset_of(*index)));
                    assembler.store_operand(*destination, X86FullRegister::Rax);
                }
                lir::Instruction::GetArrayElementPointer {
                    destination,
                    source,
                    ty,
                    index,
                } => {
                    assembler.load_operand(X86FullRegister::Rax, *source);
                    assembler.load_operand(X86FullRegister::Rbx, *index);
                    assembler.emit(format!("mul rbx, {}", ty.layout().size));
                    assembler.emit("lea rax, [rax + rbx]");
                    assembler.store_operand(*destination, X86FullRegister::Rax);
                }
                lir::Instruction::Move {
                    destination,
                    source,
                } => {
                    assembler.load_operand(X86FullRegister::Rax, *source);
                    assembler.store_operand(*destination, X86FullRegister::Rax);
                }
                lir::Instruction::IntegerCast {
                    kind,
                    destination,
                    operand,
                } => {
                    todo!("emit asm for integer cast")
                }
                lir::Instruction::UnaryOperation {
                    operator,
                    destination,
                    operand,
                } => {
                    match operator {
                        UnaryOperatorKind::Deref => {
                            let sized_reg = assembler.load_operand(X86FullRegister::Rax, *operand);

                            assembler.emit(format!("mov {sized_reg}, [{sized_reg}]"));
                            assembler.store_operand(*destination, X86FullRegister::Rax);
                        }
                        UnaryOperatorKind::AddressOf { .. } => {
                            match operand {
                                lir::Operand::Register(reg_id) => {
                                    assembler.load_register_address(X86FullRegister::Rax, *reg_id);
                                }
                                lir::Operand::Immediate(lir::Immediate::NamedStaticLabel(
                                    label,
                                )) => {
                                    assembler.emit(format!("mov rax, {label}"));
                                }
                                lir::Operand::Immediate(immediate) => {
                                    unreachable!("cannot take address of immediate: {immediate:?}")
                                }
                            }

                            assembler.store_operand(*destination, X86FullRegister::Rax);
                        }
                        UnaryOperatorKind::LogicalNot => {
                            let sized_reg = assembler.load_operand(X86FullRegister::Rax, *operand);

                            assembler.emit("xor rcx, rcx"); // FIXME: necessary?
                            assembler.emit(format!("test {sized_reg}, {sized_reg}"));
                            assembler.emit("sete cl");
                            assembler.store_operand(*destination, X86FullRegister::Rcx);
                        }
                        UnaryOperatorKind::BitwiseNot => {
                            let sized_reg = assembler.load_operand(X86FullRegister::Rax, *operand);

                            assembler.emit(format!("not {sized_reg}"));
                            assembler.store_operand(*destination, X86FullRegister::Rax);
                        }
                        UnaryOperatorKind::Negate => {
                            let sized_reg = assembler.load_operand(X86FullRegister::Rax, *operand);

                            assembler.emit(format!("neg {sized_reg}"));
                            assembler.store_operand(*destination, X86FullRegister::Rax);
                        }
                    }
                }
                lir::Instruction::BinaryOperation {
                    operator,
                    destination,
                    lhs,
                    rhs,
                } => {
                    let lhs_sized_reg = assembler.load_operand(X86FullRegister::Rax, *lhs);
                    let rhs_sized_reg = assembler.load_operand(X86FullRegister::Rcx, *rhs);

                    // TODO: seprate into several instructions. group all
                    // sign-agnostic math instructions (and specify size) which
                    // includes equality, group signed math instructions (with
                    // specified size), group unsigned math instructions (with
                    // specified size)

                    match operator {
                        BinaryOperatorKind::Add => {
                            assembler.emit(format!("add {lhs_sized_reg}, {rhs_sized_reg}"));
                            assembler.store_operand(*destination, X86FullRegister::Rax);
                        }
                        BinaryOperatorKind::Subtract => {
                            assembler.emit(format!("sub {lhs_sized_reg}, {rhs_sized_reg}"));
                            assembler.store_operand(*destination, X86FullRegister::Rax);
                        }
                        BinaryOperatorKind::Multiply => {
                            // TODO: signed vs unsigned mul
                            assembler.emit(format!("imul {lhs_sized_reg}, {rhs_sized_reg}"));
                            assembler.store_operand(*destination, X86FullRegister::Rax);
                        }
                        BinaryOperatorKind::Divide => {
                            // TODO: signed vs unsigned div

                            let size = function.registers[destination].ty.layout().size;

                            match size {
                                2 => assembler.emit("cwd"),
                                4 => assembler.emit("cdq"),
                                8 => assembler.emit("cqo"),
                                _ => unreachable!(),
                            }

                            assembler.emit(format!("idiv {rhs_sized_reg}"));
                            assembler.store_operand(*destination, X86FullRegister::Rax);
                        }
                        BinaryOperatorKind::Modulus => {
                            // TODO: signed vs unsigned div
                            assembler.emit("xor rdx, rdx");

                            let size = function.registers[destination].ty.layout().size;

                            match size {
                                2 => assembler.emit("cwd"),
                                4 => assembler.emit("cdq"),
                                8 => assembler.emit("cqo"),
                                _ => unreachable!(),
                            }

                            assembler.emit(format!("idiv {rhs_sized_reg}"));
                            assembler.store_operand(*destination, X86FullRegister::Rdx);
                        }
                        BinaryOperatorKind::Equals => {
                            assembler.emit(format!("cmp {lhs_sized_reg}, {rhs_sized_reg}"));
                            assembler.emit("sete al");
                            assembler.store_operand(*destination, X86FullRegister::Rax);
                        }
                        BinaryOperatorKind::NotEquals => {
                            assembler.emit(format!("cmp {lhs_sized_reg}, {rhs_sized_reg}"));
                            assembler.emit("setne al");
                            assembler.store_operand(*destination, X86FullRegister::Rax);
                        }
                        /* TODO: unsigned versions of these */
                        BinaryOperatorKind::LessThan => {
                            assembler.emit(format!("cmp {lhs_sized_reg}, {rhs_sized_reg}"));
                            assembler.emit("setl al");
                            assembler.store_operand(*destination, X86FullRegister::Rax);
                        }
                        BinaryOperatorKind::LessThanOrEqualTo => {
                            assembler.emit(format!("cmp {lhs_sized_reg}, {rhs_sized_reg}"));
                            assembler.emit("setle al");
                            assembler.store_operand(*destination, X86FullRegister::Rax);
                        }
                        BinaryOperatorKind::GreaterThan => {
                            assembler.emit(format!("cmp {lhs_sized_reg}, {rhs_sized_reg}"));
                            assembler.emit("setg al");
                            assembler.store_operand(*destination, X86FullRegister::Rax);
                        }
                        BinaryOperatorKind::GreaterThanOrEqualTo => {
                            assembler.emit(format!("cmp {lhs_sized_reg}, {rhs_sized_reg}"));
                            assembler.emit("setge al");
                            assembler.store_operand(*destination, X86FullRegister::Rax);
                        }
                        BinaryOperatorKind::LogicalAnd => {
                            assembler.emit(format!("test {lhs_sized_reg}, {lhs_sized_reg}"));
                            assembler.emit(format!("setnz {lhs_sized_reg}"));

                            assembler.emit(format!("test {rhs_sized_reg}, {rhs_sized_reg}"));
                            assembler.emit(format!("setnz {rhs_sized_reg}"));

                            assembler.emit(format!("and {lhs_sized_reg}, {rhs_sized_reg}"));
                            assembler.store_operand(*destination, X86FullRegister::Rax);
                        }
                        BinaryOperatorKind::LogicalOr => {
                            assembler.emit(format!("test {lhs_sized_reg}, {lhs_sized_reg}"));
                            assembler.emit(format!("setnz {lhs_sized_reg}"));

                            assembler.emit(format!("test {rhs_sized_reg}, {rhs_sized_reg}"));
                            assembler.emit(format!("setnz {rhs_sized_reg}"));

                            assembler.emit(format!("or {lhs_sized_reg}, {rhs_sized_reg}"));
                            assembler.store_operand(*destination, X86FullRegister::Rax);
                        },
                        BinaryOperatorKind::BitwiseAnd => todo!(),
                        BinaryOperatorKind::BitwiseOr => todo!(),
                        BinaryOperatorKind::BitwiseXor => todo!(),
                        BinaryOperatorKind::ShiftLeft => {
                            assembler.emit(format!("shl {lhs_sized_reg}, {rhs_sized_reg}"));
                            assembler.store_operand(*destination, X86FullRegister::Rax);
                        }
                        BinaryOperatorKind::ShiftRight => todo!(),
                    }
                }
                lir::Instruction::Branch {
                    condition,
                    positive,
                    negative,
                } => {
                    match condition {
                        lir::Operand::Immediate(immediate) => {
                            assert!(matches!(immediate, lir::Immediate::Bool(_)))
                        }
                        lir::Operand::Register(register_id) => {
                            assert!(matches!(
                                function.registers[register_id].ty,
                                lir::Type::Integer(lir::IntegerWidth::I8)
                            ))
                        }
                    }

                    assembler.load_operand(X86FullRegister::Rax, *condition);

                    assembler.emit("test al, al");
                    assembler.emit(format!("jnz {positive}"));
                    assembler.emit(format!("jmp {negative}"));
                }
                lir::Instruction::Jump { destination } => {
                    assembler.emit(format!("jmp {destination}"));
                }
                lir::Instruction::Return { value } => {
                    // TODO: dont emit jmp if we are in the last block?

                    // load return value into rax
                    if let Some(v) = value {
                        assembler.load_operand(X86FullRegister::Rax, *v);
                    }

                    assembler.emit("jmp .exit");
                }
                lir::Instruction::FunctionCall {
                    target,
                    arguments,
                    destination,
                } => {
                    assert!(matches!(
                        function.type_of_operand(*target),
                        lir::Type::Pointer
                    ));

                    // Depending on the types of the arguments, we need to determine how we move them into registers

                    // First 6 integer arguments are passed in rdi, rsi, rdx, r10, r9, r8
                    // All other arguments are passed on the stack for now.

                    // Struct fields must be manually deconstructed in lowering
                    // for optimizations like passing the fields of small
                    // structs in registers.

                    let mut register_arguments = Vec::with_capacity(6);
                    let mut stack_arguments = Vec::new();

                    for arg in arguments {
                        match arg {
                            lir::Operand::Immediate(_) => {
                                if register_arguments.len() < 6 {
                                    register_arguments.push(arg);
                                } else {
                                    stack_arguments.push(arg);
                                }
                            }
                            lir::Operand::Register(register_id) => {
                                let ty = &function.registers[register_id].ty;

                                match ty {
                                    lir::Type::Integer(_)
                                    | lir::Type::Float(_)
                                    | lir::Type::Pointer => {
                                        if register_arguments.len() < 6 {
                                            register_arguments.push(arg);
                                        } else {
                                            stack_arguments.push(arg);
                                        }
                                    }
                                    lir::Type::Struct(_) | lir::Type::Array(_, _) => {
                                        stack_arguments.push(arg)
                                    }
                                }
                            }
                        }
                    }

                    for (i, operand) in register_arguments.into_iter().enumerate() {
                        assembler.load_operand(ARG_REGS[i], *operand);
                    }

                    // TODO: reserve enough stack space for the stack arguments
                    // (each one must be 8 byte aligned unless we figure out a
                    // better way to handle smaller integer loading)

                    for (i, arg) in stack_arguments.into_iter().enumerate() {
                        // similar to above but need to push to the stack
                        // instead + handle copying memory from our local stack
                        // frame into the newly allocated region
                        todo!("handle passing args on the stack")
                    }

                    match target {
                        lir::Operand::Immediate(lir::Immediate::FunctionLabel(name)) => {
                            assembler.emit(format!("call {}", name.value()));
                        }
                        _ => {
                            assembler.load_operand(X86FullRegister::Rax, *target);
                            assembler.emit("call rax");
                        }
                    }

                    if let Some(dest) = destination {
                        assembler.store_operand(*dest, X86FullRegister::Rax);
                    }
                }
                lir::Instruction::Phi { .. } => {
                    unreachable!("phi instructions should be eliminated before codegen")
                }
                lir::Instruction::Comment(text) => {
                    if options.emit_debug_info {
                        assembler.comment(text);
                    }
                }
            }
        }
    }

    assembler.function_epilogue();
    assembler.into_output()
}
