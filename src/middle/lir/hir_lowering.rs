use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    rc::Rc,
};

use crate::{
    frontend::{
        ast::{BinaryOperatorKind, UnaryOperatorKind},
        intern::InternedSymbol,
    },
    index::{Index, IndexVec},
    middle::{
        hir::{self, visit::Visitor},
        lir::{self, RegisterId},
        primitive::UIntKind,
        ty,
        type_check::ModuleTypeCheckResults,
    },
};

struct BodyLoweringContext<'hir> {
    module: &'hir hir::Module,
    type_map: &'hir ModuleTypeCheckResults,
    owner_id: hir::LocalDefId,
    local_symbol_name: InternedSymbol,
    global_symbol_name: InternedSymbol,

    next_static_label_id: &'hir mut lir::StaticLabelId,
    static_strings: &'hir mut BTreeMap<lir::StaticLabelId, InternedSymbol>,
    static_c_strings: &'hir mut BTreeMap<lir::StaticLabelId, InternedSymbol>,

    register_map: IndexVec<lir::RegisterId, lir::Register>,
    local_to_register_map: BTreeMap<hir::ItemLocalId, lir::RegisterId>,
    expression_to_operand_map: BTreeMap<hir::ItemLocalId, lir::Operand>,
    struct_return: Option<lir::RegisterId>,
    arguments: Vec<lir::RegisterId>,

    block_map: IndexVec<lir::BlockId, lir::Block>,
    block_stack: VecDeque<lir::BlockId>,

    /// Keeps track of the start of the nearest loop scope so that we
    loop_ctx_stack: Vec<LoopContext>,

    /// If we are lowering an expression where the destination is known (like a
    /// let smmt initializer), we use this destination instead of allocating a
    /// new temporary register to avoid unnecessary copying. MUST store a
    /// pointer to the place we're writing to if Some
    destination_register: Option<lir::RegisterId>,
    /// Keeps track of the semantic context of the current expression (the same
    /// expression node should be lowered differently based on what parent node
    /// it's enclosed in)
    expression_context: ExpressionContext,
}

struct LoopContext {
    // this is where continue blocks will jump to. within while loops this will
    // be the first condition block. within infinite loops, this will just be
    // the start of the body.
    start_block: lir::BlockId,
    // indexes of all the break instructions which were inserted within this
    // loop context and need to be patched with the merge block id once it is
    // known
    break_instructions: Vec<(lir::BlockId, usize)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExpressionContext {
    /// In this context we attempt to lower the current expression node as a
    /// place (memory address) instead of a value
    Place,
    /// In this context we attempt to load the value of the expression into the
    /// destination (read)
    Value,
}

impl<'hir> BodyLoweringContext<'hir> {
    fn create_static_label_id(&mut self) -> lir::StaticLabelId {
        let prev = *self.next_static_label_id;
        self.next_static_label_id.increment_by(1);
        prev
    }

    #[track_caller]
    fn create_register(&mut self, ty: ty::Type) -> lir::RegisterId {
        let id = self.register_map.next_index();
        let ty = self.lower_type_indirect(ty);

        assert!(!matches!(ty, lir::Type::Struct(_)));

        self.register_map.push(lir::Register { id, ty })
    }

    fn create_register_with_lir_type(&mut self, ty: lir::Type) -> lir::RegisterId {
        let id = self.register_map.next_index();
        self.register_map.push(lir::Register { id, ty })
    }

    fn create_block(&mut self) -> lir::BlockId {
        let id = self.block_map.next_index();
        self.block_map.push(lir::Block {
            id,
            instructions: Vec::new(),
            predecessors: BTreeSet::new(),
        })
    }

    #[track_caller]
    fn push_instruction(&mut self, instruction: lir::Instruction) -> usize {
        if let lir::Instruction::LoadMem { destination, .. } = &instruction {
            let lir_ty = &self.register_map[*destination].ty;
            assert!(
                lir_ty.layout().size <= 8,
                "invalid LoadMem instruction pushed in function {}",
                self.global_symbol_name
            );
        }

        let current_block = self.block_stack.back().unwrap();
        self.block_map[*current_block]
            .instructions
            .push(instruction);

        self.block_map[*current_block].instructions.len() - 1
    }

    fn push_comment(&mut self, comment: impl Into<String>) {
        self.push_instruction(lir::Instruction::Comment(comment.into()));
    }

    fn emit_get_struct_elem_ptr(
        &mut self,
        source: lir::Operand,
        ty: lir::Struct,
        index: usize,
    ) -> lir::RegisterId {
        let destination = self.create_register_with_lir_type(lir::Type::Pointer);

        self.push_instruction(lir::Instruction::GetStructElementPointer {
            destination,
            source,
            ty,
            index,
        });

        destination
    }

    fn emit_get_array_elem_ptr(
        &mut self,
        source: lir::Operand,
        ty: lir::Type,
        index: lir::Operand,
    ) -> lir::RegisterId {
        let destination = self.create_register_with_lir_type(lir::Type::Pointer);

        self.push_instruction(lir::Instruction::GetArrayElementPointer {
            destination,
            source,
            ty,
            index,
        });

        destination
    }

    fn emit_alloc_stack(&mut self, ty: lir::Type) -> lir::RegisterId {
        let destination = self.create_register_with_lir_type(lir::Type::Pointer);

        self.push_instruction(lir::Instruction::AllocStack { destination, ty });

        destination
    }

    fn emit_load_mem(&mut self, source: lir::Operand, ty: lir::Type) -> lir::RegisterId {
        assert!(
            ty.is_scalar(),
            "tried to load an aggregate type from memory"
        );

        let destination = self.create_register_with_lir_type(ty);

        self.push_instruction(lir::Instruction::LoadMem {
            destination,
            source,
        });

        destination
    }

    fn emit_store_mem(&mut self, destination: lir::Operand, source: lir::Operand, ty: lir::Type) {
        assert!(ty.is_scalar(), "tried to store an aggregate type to memory");

        self.push_instruction(lir::Instruction::StoreMem {
            destination,
            source,
        });
    }

    /// Emits a function call instruction and returns the destination register
    /// (if applicable)
    fn emit_function_call(
        &mut self,
        target: lir::Operand,
        arguments: Vec<lir::Operand>,
        return_ty: Option<lir::Type>,
    ) -> Option<lir::RegisterId> {
        if let Some(ty) = &return_ty {
            assert!(
                ty.is_scalar(),
                "aggregate types can only be returned using the sret argument"
            );
        }

        let destination = return_ty.map(|ty| self.create_register_with_lir_type(ty));

        self.push_instruction(lir::Instruction::FunctionCall {
            target,
            arguments,
            destination,
        });

        destination
    }

    fn emit_unary(
        &mut self,
        operator: lir::UnaryOperatorKind,
        operand: lir::Operand,
        ty: lir::Type,
    ) -> lir::RegisterId {
        let destination = self.create_register_with_lir_type(ty);

        self.push_instruction(lir::Instruction::UnaryOperation {
            operator: operator.try_into().unwrap(),
            destination,
            operand,
        });

        destination
    }

    fn emit_integer_cast(
        &mut self,
        kind: lir::IntegerCastKind,
        operand: lir::Operand,
        ty: lir::Type,
    ) -> lir::RegisterId {
        let destination = self.create_register_with_lir_type(ty);

        self.push_instruction(lir::Instruction::IntegerCast {
            kind,
            destination,
            operand,
        });

        destination
    }

    fn emit_phi(
        &mut self,
        sources: BTreeMap<lir::BlockId, lir::Operand>,
        ty: lir::Type,
    ) -> lir::RegisterId {
        let destination = self.create_register_with_lir_type(ty);

        self.push_instruction(lir::Instruction::Phi {
            destination,
            sources,
        });

        destination
    }

    fn emit_binary_op(
        &mut self,
        operator: BinaryOperatorKind,
        lhs: lir::Operand,
        rhs: lir::Operand,
        output_ty: lir::Type,
    ) -> lir::RegisterId {
        let destination = self.create_register_with_lir_type(output_ty);

        self.push_instruction(lir::Instruction::BinaryOperation {
            destination,
            operator,
            lhs,
            rhs,
        });

        destination
    }

    fn into_output(self) -> lir::FunctionDefinition {
        lir::FunctionDefinition {
            symbol_name: self.global_symbol_name,
            registers: self.register_map.into_entries().collect(),
            struct_return: self.struct_return,
            arguments: self.arguments,
            blocks: self.block_map.into_entries().collect(),
        }
    }

    #[track_caller]
    fn lower_type(&mut self, ty: ty::Type) -> lir::Type {
        match &*ty {
            ty::TypeKind::Unit => todo!("what do we do here?"),
            ty::TypeKind::Bool => lir::Type::Integer(lir::IntegerWidth::I8),
            ty::TypeKind::Char => lir::Type::Integer(lir::IntegerWidth::I32),
            ty::TypeKind::Integer(int_kind) => lir::Type::Integer((*int_kind).into()),
            ty::TypeKind::UnsignedInteger(uint_kind) => lir::Type::Integer((*uint_kind).into()),
            ty::TypeKind::Float(float_kind) => lir::Type::Float((*float_kind).into()),
            ty::TypeKind::CStr | ty::TypeKind::Pointer(_) => lir::Type::Pointer,
            ty::TypeKind::Str | ty::TypeKind::Slice(_) => lir::Type::Struct(lir::Struct::slice()),
            ty::TypeKind::Array { ty, length } => {
                lir::Type::Array(Rc::new(self.lower_type(ty.clone())), *length)
            }
            ty::TypeKind::Tuple(items) => lir::Type::Struct(lir::Struct(
                items.iter().map(|ty| self.lower_type(ty.clone())).collect(),
            )),
            // FIXME: do we really want this to be a struct? should this be a pointer type?
            ty::TypeKind::Struct { fields, .. } => lir::Type::Struct(lir::Struct(
                fields
                    .iter()
                    .map(|field| self.lower_type(field.ty.clone()))
                    .collect(),
            )),
            ty::TypeKind::Enum { .. } => lir::Type::Integer(lir::IntegerWidth::I32),
            ty::TypeKind::FunctionPointer { .. } => lir::Type::Pointer,
            ty::TypeKind::Any => lir::Type::Pointer,
            ty::TypeKind::Never | ty::TypeKind::Infer(_) | ty::TypeKind::Error => unreachable!(),
        }
    }

    /// Lowers types for indirect usage (aggregates become pointers)
    fn lower_type_indirect(&mut self, ty: ty::Type) -> lir::Type {
        match &*ty {
            ty::TypeKind::Str
            | ty::TypeKind::Slice(_)
            | ty::TypeKind::Array { .. }
            | ty::TypeKind::Struct { .. }
            | ty::TypeKind::Tuple(_) => lir::Type::Pointer,
            _ => self.lower_type(ty),
        }
    }

    fn lower_constant_string(
        &mut self,
        symbol: InternedSymbol,
        expression: Option<Rc<hir::Expression>>,
    ) -> lir::RegisterId {
        // strings are actually fat pointers which need to be
        // stored as structs on the stack. we need to allocate
        // room for the string struct, fill its fields with the
        // static pointer and length, and then return the
        // register which stores the pointer as the target of
        // the move instead of an immediate.

        /* Create the struct on the stack */

        let struct_ptr_reg = self.destination_register.unwrap_or_else(|| {
            let reg = self.create_register_with_lir_type(lir::Type::Pointer);

            self.push_instruction(lir::Instruction::AllocStack {
                destination: reg,
                ty: lir::Type::Struct(lir::Struct::slice()),
            });

            reg
        });

        /* Set the pointer field */

        let pointer_element_ptr_reg = self.create_register_with_lir_type(lir::Type::Pointer);
        self.push_instruction(lir::Instruction::GetStructElementPointer {
            destination: pointer_element_ptr_reg,
            source: lir::Operand::Register(struct_ptr_reg),
            ty: lir::Struct::slice(),
            index: 0,
        });

        // FIXME: deduplicate strings

        let id = self.create_static_label_id();
        self.static_strings.insert(id, symbol);
        self.push_instruction(lir::Instruction::StoreMem {
            destination: lir::Operand::Register(pointer_element_ptr_reg),
            source: lir::Operand::Immediate(lir::Immediate::AnonymousStaticLabel(id)),
        });

        /* Set the length field */

        let length_element_ptr_reg = self.create_register_with_lir_type(lir::Type::Pointer);
        self.push_instruction(lir::Instruction::GetStructElementPointer {
            destination: length_element_ptr_reg,
            source: lir::Operand::Register(struct_ptr_reg),
            ty: lir::Struct::slice(),
            index: 1,
        });

        self.push_instruction(lir::Instruction::StoreMem {
            destination: lir::Operand::Register(length_element_ptr_reg),
            source: lir::Operand::Immediate(lir::Immediate::Int(
                symbol.value().len() as _,
                lir::IntegerWidth::I64,
            )),
        });

        /* Move operand is the reg that points to the base of the struct */

        if let Some(e) = expression {
            self.expression_to_operand_map
                .insert(e.hir_id.local_id, lir::Operand::Register(struct_ptr_reg));
        }

        struct_ptr_reg
    }

    fn print_string(&mut self, str_ptr: lir::Operand) -> lir::RegisterId {
        /* Extract struct fields */

        let ptr_ptr_reg = self.emit_get_struct_elem_ptr(str_ptr, lir::Struct::slice(), 0);
        let ptr_reg = self.emit_load_mem(lir::Operand::Register(ptr_ptr_reg), lir::Type::Pointer);

        let len_ptr_reg = self.emit_get_struct_elem_ptr(str_ptr, lir::Struct::slice(), 1);
        let len_reg = self.emit_load_mem(
            lir::Operand::Register(len_ptr_reg),
            lir::Type::Integer(lir::IntegerWidth::I64),
        );

        let dest_reg = self.emit_function_call(
            lir::Operand::Immediate(lir::Immediate::FunctionLabel(InternedSymbol::new(
                "__$print_str",
            ))),
            vec![
                lir::Operand::Register(ptr_reg),
                lir::Operand::Register(len_reg),
            ],
            Some(lir::Type::Integer(lir::IntegerWidth::I64)),
        );

        dest_reg.unwrap()
    }

    fn lower_binary_op(
        &mut self,
        output_ty: ty::Type,
        operator: BinaryOperatorKind,
        lhs: Rc<hir::Expression>,
        rhs: Rc<hir::Expression>,
    ) -> lir::RegisterId {
        let operand_ty = self.type_map.get_type(lhs.hir_id);

        // for logical boolean operators we need to add short circuiting blocks
        // into the calculation. for all other operators, we can just emit the
        // instruction directly.

        if operator == BinaryOperatorKind::LogicalAnd {
            assert!(output_ty.is_bool());
            assert!(operand_ty.is_bool());

            // evaluate the LHS and record the current block id
            //
            // create a new block and evaluate the RHS and record the current block id
            //
            // create a new block (fallthrough)
            //
            // create a merge block
            //
            // add an unconditional branch from the fallthrough block to the merge block
            //
            // add a phi node to the merge block (if coming from the first
            // block or the second block, we branched so false, if coming from
            // the last block, we never conditionally branched so true)

            self.with_dest_and_expr_ctx(None, ExpressionContext::Value, |this| {
                this.visit_expression(lhs.clone())
            });

            let lhs_last_block = *self.block_stack.back().unwrap();

            let rhs_first_block = self.create_block();

            let rhs_last_block: lir::BlockId;
            {
                self.block_stack.push_back(rhs_first_block);
                self.with_dest_and_expr_ctx(None, ExpressionContext::Value, |this| {
                    this.visit_expression(rhs.clone())
                });
                self.block_stack.pop_back();

                // the most recently created block is the block we need to
                // insert the merge jump into. if no blocks were created
                // while visiting the subexpression, its still the current
                // block.
                rhs_last_block = lir::BlockId::new(self.block_map.len() - 1);
            }

            let fallthrough_block = self.create_block();

            let merge_block = self.create_block();

            let lhs_value = self.expression_to_operand_map[&lhs.hir_id.local_id];
            let rhs_value = self.expression_to_operand_map[&rhs.hir_id.local_id];

            self.block_map[lhs_last_block]
                .instructions
                .push(lir::Instruction::Branch {
                    condition: lhs_value,
                    positive: rhs_first_block,
                    negative: merge_block,
                });
            self.block_map[rhs_last_block]
                .instructions
                .push(lir::Instruction::Branch {
                    condition: rhs_value,
                    positive: fallthrough_block,
                    negative: merge_block,
                });

            self.block_map[fallthrough_block]
                .instructions
                .push(lir::Instruction::Jump {
                    destination: merge_block,
                });

            self.block_map[rhs_first_block]
                .predecessors
                .insert(lhs_last_block);
            self.block_map[fallthrough_block]
                .predecessors
                .insert(rhs_last_block);
            self.block_map[merge_block]
                .predecessors
                .extend([lhs_last_block, rhs_last_block, fallthrough_block].into_iter());

            self.block_stack.pop_back();
            self.block_stack.push_back(merge_block);

            self.emit_phi(
                BTreeMap::from([
                    (
                        lhs_last_block,
                        lir::Operand::Immediate(lir::Immediate::Bool(false)),
                    ),
                    (
                        rhs_last_block,
                        lir::Operand::Immediate(lir::Immediate::Bool(false)),
                    ),
                    (
                        fallthrough_block,
                        lir::Operand::Immediate(lir::Immediate::Bool(true)),
                    ),
                ]),
                lir::Type::Integer(lir::IntegerWidth::I8),
            )
        } else if operator == BinaryOperatorKind::LogicalOr {
            self.with_dest_and_expr_ctx(None, ExpressionContext::Value, |this| {
                this.visit_expression(lhs.clone())
            });

            let lhs_last_block = *self.block_stack.back().unwrap();

            let rhs_first_block = self.create_block();

            let rhs_last_block: lir::BlockId;
            {
                self.block_stack.push_back(rhs_first_block);
                self.with_dest_and_expr_ctx(None, ExpressionContext::Value, |this| {
                    this.visit_expression(rhs.clone())
                });
                self.block_stack.pop_back();

                // the most recently created block is the block we need to
                // insert the merge jump into. if no blocks were created
                // while visiting the subexpression, its still the current
                // block.
                rhs_last_block = lir::BlockId::new(self.block_map.len() - 1);
            }

            let fallthrough_block = self.create_block();

            let merge_block = self.create_block();

            let lhs_value = self.expression_to_operand_map[&lhs.hir_id.local_id];
            let rhs_value = self.expression_to_operand_map[&rhs.hir_id.local_id];

            self.block_map[lhs_last_block]
                .instructions
                .push(lir::Instruction::Branch {
                    condition: lhs_value,
                    positive: merge_block,
                    negative: rhs_first_block,
                });
            self.block_map[rhs_last_block]
                .instructions
                .push(lir::Instruction::Branch {
                    condition: rhs_value,
                    positive: merge_block,
                    negative: fallthrough_block,
                });

            self.block_map[fallthrough_block]
                .instructions
                .push(lir::Instruction::Jump {
                    destination: merge_block,
                });

            self.block_map[rhs_first_block]
                .predecessors
                .insert(lhs_last_block);
            self.block_map[fallthrough_block]
                .predecessors
                .insert(rhs_last_block);
            self.block_map[merge_block]
                .predecessors
                .extend([lhs_last_block, rhs_last_block, fallthrough_block].into_iter());

            self.block_stack.pop_back();
            self.block_stack.push_back(merge_block);

            self.emit_phi(
                BTreeMap::from([
                    (
                        lhs_last_block,
                        lir::Operand::Immediate(lir::Immediate::Bool(true)),
                    ),
                    (
                        rhs_last_block,
                        lir::Operand::Immediate(lir::Immediate::Bool(true)),
                    ),
                    (
                        fallthrough_block,
                        lir::Operand::Immediate(lir::Immediate::Bool(false)),
                    ),
                ]),
                lir::Type::Integer(lir::IntegerWidth::I8),
            )
        } else {
            self.with_dest_and_expr_ctx(None, ExpressionContext::Value, |this| {
                this.visit_expression(lhs.clone());
                this.visit_expression(rhs.clone());
            });

            let lhs_value = self.expression_to_operand_map[&lhs.hir_id.local_id];
            let rhs_value = self.expression_to_operand_map[&rhs.hir_id.local_id];

            self.lower_binary_op_helper(output_ty, operand_ty, operator, lhs_value, rhs_value)
        }
    }

    fn lower_binary_op_helper(
        &mut self,
        output_ty: ty::Type,
        operand_ty: ty::Type,
        operator: BinaryOperatorKind,
        lhs: lir::Operand,
        rhs: lir::Operand,
    ) -> lir::RegisterId {
        match &*operand_ty {
            ty::TypeKind::Unit => todo!(),
            ty::TypeKind::Bool
            | ty::TypeKind::Char
            | ty::TypeKind::Integer(_)
            | ty::TypeKind::UnsignedInteger(_)
            | ty::TypeKind::Float(_)
            | ty::TypeKind::Pointer(_)
            | ty::TypeKind::FunctionPointer { .. }
            | ty::TypeKind::Enum { .. }
            | ty::TypeKind::Any => {
                // TODO: if LHS is a pointer and RHS is a usize, scale by size of pointee type

                let output_lir_ty = self.lower_type(output_ty.clone());

                self.emit_binary_op(operator, lhs, rhs, output_lir_ty)
            }
            ty::TypeKind::Str => todo!(),
            ty::TypeKind::CStr => todo!(),
            ty::TypeKind::Slice(_) => todo!(),
            ty::TypeKind::Array { ty: _, length: _ } => todo!(),
            ty::TypeKind::Tuple(elements) => {
                core::assert_matches!(
                    operator,
                    BinaryOperatorKind::Equals | BinaryOperatorKind::NotEquals
                );

                // TODO: desugar into `x_1 <op> y_1 && x_2 <op> y_2 && ...`
                // in a preceding HIR transformation pass to add short
                // circuiting support

                // our algorithm here is load both elements into registers,
                // compare them and store in a result register, then emit
                // logical and on all of the results

                let structure = lir::Struct(
                    elements
                        .iter()
                        .map(|ty| self.lower_type(ty.clone()))
                        .collect(),
                );

                // Collect results of comparing all sub elements

                let result_regs = elements
                    .iter()
                    .enumerate()
                    .map(|(i, field_ty)| {
                        let field_lir_ty = self.lower_type(field_ty.clone());

                        let lhs_ptr_reg = self.emit_get_struct_elem_ptr(lhs, structure.clone(), i);
                        let rhs_ptr_reg = self.emit_get_struct_elem_ptr(rhs, structure.clone(), i);

                        // for scalar elements, load from memory and
                        // recurse. for aggregates, recurse with the pointer
                        // to the element

                        if field_ty.is_aggregate() {
                            self.lower_binary_op_helper(
                                output_ty.clone(),
                                field_ty.clone(),
                                operator,
                                lir::Operand::Register(lhs_ptr_reg),
                                lir::Operand::Register(rhs_ptr_reg),
                            )
                        } else {
                            let lhs_reg = self.emit_load_mem(
                                lir::Operand::Register(lhs_ptr_reg),
                                field_lir_ty.clone(),
                            );
                            let rhs_reg = self.emit_load_mem(
                                lir::Operand::Register(rhs_ptr_reg),
                                field_lir_ty.clone(),
                            );

                            self.lower_binary_op_helper(
                                output_ty.clone(),
                                field_ty.clone(),
                                operator,
                                lir::Operand::Register(lhs_reg),
                                lir::Operand::Register(rhs_reg),
                            )
                        }
                    })
                    .collect::<Vec<_>>();

                // Make sure that all sub-elements compared equal

                let mut result_reg = *result_regs.first().unwrap();

                for reg in result_regs.into_iter().skip(1) {
                    result_reg = self.emit_binary_op(
                        BinaryOperatorKind::LogicalAnd,
                        lir::Operand::Register(result_reg),
                        lir::Operand::Register(reg),
                        lir::Type::Integer(lir::IntegerWidth::I8),
                    );
                }

                result_reg
            }
            ty::TypeKind::Struct {
                def_id,
                name,
                fields,
            } => todo!(),
            ty::TypeKind::Never | ty::TypeKind::Infer(_) | ty::TypeKind::Error => {
                unreachable!()
            }
        }
    }

    /// Creates a copy of the src in the value context and returns it. If `dest`
    /// is None, a new slot will be allocated on the stack for the result. If
    /// `dest` is Some, it must be a pointer type and it will be used as the
    /// destination for the copy instead (but only if the type is an aggregate)
    fn lower_copy(
        &mut self,
        dest: Option<lir::RegisterId>,
        src: lir::Operand,
        ty: lir::Type,
    ) -> lir::Operand {
        match ty {
            lir::Type::Struct(structure_ty) => {
                // FIXME: could we just memcpy instead?

                let dest = dest.unwrap_or_else(|| {
                    self.emit_alloc_stack(lir::Type::Struct(structure_ty.clone()))
                });

                for (i, f) in structure_ty.0.iter().enumerate() {
                    match f {
                        // for struct types, get the ptr to the src value, get the ptr to
                        // the dest value, and recurse
                        lir::Type::Struct(_) => {
                            let dest_ptr = self.emit_get_struct_elem_ptr(
                                lir::Operand::Register(dest),
                                structure_ty.clone(),
                                i,
                            );

                            let src_ptr =
                                self.emit_get_struct_elem_ptr(src, structure_ty.clone(), i);

                            self.lower_copy(
                                Some(dest_ptr),
                                lir::Operand::Register(src_ptr),
                                f.clone(),
                            );
                        }
                        lir::Type::Array(_, _) => todo!(),
                        // for scalar types, get the ptr to the src value, load into a
                        // temporary reg, get the ptr to the dest value, store the temp
                        // value
                        _ => {
                            let src_ptr =
                                self.emit_get_struct_elem_ptr(src, structure_ty.clone(), i);
                            let tmp =
                                self.emit_load_mem(lir::Operand::Register(src_ptr), f.to_owned());

                            let dest_ptr = self.emit_get_struct_elem_ptr(
                                lir::Operand::Register(dest),
                                structure_ty.clone(),
                                i,
                            );
                            self.emit_store_mem(
                                lir::Operand::Register(dest_ptr),
                                lir::Operand::Register(tmp),
                                f.to_owned(),
                            );
                        }
                    }
                }

                lir::Operand::Register(dest)
            }
            lir::Type::Array(_, _) => todo!(),
            _ => src,
        }
    }

    /// Given a pointer to a value, loads it from memory into a register. For
    /// scalar types this is just a LoadMem. For aggregate types this turns into
    /// a lower_copy() call which allocates a new temporary stack slot to hold
    /// the value.
    ///
    /// `dest` should be None for pointers to scalar types.
    fn emit_load_from_ptr(
        &mut self,
        dest_ptr: Option<lir::RegisterId>,
        src_ptr: lir::Operand,
        ty: lir::Type,
    ) -> lir::RegisterId {
        match ty {
            lir::Type::Struct(_) => {
                let lir::Operand::Register(reg) = self.lower_copy(dest_ptr, src_ptr, ty) else {
                    unreachable!()
                };

                reg
            }
            lir::Type::Array(_, _) => todo!(),
            _ => self.emit_load_mem(src_ptr, ty),
        }
    }

    fn with_dest_and_expr_ctx<R>(
        &mut self,
        dest: Option<lir::RegisterId>,
        ctx: ExpressionContext,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        self.with_destination(dest, |this| this.with_expression_context(ctx, f))
    }

    fn with_expression_context<R>(
        &mut self,
        ctx: ExpressionContext,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let prev = self.expression_context;
        self.expression_context = ctx;

        let res = f(self);

        self.expression_context = prev;
        res
    }

    fn with_destination<R>(
        &mut self,
        dest: Option<lir::RegisterId>,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let prev = self.destination_register.take();
        self.destination_register = dest;

        let res = f(self);

        self.destination_register = prev;
        res
    }

    /// Shared helper for lowering both normal functions and method calls
    fn lower_function_call(
        &mut self,
        symbol: InternedSymbol,
        self_arg: Option<(hir::SelfParameter, Rc<hir::Expression>)>,
        arguments: impl Iterator<Item = Rc<hir::Expression>>,
        return_ty: Option<ty::Type>,
    ) -> Option<lir::RegisterId> {
        let mut args = Vec::new();

        let self_value = self_arg.map(|(self_parameter, self_target)| {
            // 4 options here:
            //  - copy call on an owned type
            //    - create a copy by copying each field
            //    - pass it as an argument
            //  - copy call on an pointer type
            //    - create a copy through dereferencing each field
            //    - pass it as an argument
            //  - pointer call on an owned type
            //    - take the memory address of the type
            //    - pass the pointer
            //  - pointer call on a pointer type
            //    - pass the pointer as the argument

            let self_target_ty = self.type_map.get_type(self_target.hir_id);

            match (self_parameter, &*self_target_ty) {
                (
                    hir::SelfParameter::Owned,
                    ty::TypeKind::Struct {
                        def_id,
                        name,
                        fields,
                    },
                ) => todo!(),
                (hir::SelfParameter::Owned, ty::TypeKind::Pointer(_)) => todo!(),
                (hir::SelfParameter::Pointer { is_mutable: _ }, ty::TypeKind::Pointer(_)) => {
                    self.expression_to_operand_map[&self_target.hir_id.local_id]
                }
                // structs are actually stored as pointers to their
                // allocation so this is the same as the pointer
                // case
                (hir::SelfParameter::Pointer { is_mutable: _ }, ty::TypeKind::Struct { .. }) => {
                    self.expression_to_operand_map[&self_target.hir_id.local_id]
                }
                (_, ty) => unreachable!("method call on illegal type: {ty}"),
            }
        });

        // evaluate all of the arguments and pass them by value (copies will be
        // made automatically and new allocations will be created as necessary
        // for aggregates)
        for arg in arguments {
            self.with_dest_and_expr_ctx(None, ExpressionContext::Value, |this| {
                this.visit_expression(arg.clone())
            });

            args.push(self.expression_to_operand_map[&arg.hir_id.local_id]);
        }

        let return_lir_ty = return_ty.clone().map(|ty| self.lower_type(ty));

        let sret_reg = return_lir_ty
            .clone()
            .filter(|ty| ty.is_aggregate())
            .map(|ty| {
                self.destination_register
                    .unwrap_or_else(|| self.emit_alloc_stack(ty))
            });

        let args = sret_reg
            .map(lir::Operand::Register)
            .into_iter()
            .chain(self_value)
            .chain(args)
            .collect();

        // returning a struct:
        //
        // caller allocates room for the struct on the stack
        // caller passes a pointer to this struct as a hidden sret argument (rdi)
        // callee does alloc stack
        // move exprs into fields
        // memcpy from stack into return struct
        //
        // if optimizer recognizes that struct return is
        // the last block, above can be simplified to
        // move exprs directly into struct fields
        // instead of calling memcpy

        let return_reg = self.emit_function_call(
            lir::Operand::Immediate(lir::Immediate::FunctionLabel(symbol)),
            args,
            // if the return type is an aggregate, its already being passed as
            // in the sret argument so we dont expect a direct return value from
            // the function call itself
            return_lir_ty.filter(|ty| ty.is_scalar()),
        );

        return_reg.or(sret_reg)
    }
}

impl<'hir> hir::visit::Visitor for BodyLoweringContext<'hir> {
    fn visit_function_definition(
        &mut self,
        _name: &hir::Path,
        signature: &hir::FunctionSignature,
        body: hir::BodyId,
    ) {
        let body = self.module.get_body(body);

        if let Some(return_ty) = &signature.return_type {
            let return_ty = self.type_map.get_type(return_ty.hir_id);

            if return_ty.is_aggregate() {
                let sret_reg = self.create_register_with_lir_type(lir::Type::Pointer);
                self.struct_return = Some(sret_reg);
            }
        }

        if let Some(self_ty) = self.type_map.function_results[&self.owner_id]
            .self_type
            .clone()
        {
            let id = self.create_register(self_ty);
            self.arguments.push(id);
        }

        for (name, ty) in body.params.iter().zip(signature.parameters.iter()) {
            let ty = self.type_map.get_type(ty.hir_id);
            let id = self.create_register(ty);

            self.local_to_register_map.insert(name.hir_id.local_id, id);
            self.arguments.push(id);
        }

        let block_id = self.create_block();
        self.block_stack.push_back(block_id);

        hir::visit::walk_body(self, body.clone());

        let implicit_return = body.block.expression.as_ref();

        if let Some(e) = implicit_return
            && let ty = self.type_map.get_type(e.hir_id)
            && ty.is_aggregate()
        {
            // TODO: if the return value is a local variable, dont allocate
            // stack space for it and instead just use the sret. if the value is
            // a temporary, also just use the sret. if the value is a struct
            // initializer literal, use the sret (is this a unique case?). we
            // should never need to copy here.

            let dest_struct_ptr = self
                .struct_return
                .expect("functions returning a struct should have an sret set");
            let src_struct_ptr = self.expression_to_operand_map[&e.hir_id.local_id];

            let ty = self.lower_type(ty);
            self.lower_copy(Some(dest_struct_ptr), src_struct_ptr, ty);
            self.push_instruction(lir::Instruction::Return { value: None });
        } else {
            // FIXME: dont add an extra return if the last expr is already a return stmt

            // Main implicitly returns 0 even if there is no return value
            let value = implicit_return
                .and_then(|e| self.expression_to_operand_map.get(&e.hir_id.local_id))
                .copied()
                .or_else(|| {
                    (self.local_symbol_name.value() == "main").then_some(lir::Operand::Immediate(
                        lir::Immediate::Int(0, lir::IntegerWidth::I8),
                    ))
                });

            let current_block = lir::BlockId::new(self.block_map.len() - 1);

            self.block_map[current_block]
                .instructions
                .push(lir::Instruction::Return { value });
        }
    }

    fn visit_let_statement(&mut self, let_stmt: std::rc::Rc<hir::LetStatement>) {
        self.push_comment(format!("let {} = ...", let_stmt.name.symbol));

        let ty = self.type_map.get_type(let_stmt.hir_id);
        let lir_ty = self.lower_type(ty.clone());

        let ptr_reg = self.emit_alloc_stack(lir_ty.clone());
        self.local_to_register_map
            .insert(let_stmt.hir_id.local_id, ptr_reg);

        // for scalars, its enough to simply compute their value into a
        // temporary and store the resulting temporary into the allocated stack
        // slot. for aggregate types we want to construct the value in place in
        // memory to avoid the extra copy, so we set a global destination
        // register for the traversal

        self.with_dest_and_expr_ctx(
            ty.is_aggregate().then(|| ptr_reg),
            ExpressionContext::Value,
            |this| hir::visit::walk_let_statement(this, let_stmt.clone()),
        );

        // for scalar types, add a store into the stack slot
        if let Some(init) = &let_stmt.initializer {
            let init_value = self.expression_to_operand_map[&init.hir_id.local_id];

            if !ty.is_aggregate() {
                self.emit_store_mem(lir::Operand::Register(ptr_reg), init_value, lir_ty);
            } else {
                debug_assert_eq!(
                    init_value,
                    lir::Operand::Register(ptr_reg),
                    "let stmt destination was not respected for expr: {init:#?}"
                );
            }
        }
    }

    fn visit_expression(&mut self, expression: std::rc::Rc<hir::Expression>) {
        match &expression.kind {
            hir::ExpressionKind::Literal(literal) => {
                let value = match literal {
                    hir::Literal::Boolean(v) => lir::Immediate::Bool(*v),
                    hir::Literal::Char(v) => lir::Immediate::Int(*v as u64, lir::IntegerWidth::I32),
                    hir::Literal::Integer(v, k) => lir::Immediate::Int(
                        *v,
                        match k {
                            hir::LiteralIntegerKind::Signed(int_kind) => (*int_kind).into(),
                            hir::LiteralIntegerKind::Unsigned(uint_kind) => (*uint_kind).into(),
                            hir::LiteralIntegerKind::Unsuffixed => {
                                let ty = self.type_map.get_type(expression.hir_id);

                                match &*ty {
                                    ty::TypeKind::Integer(int_kind) => (*int_kind).into(),
                                    ty::TypeKind::UnsignedInteger(uint_kind) => (*uint_kind).into(),
                                    ty::TypeKind::Pointer(_) | ty::TypeKind::Any => {
                                        UIntKind::USize.into()
                                    }
                                    ty => unreachable!("expr has type {ty}: {expression:#?}"),
                                }
                            }
                        },
                    ),
                    hir::Literal::Float(..) => todo!("load float"),
                    hir::Literal::String(s) => {
                        self.lower_constant_string(*s, Some(expression.clone()));
                        return;
                    }
                    hir::Literal::ByteString(_) => {
                        // byte strings follow the same rule as above since they
                        // are native slices (fat pointers) and not just a
                        // pointer to some bytes.
                        todo!("load byte string (need to allocate in static mem)")
                    }
                    hir::Literal::CString(_) => {
                        // c strings are much simpler since they are just fancy
                        // raw pointers
                        todo!("load c string (need to allocate in static mem)")
                    }
                };

                self.expression_to_operand_map
                    .insert(expression.hir_id.local_id, lir::Operand::Immediate(value));
            }
            hir::ExpressionKind::Path(path) => {
                match path.resolution() {
                    hir::Resolution::Local(local_id) => {
                        let src_reg = self.local_to_register_map[local_id];

                        match self.expression_context {
                            // just return the pointer to the stack slot
                            ExpressionContext::Place => {
                                let ty = self.type_map.get_type(expression.hir_id);

                                if self.arguments.contains(&src_reg) && !ty.is_aggregate() {
                                    todo!(
                                        "during codegen, make sure to spill this argument into a stack slot in the prologue"
                                    );
                                }

                                self.expression_to_operand_map.insert(
                                    expression.hir_id.local_id,
                                    lir::Operand::Register(src_reg),
                                );
                            }
                            // for scalars, just return the src register, for
                            // aggregates, copy into current destination or
                            // create a new one if this is an intermediate
                            ExpressionContext::Value => {
                                let ty = self.type_map.get_type(expression.hir_id);
                                let lir_ty = self.lower_type(ty);

                                let value = if self.arguments.contains(&src_reg) {
                                    self.lower_copy(
                                        self.destination_register,
                                        lir::Operand::Register(src_reg),
                                        lir_ty,
                                    )
                                } else {
                                    lir::Operand::Register(self.emit_load_from_ptr(
                                        self.destination_register,
                                        lir::Operand::Register(src_reg),
                                        lir_ty,
                                    ))
                                };

                                self.expression_to_operand_map
                                    .insert(expression.hir_id.local_id, value);
                            }
                        }
                    }
                    hir::Resolution::Definition(hir::DefinitionKind::Static, def_id) => {
                        let hir::ItemKind::Static {
                            is_mutable,
                            name,
                            ty,
                            initializer,
                        } = &self
                            .module
                            .get_owner(*def_id)
                            .unwrap()
                            .node()
                            .as_item()
                            .unwrap()
                            .kind
                        else {
                            unreachable!()
                        };

                        let ty = self.type_map.get_type(ty.hir_id);

                        let src =
                            lir::Operand::Immediate(lir::Immediate::NamedStaticLabel(name.symbol));

                        match self.expression_context {
                            // just return the pointer to the static
                            ExpressionContext::Place => {
                                self.expression_to_operand_map
                                    .insert(expression.hir_id.local_id, src);
                            }
                            // load the value from the stack slot into the
                            // destination register, or for aggregate types
                            // allocate a new stack slot
                            ExpressionContext::Value => {
                                let lir_ty = self.lower_type(ty);

                                let value =
                                    self.emit_load_from_ptr(self.destination_register, src, lir_ty);

                                self.expression_to_operand_map.insert(
                                    expression.hir_id.local_id,
                                    lir::Operand::Register(value),
                                );
                            }
                        }
                    }
                    hir::Resolution::Definition(hir::DefinitionKind::EnumVariant, def_id) => {
                        // FIXME: is this right? if we call a function on an
                        // enum variant is it in the value context? (i think
                        // not)
                        debug_assert_eq!(self.expression_context, ExpressionContext::Value);

                        let enum_def_id = self.module.definitions[def_id].as_non_owner().unwrap();
                        let enum_def = self
                            .module
                            .get_owner(enum_def_id.owner)
                            .unwrap()
                            .node()
                            .as_item()
                            .unwrap();

                        let hir::ItemKind::Enum { variants, .. } = &enum_def.kind else {
                            unreachable!()
                        };

                        let index = variants.iter().position(|v| v.def_id == *def_id).unwrap();

                        self.expression_to_operand_map.insert(
                            expression.hir_id.local_id,
                            lir::Operand::Immediate(lir::Immediate::Int(
                                index as _,
                                // TODO: choose width based on enum size
                                lir::IntegerWidth::I32,
                            )),
                        );
                    }
                    hir::Resolution::Definition(
                        hir::DefinitionKind::Function | hir::DefinitionKind::AssociatedFunction,
                        def_id,
                    ) => {
                        let hir::ItemKind::Function {
                            name, signature, ..
                        } = &self
                            .module
                            .get_owner(*def_id)
                            .unwrap()
                            .node()
                            .as_item()
                            .unwrap()
                            .kind
                        else {
                            unreachable!()
                        };

                        let symbol = self.module.global_symbol_for(name);

                        self.expression_to_operand_map.insert(
                            expression.hir_id.local_id,
                            lir::Operand::Immediate(lir::Immediate::FunctionLabel(symbol)),
                        );
                    }
                    hir::Resolution::Definition(..)
                    | hir::Resolution::IntrinsicFunction(..)
                    | hir::Resolution::Primitive(..) => {}
                }
            }
            hir::ExpressionKind::This => {
                // self is always the 0th argument when present
                let src_reg = self.arguments[0];

                match self.expression_context {
                    // just return the pointer to the stack slot
                    ExpressionContext::Place => {
                        self.expression_to_operand_map
                            .insert(expression.hir_id.local_id, lir::Operand::Register(src_reg));
                    }
                    // for scalars, just return the src register, for
                    // aggregates, copy into current destination or
                    // create a new one if this is an intermediate
                    ExpressionContext::Value => {
                        let ty = self.type_map.get_type(expression.hir_id);
                        let lir_ty = self.lower_type(ty);

                        let value = self.lower_copy(
                            self.destination_register,
                            lir::Operand::Register(src_reg),
                            lir_ty,
                        );

                        self.expression_to_operand_map
                            .insert(expression.hir_id.local_id, value);
                    }
                }
            }
            hir::ExpressionKind::Array(hir::ArrayInitializer::Repeated { value, length }) => {
                todo!()
            }
            hir::ExpressionKind::Array(hir::ArrayInitializer::Specific(values)) => {
                let array_ty = self.lower_type(self.type_map.get_type(expression.hir_id));
                let lir::Type::Array(inner_ty, length) = array_ty.clone() else {
                    unreachable!()
                };

                assert_eq!(length, values.len());

                let array_ptr_reg = self
                    .destination_register
                    .unwrap_or_else(|| self.emit_alloc_stack(array_ty));

                for (i, e) in values.iter().enumerate() {
                    let element_ptr_reg = self.emit_get_array_elem_ptr(
                        lir::Operand::Register(array_ptr_reg),
                        inner_ty.as_ref().clone(),
                        lir::Operand::Immediate(lir::Immediate::Int(
                            i as _,
                            lir::IntegerWidth::I64,
                        )),
                    );

                    self.with_dest_and_expr_ctx(
                        inner_ty.is_aggregate().then_some(element_ptr_reg),
                        ExpressionContext::Value,
                        |this| this.visit_expression(e.clone()),
                    );

                    // for scalar types, add a store into the memory we
                    // allocated for the array element (aggregate types are
                    // already initialized in place here)

                    let init_value = self.expression_to_operand_map[&e.hir_id.local_id];

                    if inner_ty.is_scalar() {
                        self.emit_store_mem(
                            lir::Operand::Register(element_ptr_reg),
                            init_value,
                            inner_ty.as_ref().clone(),
                        );
                    } else {
                        debug_assert_eq!(
                            init_value,
                            lir::Operand::Register(element_ptr_reg),
                            "array element initializer destination was not respected for expr: {e:#?}"
                        );
                    }
                }

                self.expression_to_operand_map.insert(
                    expression.hir_id.local_id,
                    lir::Operand::Register(array_ptr_reg),
                );
            }
            hir::ExpressionKind::Tuple(expressions) => {
                let ty = self.type_map.get_type(expression.hir_id);
                let lir_ty = self.lower_type(ty);

                let struct_ty = lir_ty.as_struct().unwrap();

                /* Create a temporary if a destination was not already allocated */

                let struct_ptr_reg = self
                    .destination_register
                    .unwrap_or_else(|| self.emit_alloc_stack(lir_ty.clone()));

                /* Set each field */

                for (i, e) in expressions.iter().enumerate() {
                    self.push_comment(format!("field {i}"));

                    // get field address

                    let element_ptr_reg = self.emit_get_struct_elem_ptr(
                        lir::Operand::Register(struct_ptr_reg),
                        struct_ty.clone(),
                        i,
                    );

                    // compute field value

                    let elem_ty = self.type_map.get_type(e.hir_id);
                    let elem_ty = self.lower_type(elem_ty);

                    self.with_dest_and_expr_ctx(
                        elem_ty.is_aggregate().then_some(element_ptr_reg),
                        ExpressionContext::Value,
                        |this| this.visit_expression(e.clone()),
                    );

                    // store field value (if we didnt pass it to the expression)

                    // for scalar types, add a store into the memory we
                    // allocated for the array element (aggregate types are
                    // already initialized in place here)

                    let init_value = self.expression_to_operand_map[&e.hir_id.local_id];

                    if elem_ty.is_scalar() {
                        self.emit_store_mem(
                            lir::Operand::Register(element_ptr_reg),
                            init_value,
                            elem_ty.clone(),
                        );
                    } else {
                        debug_assert_eq!(
                            init_value,
                            lir::Operand::Register(element_ptr_reg),
                            "tuple element initializer destination was not respected for expr at index {i}: {e:#?}"
                        );
                    }
                }

                self.expression_to_operand_map.insert(
                    expression.hir_id.local_id,
                    lir::Operand::Register(struct_ptr_reg),
                );
            }
            hir::ExpressionKind::Struct { name: _, fields } => {
                let ty = self.type_map.get_type(expression.hir_id);
                let lir_ty = self.lower_type(ty);

                let struct_ty = lir_ty.as_struct().unwrap();

                /* Create a temporary if a destination was not already allocated */

                let struct_ptr_reg = self
                    .destination_register
                    .unwrap_or_else(|| self.emit_alloc_stack(lir_ty.clone()));

                /* Set each field */

                for (i, f) in fields.iter().enumerate() {
                    self.push_comment(format!("field {i} ({})", f.name.symbol));

                    // get field address

                    let element_ptr_reg = self.emit_get_struct_elem_ptr(
                        lir::Operand::Register(struct_ptr_reg),
                        struct_ty.clone(),
                        i,
                    );

                    // compute field value

                    let elem_ty = self.type_map.get_type(f.value.hir_id);
                    let elem_ty = self.lower_type(elem_ty);

                    self.with_dest_and_expr_ctx(
                        elem_ty.is_aggregate().then_some(element_ptr_reg),
                        ExpressionContext::Value,
                        |this| this.visit_expression(f.value.clone()),
                    );

                    // store field value (if we didnt pass it to the expression)

                    // for scalar types, add a store into the memory we
                    // allocated for the array element (aggregate types are
                    // already initialized in place here)

                    let init_value = self.expression_to_operand_map[&f.value.hir_id.local_id];

                    if elem_ty.is_scalar() {
                        self.emit_store_mem(
                            lir::Operand::Register(element_ptr_reg),
                            init_value,
                            elem_ty.clone(),
                        );
                    } else {
                        debug_assert_eq!(
                            init_value,
                            lir::Operand::Register(element_ptr_reg),
                            "tuple element initializer destination was not respected for expr at index {i}: {:#?}",
                            f.value
                        );
                    }
                }

                self.expression_to_operand_map.insert(
                    expression.hir_id.local_id,
                    lir::Operand::Register(struct_ptr_reg),
                );
            }
            hir::ExpressionKind::Block(block) => {
                self.with_expression_context(ExpressionContext::Value, |this| {
                    hir::visit::walk_expression(this, expression.clone())
                });

                if let Some(value) = self.expression_to_operand_map.get(&block.hir_id.local_id) {
                    self.expression_to_operand_map
                        .insert(expression.hir_id.local_id, *value);
                }
            }
            hir::ExpressionKind::FieldAccess {
                target,
                name,
                dereference,
                is_method_call,
            } => {
                // target should evaluate to a location in memory where we can
                // read the value of the field from (ptr)

                self.with_dest_and_expr_ctx(None, ExpressionContext::Place, |this| {
                    this.visit_expression(target.clone())
                });

                // method calls are handled in the function call visitor. theres
                // nothing we need to do here.
                if *is_method_call {
                    return;
                }

                let target_value = self.expression_to_operand_map[&target.hir_id.local_id];

                // target type is either be a struct or struct-like type (str,
                // slice, tuple, etc). The operand associated with this
                // expression stores a pointer to the structure and we need to
                // emit instructions for getting the pointer to the field and
                // optionally loading the value from memory if we are in a value
                // context

                let mut target_ty = self.type_map.get_type(target.hir_id);

                if let ty::TypeKind::Pointer(inner_ty) = &*target_ty {
                    assert!(*dereference);

                    target_ty = inner_ty.clone();
                }

                let (structure_ty, field_index, field_ty) = match &*target_ty {
                    ty::TypeKind::Str | ty::TypeKind::Slice(_) => {
                        let structure_ty = lir::Struct::slice();

                        let (field_index, field_ty) = match name.symbol.value() {
                            "ptr" => (0, lir::Type::Pointer),
                            "len" => (1, lir::Type::Integer(lir::IntegerWidth::I64)),
                            _ => unreachable!(),
                        };

                        (structure_ty, field_index, field_ty)
                    }
                    ty::TypeKind::Tuple(items) => {
                        let field_index = name
                            .symbol
                            .value()
                            .strip_prefix("v")
                            .unwrap()
                            .parse::<usize>()
                            .unwrap();

                        let lir::Type::Struct(structure_ty) = self.lower_type(target_ty) else {
                            unreachable!();
                        };
                        let field_ty = structure_ty.0[field_index].clone();

                        (structure_ty, field_index, field_ty)
                    }
                    ty::TypeKind::Struct {
                        def_id: _,
                        name: _,
                        fields,
                    } => {
                        let mut field_index_map = BTreeMap::new();
                        let field_tys = fields
                            .iter()
                            .enumerate()
                            .map(|(i, f)| {
                                field_index_map.insert(f.name, i);
                                self.lower_type(f.ty.clone())
                            })
                            .collect::<Rc<[_]>>();

                        let structure_ty = lir::Struct(field_tys.clone());

                        let (field_index, field_ty) = {
                            let idx = field_index_map[&name.symbol];

                            (idx, field_tys[idx].clone())
                        };

                        (structure_ty, field_index, field_ty)
                    }
                    _ => unreachable!(),
                };

                // let struct_ptr = if *dereference {
                //     lir::Operand::Register(self.emit_load_mem(target_value, lir::Type::Pointer))
                // } else {
                //     target_value
                // };

                let field_ptr_reg =
                    self.emit_get_struct_elem_ptr(target_value, structure_ty, field_index);

                let output_reg = match self.expression_context {
                    ExpressionContext::Value => self.emit_load_from_ptr(
                        self.destination_register,
                        lir::Operand::Register(field_ptr_reg),
                        field_ty,
                    ),
                    ExpressionContext::Place => field_ptr_reg,
                };

                self.expression_to_operand_map.insert(
                    expression.hir_id.local_id,
                    lir::Operand::Register(output_reg),
                );
            }
            hir::ExpressionKind::FunctionCall { target, arguments } => {
                self.with_dest_and_expr_ctx(None, ExpressionContext::Value, |this| {
                    this.visit_expression(target.clone())
                });

                match &target.kind {
                    hir::ExpressionKind::Path(path) => {
                        match path.resolution() {
                            hir::Resolution::Definition(
                                hir::DefinitionKind::Function
                                | hir::DefinitionKind::AssociatedFunction,
                                def_id,
                            ) => {
                                let hir::ItemKind::Function {
                                    name, signature, ..
                                } = &self
                                    .module
                                    .get_owner(*def_id)
                                    .unwrap()
                                    .node()
                                    .as_item()
                                    .unwrap()
                                    .kind
                                else {
                                    unreachable!()
                                };

                                let symbol = self.module.global_symbol_for(name);
                                let return_ty = signature
                                    .return_type
                                    .as_ref()
                                    .map(|ty| self.type_map.get_type(ty.hir_id));

                                let value_reg = self.lower_function_call(
                                    symbol,
                                    None,
                                    arguments.iter().cloned(),
                                    return_ty,
                                );

                                if let Some(value) = value_reg {
                                    self.expression_to_operand_map.insert(
                                        expression.hir_id.local_id,
                                        lir::Operand::Register(value),
                                    );
                                }
                            }
                            hir::Resolution::Definition(def_kind, ..) => {
                                unreachable!(
                                    "other definition kinds may not be function call targets: {def_kind:?}"
                                )
                            }
                            hir::Resolution::Local(_) => todo!(
                                "locals as function pointers (stack slot stores the pointer to the function)"
                            ),
                            hir::Resolution::IntrinsicFunction(name) if name.value() == "print" => {
                                /* Parse strings and deconstruct into multiple function calls */

                                let format_string =
                                    arguments[0].kind.expect_literal().expect_string().value();

                                let parts = parse_format_string(format_string);

                                let format_arguments_count = parts
                                    .iter()
                                    .filter(|p| matches!(p, FormatStringItem::Argument(_)))
                                    .count();

                                assert_eq!(
                                    arguments.len() - 1,
                                    format_arguments_count,
                                    "wrong number of format arguments passed to print"
                                );

                                if format_arguments_count == 0 {
                                    for arg in arguments.iter() {
                                        self.with_dest_and_expr_ctx(
                                            None,
                                            ExpressionContext::Value,
                                            |this| this.visit_expression(arg.clone()),
                                        );
                                    }

                                    let str_ptr = self.expression_to_operand_map
                                        [&arguments[0].hir_id.local_id];

                                    let dest_reg = self.print_string(str_ptr);

                                    // FIXME: should this function care about the return value?
                                    self.expression_to_operand_map.insert(
                                        expression.hir_id.local_id,
                                        lir::Operand::Register(dest_reg),
                                    );

                                    return;
                                }

                                for arg in arguments.iter().skip(1) {
                                    self.with_dest_and_expr_ctx(
                                        None,
                                        ExpressionContext::Value,
                                        |this| this.visit_expression(arg.clone()),
                                    );
                                }

                                for part in parts {
                                    match part {
                                        FormatStringItem::String(symbol) => {
                                            let str_ptr_reg =
                                                self.lower_constant_string(symbol, None);

                                            let dest_reg = self
                                                .print_string(lir::Operand::Register(str_ptr_reg));

                                            // FIXME: should this function care about the return value?
                                            self.expression_to_operand_map.insert(
                                                expression.hir_id.local_id,
                                                lir::Operand::Register(dest_reg),
                                            );
                                        }
                                        FormatStringItem::Argument(index) => {
                                            let arg = &arguments[index + 1];
                                            let arg_value = self.expression_to_operand_map
                                                [&arg.hir_id.local_id];
                                            let ty = self.type_map.get_type(arg.hir_id);

                                            match &*ty {
                                                ty::TypeKind::Integer(int_kind) => {
                                                    let width: lir::IntegerWidth =
                                                        (*int_kind).into();

                                                    let fn_name = match width {
                                                        lir::IntegerWidth::I8 => "__$print_i8",
                                                        lir::IntegerWidth::I16 => "__$print_i16",
                                                        lir::IntegerWidth::I32 => "__$print_i32",
                                                        lir::IntegerWidth::I64 => "__$print_i64",
                                                    };

                                                    let dest_reg = self.emit_function_call(
                                                        lir::Operand::Immediate(
                                                            lir::Immediate::FunctionLabel(
                                                                InternedSymbol::new(fn_name),
                                                            ),
                                                        ),
                                                        vec![arg_value],
                                                        Some(lir::Type::Integer(
                                                            lir::IntegerWidth::I64,
                                                        )),
                                                    );

                                                    self.expression_to_operand_map.insert(
                                                        expression.hir_id.local_id,
                                                        lir::Operand::Register(dest_reg.unwrap()),
                                                    );
                                                }
                                                ty::TypeKind::UnsignedInteger(uint_kind) => {
                                                    let width: lir::IntegerWidth =
                                                        (*uint_kind).into();

                                                    let fn_name = match width {
                                                        lir::IntegerWidth::I8 => "__$print_u8",
                                                        lir::IntegerWidth::I16 => "__$print_u16",
                                                        lir::IntegerWidth::I32 => "__$print_u32",
                                                        lir::IntegerWidth::I64 => "__$print_u64",
                                                    };

                                                    let dest_reg = self.emit_function_call(
                                                        lir::Operand::Immediate(
                                                            lir::Immediate::FunctionLabel(
                                                                InternedSymbol::new(fn_name),
                                                            ),
                                                        ),
                                                        vec![arg_value],
                                                        Some(lir::Type::Integer(
                                                            lir::IntegerWidth::I64,
                                                        )),
                                                    );

                                                    self.expression_to_operand_map.insert(
                                                        expression.hir_id.local_id,
                                                        lir::Operand::Register(dest_reg.unwrap()),
                                                    );
                                                }
                                                ty::TypeKind::Pointer(_) => {
                                                    let dest_reg = self.emit_function_call(
                                                        lir::Operand::Immediate(
                                                            lir::Immediate::FunctionLabel(
                                                                InternedSymbol::new(
                                                                    "__$print_i64_hex",
                                                                ),
                                                            ),
                                                        ),
                                                        vec![arg_value],
                                                        Some(lir::Type::Integer(
                                                            lir::IntegerWidth::I64,
                                                        )),
                                                    );

                                                    self.expression_to_operand_map.insert(
                                                        expression.hir_id.local_id,
                                                        lir::Operand::Register(dest_reg.unwrap()),
                                                    );
                                                }
                                                ty::TypeKind::Enum { name, def_id } => {
                                                    // let str_ptr_reg =
                                                    //     self.lower_constant_string(*name, None);

                                                    // let dest_reg = self.print_string(
                                                    //     lir::Operand::Register(str_ptr_reg),
                                                    // );

                                                    let dest_reg = self.emit_function_call(
                                                        lir::Operand::Immediate(
                                                            lir::Immediate::FunctionLabel(
                                                                InternedSymbol::new("__$print_i32"),
                                                            ),
                                                        ),
                                                        vec![arg_value],
                                                        Some(lir::Type::Integer(
                                                            lir::IntegerWidth::I64,
                                                        )),
                                                    );

                                                    // FIXME: should this function care about the return value?
                                                    self.expression_to_operand_map.insert(
                                                        expression.hir_id.local_id,
                                                        lir::Operand::Register(dest_reg.unwrap()),
                                                    );
                                                }
                                                &ty::TypeKind::Str => {
                                                    let dest_reg = self.print_string(arg_value);

                                                    self.expression_to_operand_map.insert(
                                                        expression.hir_id.local_id,
                                                        lir::Operand::Register(dest_reg),
                                                    );
                                                }
                                                ty_kind => todo!("print type {ty_kind}"),
                                            }
                                        }
                                    }
                                }
                            }
                            hir::Resolution::IntrinsicFunction(name) if name.value() == "str" => {
                                self.with_dest_and_expr_ctx(
                                    None,
                                    ExpressionContext::Value,
                                    |this| {
                                        this.visit_expression(arguments[0].clone());
                                        this.visit_expression(arguments[1].clone());
                                    },
                                );

                                let ptr =
                                    self.expression_to_operand_map[&arguments[0].hir_id.local_id];
                                let len =
                                    self.expression_to_operand_map[&arguments[1].hir_id.local_id];

                                let dest_reg = self.destination_register.unwrap_or_else(|| {
                                    self.emit_alloc_stack(lir::Type::Struct(lir::Struct::slice()))
                                });

                                let ptr_ptr_reg = self.emit_get_struct_elem_ptr(
                                    lir::Operand::Register(dest_reg),
                                    lir::Struct::slice(),
                                    0,
                                );
                                self.emit_store_mem(
                                    lir::Operand::Register(ptr_ptr_reg),
                                    ptr,
                                    lir::Type::Pointer,
                                );

                                let let_ptr_reg = self.emit_get_struct_elem_ptr(
                                    lir::Operand::Register(dest_reg),
                                    lir::Struct::slice(),
                                    1,
                                );
                                self.emit_store_mem(
                                    lir::Operand::Register(let_ptr_reg),
                                    len,
                                    lir::Type::Integer(lir::IntegerWidth::I64),
                                );

                                self.expression_to_operand_map.insert(
                                    expression.hir_id.local_id,
                                    lir::Operand::Register(dest_reg),
                                );
                            }
                            hir::Resolution::IntrinsicFunction(name) if name.value() == "exit" => {
                                self.with_dest_and_expr_ctx(
                                    None,
                                    ExpressionContext::Value,
                                    |this| this.visit_expression(arguments[0].clone()),
                                );

                                let arg =
                                    self.expression_to_operand_map[&arguments[0].hir_id.local_id];

                                self.emit_function_call(
                                    lir::Operand::Immediate(lir::Immediate::FunctionLabel(
                                        InternedSymbol::new("__$exit"),
                                    )),
                                    vec![arg],
                                    None,
                                );
                            }
                            hir::Resolution::IntrinsicFunction(name) if name.value() == "read" => {
                                for arg in arguments.iter() {
                                    self.with_dest_and_expr_ctx(
                                        None,
                                        ExpressionContext::Value,
                                        |this| this.visit_expression(arg.clone()),
                                    );
                                }

                                let mut argument_operands = vec![lir::Operand::Immediate(
                                    lir::Immediate::Int(0, lir::IntegerWidth::I64),
                                )];

                                for arg in arguments.iter() {
                                    argument_operands
                                        .push(self.expression_to_operand_map[&arg.hir_id.local_id]);
                                }

                                let dest_reg = self.emit_function_call(
                                    lir::Operand::Immediate(lir::Immediate::FunctionLabel(
                                        InternedSymbol::new("__$syscall_3"),
                                    )),
                                    argument_operands,
                                    Some(lir::Type::Integer(lir::IntegerWidth::I64)),
                                );

                                self.expression_to_operand_map.insert(
                                    expression.hir_id.local_id,
                                    lir::Operand::Register(dest_reg.unwrap()),
                                );
                            }
                            hir::Resolution::IntrinsicFunction(name) if name.value() == "open" => {
                                let mut args = Vec::with_capacity(arguments.len());

                                for arg in arguments.iter() {
                                    self.with_dest_and_expr_ctx(
                                        None,
                                        ExpressionContext::Value,
                                        |this| this.visit_expression(arg.clone()),
                                    );

                                    let value =
                                        self.expression_to_operand_map[&arg.hir_id.local_id];

                                    args.push(value);
                                }

                                let mut argument_operands = vec![lir::Operand::Immediate(
                                    lir::Immediate::Int(2, lir::IntegerWidth::I64),
                                )];

                                let ptr_ptr_reg =
                                    self.emit_get_struct_elem_ptr(args[0], lir::Struct::slice(), 0);

                                let ptr_reg = self.emit_load_mem(
                                    lir::Operand::Register(ptr_ptr_reg),
                                    lir::Type::Pointer,
                                );

                                argument_operands.push(lir::Operand::Register(ptr_reg)); // ptr
                                argument_operands.push(args[1]); // flags
                                argument_operands.push(args[2]); // mode

                                let dest_reg = self.emit_function_call(
                                    lir::Operand::Immediate(lir::Immediate::FunctionLabel(
                                        InternedSymbol::new("__$syscall_3"),
                                    )),
                                    argument_operands,
                                    Some(lir::Type::Integer(lir::IntegerWidth::I64)),
                                );

                                self.expression_to_operand_map.insert(
                                    expression.hir_id.local_id,
                                    lir::Operand::Register(dest_reg.unwrap()),
                                );
                            }
                            hir::Resolution::IntrinsicFunction(name) if name.value() == "close" => {
                                for arg in arguments.iter() {
                                    self.with_dest_and_expr_ctx(
                                        None,
                                        ExpressionContext::Value,
                                        |this| this.visit_expression(arg.clone()),
                                    );
                                }

                                let mut argument_operands = vec![lir::Operand::Immediate(
                                    lir::Immediate::Int(3, lir::IntegerWidth::I64),
                                )];

                                for arg in arguments.iter() {
                                    argument_operands
                                        .push(self.expression_to_operand_map[&arg.hir_id.local_id]);
                                }

                                let dest_reg = self.emit_function_call(
                                    lir::Operand::Immediate(lir::Immediate::FunctionLabel(
                                        InternedSymbol::new("__$syscall_1"),
                                    )),
                                    argument_operands,
                                    Some(lir::Type::Integer(lir::IntegerWidth::I64)),
                                );

                                self.expression_to_operand_map.insert(
                                    expression.hir_id.local_id,
                                    lir::Operand::Register(dest_reg.unwrap()),
                                );
                            }
                            hir::Resolution::IntrinsicFunction(name) => {
                                todo!("lower intrinsic function: {}", name.value())
                            }
                            hir::Resolution::Primitive(_) => {
                                unreachable!("primitives may not be used as function call targets")
                            }
                        }
                    }
                    hir::ExpressionKind::FieldAccess {
                        target: self_target,
                        name: _,
                        dereference,
                        is_method_call: true,
                    } => {
                        // assert!(!*dereference);

                        let method_def_id = self.type_map.function_results[&self.owner_id]
                            .method_resolutions[&target.hir_id.local_id];

                        let hir::ItemKind::Function {
                            name, signature, ..
                        } = &self
                            .module
                            .get_owner(method_def_id)
                            .unwrap()
                            .node()
                            .as_item()
                            .unwrap()
                            .kind
                        else {
                            unreachable!()
                        };

                        let symbol = self.module.global_symbol_for(name);
                        let return_ty = signature
                            .return_type
                            .as_ref()
                            .map(|ty| self.type_map.get_type(ty.hir_id));

                        let value_reg = self.lower_function_call(
                            symbol,
                            Some((signature.self_parameter.unwrap(), self_target.clone())),
                            arguments.iter().cloned(),
                            return_ty,
                        );

                        if let Some(value) = value_reg {
                            self.expression_to_operand_map
                                .insert(expression.hir_id.local_id, lir::Operand::Register(value));
                        }
                    }
                    _ => todo!("lower function pointer calls"),
                }
            }
            hir::ExpressionKind::Subscript { target, index } => {
                self.with_dest_and_expr_ctx(None, ExpressionContext::Place, |this| {
                    this.visit_expression(target.clone())
                });
                self.with_dest_and_expr_ctx(None, ExpressionContext::Value, |this| {
                    this.visit_expression(index.clone())
                });

                let target_ty = self.type_map.get_type(target.hir_id);

                let target_value = self.expression_to_operand_map[&target.hir_id.local_id];
                let index_value = self.expression_to_operand_map[&index.hir_id.local_id];

                let dest_reg = match &*target_ty {
                    ty::TypeKind::Str => {
                        let ptr_ptr_reg =
                            self.emit_get_struct_elem_ptr(target_value, lir::Struct::slice(), 0);
                        let ptr_reg = self
                            .emit_load_mem(lir::Operand::Register(ptr_ptr_reg), lir::Type::Pointer);

                        let elem_ptr_reg = self.emit_get_array_elem_ptr(
                            lir::Operand::Register(ptr_reg),
                            lir::Type::Integer(lir::IntegerWidth::I8),
                            index_value,
                        );

                        match self.expression_context {
                            ExpressionContext::Place => elem_ptr_reg,
                            ExpressionContext::Value => {
                                let byte = self.emit_load_mem(
                                    lir::Operand::Register(elem_ptr_reg),
                                    lir::Type::Integer(lir::IntegerWidth::I8),
                                );

                                self.emit_integer_cast(
                                    lir::IntegerCastKind::ZeroExtension,
                                    lir::Operand::Register(byte),
                                    lir::Type::Integer(lir::IntegerWidth::I32),
                                )
                            }
                        }
                    }
                    ty::TypeKind::CStr => todo!(),
                    ty::TypeKind::Pointer(ty) => todo!(),
                    ty::TypeKind::Slice(ty) => todo!(),
                    ty::TypeKind::Array { ty, length } => {
                        let ty = self.lower_type(ty.clone());

                        let elem_ptr_reg =
                            self.emit_get_array_elem_ptr(target_value, ty.clone(), index_value);

                        match self.expression_context {
                            ExpressionContext::Place => elem_ptr_reg,
                            ExpressionContext::Value => self.emit_load_from_ptr(
                                self.destination_register,
                                lir::Operand::Register(elem_ptr_reg),
                                ty,
                            ),
                        }
                    }
                    ty::TypeKind::Tuple(items) => todo!(),
                    _ => unreachable!(),
                };

                self.expression_to_operand_map
                    .insert(expression.hir_id.local_id, lir::Operand::Register(dest_reg));
            }
            hir::ExpressionKind::Binary { lhs, operator, rhs } => {
                let output_ty = self.type_map.get_type(expression.hir_id);

                let dest_reg = self.lower_binary_op(output_ty, *operator, lhs.clone(), rhs.clone());

                self.expression_to_operand_map
                    .insert(expression.hir_id.local_id, lir::Operand::Register(dest_reg));
            }
            hir::ExpressionKind::Unary { operator, operand } => {
                match *operator {
                    // the deref operator has different meanings based on the
                    // current context
                    UnaryOperatorKind::Deref => {
                        self.with_dest_and_expr_ctx(None, ExpressionContext::Value, |this| {
                            this.visit_expression(operand.clone())
                        });

                        let ptr = self.expression_to_operand_map[&operand.hir_id.local_id];

                        let dest = match self.expression_context {
                            // return the pointer r-value as an l-value (maps
                            // between contexts)
                            ExpressionContext::Place => ptr,
                            // perform a memory load of the pointer
                            ExpressionContext::Value => {
                                let ty = self.type_map.get_type(expression.hir_id);
                                let ty = self.lower_type(ty);

                                lir::Operand::Register(self.emit_load_from_ptr(
                                    self.destination_register,
                                    ptr,
                                    ty,
                                ))
                            }
                        };

                        self.expression_to_operand_map
                            .insert(expression.hir_id.local_id, dest);
                    }
                    // return the pointer l-value as an r-value (maps between
                    // contexts)
                    UnaryOperatorKind::AddressOf { is_mutable } => {
                        assert_eq!(
                            self.expression_context,
                            ExpressionContext::Value,
                            "address-of operator should only be evaluated in a value expression context"
                        );

                        // FIXME: keep track of all the registers whose
                        // addresses we've taken the address of so that we can
                        // know which registers must be spilled and which ones
                        // can be promoted to registers

                        // FIXME: coerce array address-of operations into slice
                        // creation if the current value context expects one (we
                        // need to keep track of type coercions during type
                        // checking to look for them here)

                        self.with_dest_and_expr_ctx(None, ExpressionContext::Place, |this| {
                            this.visit_expression(operand.clone())
                        });

                        let dest = self.expression_to_operand_map[&operand.hir_id.local_id];

                        self.expression_to_operand_map
                            .insert(expression.hir_id.local_id, dest);
                    }
                    // remaining unary operators are just trivial r-value ->
                    // r-value transformations
                    operator @ (UnaryOperatorKind::LogicalNot
                    | UnaryOperatorKind::BitwiseNot
                    | UnaryOperatorKind::Negate) => {
                        self.with_dest_and_expr_ctx(None, ExpressionContext::Value, |this| {
                            this.visit_expression(operand.clone())
                        });

                        let ty = self.type_map.get_type(expression.hir_id);
                        let ty = self.lower_type(ty);

                        let operand = self.expression_to_operand_map[&operand.hir_id.local_id];
                        let dest_reg = self.emit_unary(operator.try_into().unwrap(), operand, ty);

                        self.expression_to_operand_map
                            .insert(expression.hir_id.local_id, lir::Operand::Register(dest_reg));
                    }
                }
            }
            hir::ExpressionKind::Cast {
                expression: castee,
                ty: dest_ty,
            } => {
                self.with_dest_and_expr_ctx(None, ExpressionContext::Value, |this| {
                    hir::visit::walk_expression(this, expression.clone())
                });

                let src_ty = self.type_map.get_type(castee.hir_id);
                let dest_ty = self.type_map.get_type(dest_ty.hir_id);

                let lir_ty = self.lower_type(dest_ty.clone());

                let castee = self.expression_to_operand_map[&castee.hir_id.local_id];

                // trivial cast, just copy
                if src_ty == dest_ty
                    || (*src_ty == ty::TypeKind::UnsignedInteger(UIntKind::USize)
                        && dest_ty.is_pointer_like())
                    || (src_ty.is_pointer_like() && dest_ty.is_pointer_like())
                    || (*src_ty == ty::TypeKind::Char
                        && *dest_ty == ty::TypeKind::UnsignedInteger(UIntKind::U32))
                {
                    let dest = self.lower_copy(self.destination_register, castee, lir_ty);

                    self.expression_to_operand_map
                        .insert(expression.hir_id.local_id, dest);

                    return;
                }

                // only integers and pointers can be casted

                let kind = match (&*src_ty, &*dest_ty) {
                    // all combinations of smaller dest than src
                    (ty::TypeKind::UnsignedInteger(src), ty::TypeKind::UnsignedInteger(dest))
                        if lir::IntegerWidth::from(*src) >= lir::IntegerWidth::from(*dest) =>
                    {
                        lir::IntegerCastKind::Truncate
                    }
                    (ty::TypeKind::UnsignedInteger(src), ty::TypeKind::Integer(dest))
                        if lir::IntegerWidth::from(*src) >= lir::IntegerWidth::from(*dest) =>
                    {
                        lir::IntegerCastKind::Truncate
                    }
                    (ty::TypeKind::Integer(src), ty::TypeKind::UnsignedInteger(dest))
                        if lir::IntegerWidth::from(*src) >= lir::IntegerWidth::from(*dest) =>
                    {
                        lir::IntegerCastKind::Truncate
                    }
                    (ty::TypeKind::Integer(src), ty::TypeKind::Integer(dest))
                        if lir::IntegerWidth::from(*src) >= lir::IntegerWidth::from(*dest) =>
                    {
                        lir::IntegerCastKind::Truncate
                    }

                    // all combinations of larger dest than src
                    (
                        ty::TypeKind::UnsignedInteger(_),
                        ty::TypeKind::UnsignedInteger(_) | ty::TypeKind::Integer(_),
                    ) => lir::IntegerCastKind::ZeroExtension,
                    (
                        ty::TypeKind::Integer(_),
                        ty::TypeKind::UnsignedInteger(_) | ty::TypeKind::Integer(_),
                    ) => lir::IntegerCastKind::SignExtension,

                    (src, dest) => unreachable!("src = {src:?}, dest = {dest:?}"),
                };

                let dest_reg = self.emit_integer_cast(kind, castee, lir_ty);

                self.expression_to_operand_map
                    .insert(expression.hir_id.local_id, lir::Operand::Register(dest_reg));
            }
            hir::ExpressionKind::If {
                condition,
                positive,
                negative,
            } => {
                self.with_dest_and_expr_ctx(None, ExpressionContext::Value, |this| {
                    this.visit_expression(condition.clone())
                });
                let condition = self.expression_to_operand_map[&condition.hir_id.local_id];

                let ty = self.type_map.get_type(expression.hir_id);

                // If the implicit return value of the conditional expression is
                // an aggregate type, we thread the target destination through
                // the context for it to be constructed in-place instead of
                // creating phi nodes in the merge block
                let aggregate_dest_reg = ty.is_aggregate().then(|| {
                    let lir_ty = self.lower_type(ty.clone());

                    self.destination_register
                        .unwrap_or_else(|| self.emit_alloc_stack(lir_ty))
                });

                let mut phi_map =
                    (!ty.is_aggregate() && !ty.is_unit() && !ty.is_never()).then(BTreeMap::new);

                // For if expressions, there are 2 possible cases. In the first
                // case where there is no else, we allocate a new block for the
                // positive branch and a new block to act as both the negative
                // fallthrough and the merge point. In the second case where
                // there is an else, we allocate a new block for the positive
                // branch, a new block for the negative branch, and a new block
                // for the merge point.

                let starting_block_id = *self.block_stack.back().unwrap();

                let positive_block_id = self.create_block();
                self.block_map[positive_block_id]
                    .predecessors
                    .insert(starting_block_id);

                let positive_branch_last_block: lir::BlockId;
                {
                    self.block_stack.push_back(positive_block_id);
                    self.with_dest_and_expr_ctx(
                        aggregate_dest_reg,
                        ExpressionContext::Value,
                        |this| this.visit_block(positive.clone(), hir::visit::BlockContext::Scope),
                    );
                    self.block_stack.pop_back();

                    // the most recently created block is the block we need to
                    // insert the merge jump into. if no blocks were created
                    // while visiting the subexpression, its still the current
                    // block.
                    positive_branch_last_block = lir::BlockId::new(self.block_map.len() - 1);
                }

                let mut merge_block_id = self.create_block();
                let negative_block_id = if let Some(n) = &negative {
                    // allocate a negative branch block before the merge branch
                    let negative_branch_block_id = merge_block_id;

                    self.block_map[negative_branch_block_id]
                        .predecessors
                        .insert(starting_block_id);

                    self.block_stack.push_back(negative_branch_block_id);
                    self.with_dest_and_expr_ctx(
                        aggregate_dest_reg,
                        ExpressionContext::Value,
                        |this| this.visit_expression(n.clone()),
                    );
                    self.block_stack.pop_back();

                    merge_block_id = self.create_block();

                    if !self.type_map.get_type(n.hir_id).is_never() {
                        let negative_branch_last_block =
                            lir::BlockId::new(self.block_map.len() - 2);

                        // insert unconditional jump in the negative branch to the
                        // allocated merge block if the branch does not return
                        if !self.block_map[negative_branch_last_block].returns() {
                            self.block_map[negative_branch_last_block]
                                .instructions
                                .push(lir::Instruction::Jump {
                                    destination: merge_block_id,
                                });
                            self.block_map[merge_block_id]
                                .predecessors
                                .insert(negative_branch_last_block);

                            if let Some(ref mut map) = phi_map {
                                let value = self.expression_to_operand_map[&n.hir_id.local_id];
                                map.insert(negative_branch_last_block, value);
                            }
                        }
                    }

                    negative_branch_block_id
                } else {
                    // in this case the negative fallthrough is the same as the
                    // merge block id

                    self.block_map[merge_block_id]
                        .predecessors
                        .insert(starting_block_id);

                    merge_block_id
                };

                // insert unconditional jump in the positive branch to the
                // allocated merge block if the branch does not return
                if !self.block_map[positive_branch_last_block].returns() {
                    self.block_map[positive_branch_last_block]
                        .instructions
                        .push(lir::Instruction::Jump {
                            destination: merge_block_id,
                        });
                    self.block_map[merge_block_id]
                        .predecessors
                        .insert(positive_branch_last_block);

                    if let Some(ref mut map) = phi_map {
                        let value = self.expression_to_operand_map[&positive.hir_id.local_id];
                        map.insert(positive_branch_last_block, value);
                    }
                }

                self.block_map[starting_block_id]
                    .instructions
                    .push(lir::Instruction::Branch {
                        condition: condition,
                        positive: positive_block_id,
                        negative: negative_block_id,
                    });

                self.block_stack.pop_back();
                self.block_stack.push_back(merge_block_id);

                let phi_reg = phi_map.map(|map| {
                    let lir_ty = self.lower_type(ty.clone());

                    self.emit_phi(map, lir_ty)
                });

                if let Some(reg) = aggregate_dest_reg.or(phi_reg) {
                    self.expression_to_operand_map
                        .insert(expression.hir_id.local_id, lir::Operand::Register(reg));
                }
            }
            hir::ExpressionKind::While { condition, block } => {
                // .while_condition:
                //     %0 = %i < %n
                //     br %0 .while_body .while_end
                // .while_body:
                //     jmp .while_condition
                // .while_end:

                let current_block_id = *self.block_stack.back().unwrap();

                let condition_block_id = self.create_block();
                self.block_map[condition_block_id]
                    .predecessors
                    .insert(current_block_id);

                self.loop_ctx_stack.push(LoopContext {
                    start_block: condition_block_id,
                    break_instructions: Vec::new(),
                });

                self.block_stack.push_back(condition_block_id);
                self.with_dest_and_expr_ctx(None, ExpressionContext::Value, |this| {
                    this.visit_expression(condition.clone())
                });
                self.block_stack.pop_back();

                let last_inserted_condition_block = lir::BlockId::new(self.block_map.len() - 1);

                // Loop Body

                let body_block_id = self.create_block();

                self.block_stack.push_back(body_block_id);
                self.with_dest_and_expr_ctx(None, ExpressionContext::Value, |this| {
                    this.visit_block(block.clone(), hir::visit::BlockContext::Loop)
                });
                self.block_stack.pop_back();

                // At the end of the body, insert an unconditional jump back to
                // the condition checking block

                let last_inserted_body_block = lir::BlockId::new(self.block_map.len() - 1);

                self.block_map[last_inserted_body_block].instructions.push(
                    lir::Instruction::Jump {
                        destination: condition_block_id,
                    },
                );
                self.block_map[condition_block_id]
                    .predecessors
                    .insert(last_inserted_body_block);

                // The end block is reached once the loop breaks or the
                // condition returns false

                let end_block_id = self.create_block();

                // Conditional branch to decide if we continue the loop

                let condition_value = self.expression_to_operand_map[&condition.hir_id.local_id];
                self.block_map[last_inserted_condition_block]
                    .instructions
                    .push(lir::Instruction::Branch {
                        condition: condition_value,
                        positive: body_block_id,
                        negative: end_block_id,
                    });
                self.block_map[body_block_id]
                    .predecessors
                    .insert(last_inserted_condition_block);
                self.block_map[end_block_id]
                    .predecessors
                    .insert(last_inserted_condition_block);

                // Patch break expressions within the loop body

                let ctx = self.loop_ctx_stack.pop().unwrap();

                for (block_id, idx) in ctx.break_instructions {
                    let lir::Instruction::Jump { destination } =
                        &mut self.block_map[block_id].instructions[idx]
                    else {
                        unreachable!()
                    };

                    *destination = end_block_id;

                    self.block_map[end_block_id].predecessors.insert(block_id);
                }

                // Continue execution in the new block

                self.block_stack.pop_back();
                self.block_stack.push_back(end_block_id);
            }
            hir::ExpressionKind::Assignment { lhs, rhs } => {
                // get the pointer we're assigning into

                self.with_dest_and_expr_ctx(None, ExpressionContext::Place, |this| {
                    this.visit_expression(lhs.clone())
                });

                let ptr_reg = match self.expression_to_operand_map[&lhs.hir_id.local_id] {
                    lir::Operand::Register(x) => x,
                    source => {
                        // TODO: we dont need this copy here if we can figure
                        // out a good way to specify all of our constraints here
                        // in the code
                        let destination = self.create_register_with_lir_type(lir::Type::Pointer);
                        self.push_instruction(lir::Instruction::Copy {
                            destination,
                            source,
                        });
                        destination
                    }
                };

                // evaluate the value and store it if it was not constructed in
                // place with the provided aggregate destination register

                let ty = self.type_map.get_type(rhs.hir_id);
                let ty = self.lower_type(ty);

                self.with_dest_and_expr_ctx(
                    ty.is_aggregate().then(|| ptr_reg),
                    ExpressionContext::Value,
                    |this| this.visit_expression(rhs.clone()),
                );

                let value = self.expression_to_operand_map[&rhs.hir_id.local_id];

                if ty.is_scalar() {
                    self.emit_store_mem(lir::Operand::Register(ptr_reg), value, ty);
                } else {
                    debug_assert_eq!(
                        value,
                        lir::Operand::Register(ptr_reg),
                        "let stmt destination was not respected for expr: {rhs:#?}"
                    );
                }
            }
            hir::ExpressionKind::OperatorAssignment { operator, lhs, rhs } => todo!(),
            hir::ExpressionKind::Break => {
                let current_block = *self.block_stack.back().unwrap();
                let idx = self.push_instruction(lir::Instruction::Jump {
                    destination: lir::BlockId::PLACEHOLDER,
                });

                let ctx = self
                    .loop_ctx_stack
                    .last_mut()
                    .expect("missing loop context at continue");
                ctx.break_instructions.push((current_block, idx));
            }
            hir::ExpressionKind::Continue => {
                let ctx = self
                    .loop_ctx_stack
                    .last()
                    .expect("missing loop context at continue");

                let current_block_id = lir::BlockId::new(self.block_map.len() - 1);
                self.block_map[ctx.start_block]
                    .predecessors
                    .insert(current_block_id);

                self.push_instruction(lir::Instruction::Jump {
                    destination: ctx.start_block,
                });
            }
            hir::ExpressionKind::Return(value) => {
                self.with_dest_and_expr_ctx(self.struct_return, ExpressionContext::Value, |this| {
                    hir::visit::walk_expression(this, expression.clone());
                });

                if self.struct_return.is_some() {
                    {
                        assert!(value.is_some());
                        assert!(
                            self.type_map
                                .get_type(value.as_ref().unwrap().hir_id)
                                .is_aggregate()
                        );
                    }

                    self.push_instruction(lir::Instruction::Return { value: None });
                    return;
                }

                let value = value
                    .as_ref()
                    .map(|e| self.expression_to_operand_map[&e.hir_id.local_id]);

                // Main implicitly returns 0 even if the signature does not
                // say so
                let value = if self.local_symbol_name.value() == "main" {
                    Some(value.unwrap_or(lir::Operand::Immediate(lir::Immediate::Int(
                        0,
                        lir::IntegerWidth::I8,
                    ))))
                } else {
                    value
                };

                self.push_instruction(lir::Instruction::Return { value });
            }
        }
    }

    fn visit_block(&mut self, block: Rc<hir::Block>, _context: hir::visit::BlockContext) {
        // hir::visit::walk_block(self, block.clone());

        for statement in block.statements.iter() {
            self.with_dest_and_expr_ctx(None, ExpressionContext::Value, |this| {
                this.visit_statement(statement.clone())
            });
        }

        if let Some(e) = &block.expression {
            self.visit_expression(e.clone());

            let ty = self.type_map.get_type(e.hir_id);
            if ty.is_unit() || ty.is_never() {
                return;
            }

            let value = self.expression_to_operand_map[&e.hir_id.local_id];

            self.expression_to_operand_map
                .insert(block.hir_id.local_id, value);
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FormatStringItem {
    String(InternedSymbol),
    Argument(usize),
}

fn parse_format_string(string: &str) -> Vec<FormatStringItem> {
    let mut parts = Vec::new();
    let mut arg_count = 0;

    let mut last = 0;
    for (index, matched) in string.match_indices("{}") {
        if last != index {
            parts.push(FormatStringItem::String(InternedSymbol::new(
                &string[last..index],
            )));
        }

        parts.push(FormatStringItem::Argument(arg_count));
        arg_count += 1;

        last = index + matched.len();
    }
    if last < string.len() {
        parts.push(FormatStringItem::String(InternedSymbol::new(
            &string[last..],
        )));
    }

    parts.retain(|i| !matches!(i, FormatStringItem::String(s) if s.value() == ""));

    parts
}

pub fn lower_to_lir(module: &hir::Module, type_map: &ModuleTypeCheckResults) -> lir::Module {
    let mut function_definitions = BTreeMap::new();
    let mut static_definitions = BTreeMap::new();

    let mut next_static_label_id = lir::StaticLabelId::new(0);
    let mut static_strings = BTreeMap::new();
    let mut static_c_strings = BTreeMap::new();

    for owner_id in module.get_owners() {
        let item = module
            .get_owner(owner_id)
            .unwrap()
            .node()
            .as_item()
            .unwrap();

        match &item.kind {
            hir::ItemKind::Function { name, .. } => {
                let local_symbol_name = name.as_local_symbol();
                let global_symbol_name = module.global_symbol_for(name);

                let mut ctx = BodyLoweringContext {
                    module,
                    owner_id,
                    local_symbol_name,
                    global_symbol_name,
                    type_map,
                    next_static_label_id: &mut next_static_label_id,
                    static_strings: &mut static_strings,
                    static_c_strings: &mut static_c_strings,
                    register_map: IndexVec::new(),
                    struct_return: None,
                    arguments: Vec::new(),
                    block_map: IndexVec::new(),
                    block_stack: VecDeque::new(),
                    loop_ctx_stack: Vec::new(),
                    local_to_register_map: BTreeMap::new(),
                    expression_to_operand_map: BTreeMap::new(),
                    destination_register: None,
                    expression_context: ExpressionContext::Value,
                };

                let hir::OwnerNode::Item(item) = module.get_owner(owner_id).unwrap().node();
                hir::visit::walk_item(&mut ctx, item);

                function_definitions.insert(owner_id, ctx.into_output());
            }
            hir::ItemKind::Struct { .. }
            | hir::ItemKind::Enum { .. }
            | hir::ItemKind::TypeAlias { .. } => continue,
            hir::ItemKind::Static { name, ty, .. } => {
                let mut ctx = BodyLoweringContext {
                    module,
                    owner_id,
                    local_symbol_name: name.symbol,
                    global_symbol_name: name.symbol,
                    type_map,
                    next_static_label_id: &mut next_static_label_id,
                    static_strings: &mut static_strings,
                    static_c_strings: &mut static_c_strings,
                    register_map: IndexVec::new(),
                    struct_return: None,
                    arguments: Vec::new(),
                    block_map: IndexVec::new(),
                    block_stack: VecDeque::new(),
                    loop_ctx_stack: Vec::new(),
                    local_to_register_map: BTreeMap::new(),
                    expression_to_operand_map: BTreeMap::new(),
                    destination_register: None,
                    expression_context: ExpressionContext::Value,
                };

                let ty = type_map.get_type(ty.hir_id);
                let ty = ctx.lower_type(ty);

                static_definitions.insert(
                    owner_id,
                    lir::StaticDefinition {
                        symbol_name: name.symbol,
                        layout: ty.layout(),
                    },
                );
            }
        }
    }

    lir::Module {
        function_definitions,
        static_definitions,
        static_strings,
        static_c_strings,
    }
}
