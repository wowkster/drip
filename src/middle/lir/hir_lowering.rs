use std::{
    any::TypeId,
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
        hir,
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
    expression_to_register_map: BTreeMap<hir::ItemLocalId, lir::RegisterId>,
    struct_return: Option<lir::RegisterId>,
    arguments: Vec<lir::RegisterId>,

    block_map: IndexVec<lir::BlockId, lir::Block>,
    block_stack: VecDeque<lir::BlockId>,

    /// If we are lowering an expression where the destination is known (like a
    /// let sms initializer), we use this destination instead of allocating a
    /// new temporary register to avoid unnecessary copying.
    destination_register: Option<lir::RegisterId>,
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

    fn push_instruction(&mut self, instruction: lir::Instruction) {
        let current_block = self.block_stack.back().unwrap();
        self.block_map[*current_block]
            .instructions
            .push(instruction);
    }

    fn push_comment(&mut self, comment: impl Into<String>) {
        self.push_instruction(lir::Instruction::Comment(comment.into()));
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

    fn lower_string(
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
            self.expression_to_register_map
                .insert(e.hir_id.local_id, struct_ptr_reg);
        }

        struct_ptr_reg
    }

    fn print_string(&mut self, str_ptr_reg: lir::RegisterId) -> lir::RegisterId {
        /* Extract struct fields */

        let ptr_ptr_reg = self.create_register_with_lir_type(lir::Type::Pointer);
        self.push_instruction(lir::Instruction::GetStructElementPointer {
            destination: ptr_ptr_reg,
            source: lir::Operand::Register(str_ptr_reg),
            ty: lir::Struct::slice(),
            index: 0,
        });
        let ptr_reg = self.create_register_with_lir_type(lir::Type::Pointer);
        self.push_instruction(lir::Instruction::LoadMem {
            destination: ptr_reg,
            source: lir::Operand::Register(ptr_ptr_reg),
        });

        let len_ptr_reg =
            self.create_register_with_lir_type(lir::Type::Integer(lir::IntegerWidth::I64));
        self.push_instruction(lir::Instruction::GetStructElementPointer {
            destination: len_ptr_reg,
            source: lir::Operand::Register(str_ptr_reg),
            ty: lir::Struct::slice(),
            index: 1,
        });
        let len_reg =
            self.create_register_with_lir_type(lir::Type::Integer(lir::IntegerWidth::I64));
        self.push_instruction(lir::Instruction::LoadMem {
            destination: len_reg,
            source: lir::Operand::Register(len_ptr_reg),
        });

        let dest_reg =
            self.create_register_with_lir_type(lir::Type::Integer(lir::IntegerWidth::I64));

        self.push_instruction(lir::Instruction::FunctionCall {
            target: lir::Operand::Immediate(lir::Immediate::FunctionLabel(InternedSymbol::new(
                "__$print_str",
            ))),
            arguments: vec![
                lir::Operand::Register(ptr_reg),
                lir::Operand::Register(len_reg),
            ],
            destination: Some(dest_reg),
        });

        dest_reg
    }

    fn lower_binary_op(
        &mut self,
        operand_ty: ty::Type,
        lhs: lir::RegisterId,
        operator: BinaryOperatorKind,
        rhs: lir::RegisterId,
        destination: lir::RegisterId,
    ) {
        match &*operand_ty {
            ty::TypeKind::Unit => todo!(),
            ty::TypeKind::Bool
            | ty::TypeKind::Char
            | ty::TypeKind::Integer(_)
            | ty::TypeKind::UnsignedInteger(_)
            | ty::TypeKind::Float(_)
            | ty::TypeKind::Pointer(_)
            | ty::TypeKind::FunctionPointer { .. }
            | ty::TypeKind::Any => {
                // TODO: if LHS is a pointer and RHS is a usize, scale by size of pointee type

                self.push_instruction(lir::Instruction::BinaryOperation {
                    operator,
                    destination,
                    lhs: lir::Operand::Register(lhs),
                    rhs: lir::Operand::Register(rhs),
                });
            }
            ty::TypeKind::Str => todo!(),
            ty::TypeKind::CStr => todo!(),
            ty::TypeKind::Slice(_) => todo!(),
            ty::TypeKind::Array { ty: _, length: _ } => todo!(),
            ty::TypeKind::Tuple(items) => {
                let structure =
                    lir::Struct(items.iter().map(|ty| self.lower_type(ty.clone())).collect());

                // Collect results of comparing all sub elements

                let destination_regs = items
                    .iter()
                    .enumerate()
                    .map(|(i, ty)| {
                        let reg_ty = self.lower_type_indirect(ty.clone());

                        // Load element from LHS tuple

                        let lhs_ptr_reg = self.create_register_with_lir_type(lir::Type::Integer(
                            lir::IntegerWidth::I64,
                        ));
                        self.push_instruction(lir::Instruction::GetStructElementPointer {
                            destination: lhs_ptr_reg,
                            source: lir::Operand::Register(lhs),
                            ty: structure.clone(),
                            index: i,
                        });
                        let lhs_reg = self.create_register_with_lir_type(reg_ty.clone());
                        self.push_instruction(lir::Instruction::LoadMem {
                            destination: lhs_reg,
                            source: lir::Operand::Register(lhs_ptr_reg),
                        });

                        // Load element from RHS tuple

                        let rhs_ptr_reg = self.create_register_with_lir_type(lir::Type::Integer(
                            lir::IntegerWidth::I64,
                        ));
                        self.push_instruction(lir::Instruction::GetStructElementPointer {
                            destination: rhs_ptr_reg,
                            source: lir::Operand::Register(rhs),
                            ty: structure.clone(),
                            index: i,
                        });
                        let rhs_reg = self.create_register_with_lir_type(reg_ty);
                        self.push_instruction(lir::Instruction::LoadMem {
                            destination: rhs_reg,
                            source: lir::Operand::Register(rhs_ptr_reg),
                        });

                        // Compare lhs and rhs

                        let destination = self.create_register_with_lir_type(lir::Type::Integer(
                            lir::IntegerWidth::I8,
                        ));
                        self.lower_binary_op(ty.clone(), lhs_reg, operator, rhs_reg, destination);

                        destination
                    })
                    .collect::<Vec<_>>();

                assert!(matches!(operator, BinaryOperatorKind::Equals | BinaryOperatorKind::NotEquals));

                // Make sure that all sub-elements compared equal

                self.push_instruction(lir::Instruction::Move {
                    destination,
                    source: lir::Operand::Register(*destination_regs.first().unwrap()),
                });

                for reg in destination_regs.into_iter().skip(1) {
                    self.push_instruction(lir::Instruction::BinaryOperation {
                        operator: BinaryOperatorKind::LogicalAnd,
                        destination,
                        lhs: lir::Operand::Register(destination),
                        rhs: lir::Operand::Register(reg),
                    });
                }

                // make sure that all the elements are true
            }
            ty::TypeKind::Struct {
                def_id,
                name,
                fields,
            } => todo!(),
            ty::TypeKind::Never | ty::TypeKind::Infer(_) | ty::TypeKind::Error => unreachable!(),
        }
    }

    /// Outputs a copy from src into dest. For scalar types, this operation is a
    /// Move instruction. For aggregate types, this is a field by field copy
    /// operation.
    fn lower_copy(&mut self, dest_reg: lir::RegisterId, src_reg: lir::RegisterId, ty: ty::Type) {
        if ty.is_struct() {
            // FIXME: could we just memcpy instead?

            let ty = self.lower_type(ty);
            let lir::Type::Struct(structure_ty) = ty else {
                unreachable!()
            };

            for (i, f) in structure_ty.0.iter().enumerate() {
                let src_ptr_reg = self.create_register_with_lir_type(lir::Type::Pointer);
                self.push_instruction(lir::Instruction::GetStructElementPointer {
                    destination: src_ptr_reg,
                    source: lir::Operand::Register(src_reg),
                    ty: structure_ty.clone(),
                    index: i,
                });

                let tmp_ptr_reg = self.create_register_with_lir_type(f.to_owned());
                self.push_instruction(lir::Instruction::LoadMem {
                    destination: tmp_ptr_reg,
                    source: lir::Operand::Register(src_ptr_reg),
                });

                let dest_ptr_reg = self.create_register_with_lir_type(lir::Type::Pointer);
                self.push_instruction(lir::Instruction::GetStructElementPointer {
                    destination: dest_ptr_reg,
                    source: lir::Operand::Register(dest_reg),
                    ty: structure_ty.clone(),
                    index: i,
                });

                self.push_instruction(lir::Instruction::StoreMem {
                    destination: lir::Operand::Register(dest_ptr_reg),
                    source: lir::Operand::Register(tmp_ptr_reg),
                });
            }
        } else {
            self.push_instruction(lir::Instruction::Move {
                destination: dest_reg,
                source: lir::Operand::Register(src_reg),
            });
        }
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

            if return_ty.is_struct() {
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

            let dest_struct_ptr_reg = self
                .struct_return
                .expect("functions returning a struct should have an sret set");
            let src_struct_ptr_reg = self.expression_to_register_map[&e.hir_id.local_id];

            self.lower_copy(dest_struct_ptr_reg, src_struct_ptr_reg, ty);
            self.push_instruction(lir::Instruction::Return { value: None });
        } else {
            // FIXME: dont add an extra return if the last expr is already a return stmt

            // Main implicitly returns 0 even if there is no return value
            let value = implicit_return
                .and_then(|e| self.expression_to_register_map.get(&e.hir_id.local_id))
                .copied()
                .map(lir::Operand::Register)
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

        let reg = self.create_register(ty.clone());
        self.local_to_register_map
            .insert(let_stmt.hir_id.local_id, reg);

        if ty.is_aggregate() {
            let ty = self.lower_type(ty.clone());

            self.push_instruction(lir::Instruction::AllocStack {
                destination: reg,
                ty: ty,
            });
        }

        self.with_destination(Some(reg), |this| {
            hir::visit::walk_let_statement(this, let_stmt.clone())
        });

        if let Some(init) = &let_stmt.initializer {
            debug_assert_eq!(
                self.expression_to_register_map[&init.hir_id.local_id], reg,
                "let stmt destination was not respected for expr: {init:#?}"
            );
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
                        self.lower_string(*s, Some(expression.clone()));
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

                let reg = self.destination_register.unwrap_or_else(|| {
                    let ty = self.type_map.get_type(expression.hir_id);
                    self.create_register(ty)
                });

                self.push_instruction(lir::Instruction::Move {
                    destination: reg,
                    source: lir::Operand::Immediate(value),
                });
                self.expression_to_register_map
                    .insert(expression.hir_id.local_id, reg);
            }
            hir::ExpressionKind::Path(path) => {
                self.with_destination(self.destination_register, |this| {
                    hir::visit::walk_expression(this, expression.clone())
                });

                if let Some(reg) = self
                    .expression_to_register_map
                    .get(&path.segments.last().unwrap().hir_id.local_id)
                {
                    self.expression_to_register_map
                        .insert(expression.hir_id.local_id, *reg);
                }
            }
            hir::ExpressionKind::This => {
                // self is always the 0th argument when present
                self.expression_to_register_map
                    .insert(expression.hir_id.local_id, self.arguments[0]);
            }
            hir::ExpressionKind::Array(hir::ArrayInitializer::Repeated { value, length }) => {
                todo!()
            }
            hir::ExpressionKind::Array(hir::ArrayInitializer::Specific(values)) => {
                hir::visit::walk_expression(self, expression.clone());

                let array_ty = self.lower_type(self.type_map.get_type(expression.hir_id));
                let lir::Type::Array(inner_ty, length) = array_ty.clone() else {
                    unreachable!()
                };

                assert_eq!(length, values.len());

                let array_ptr_reg = self.create_register_with_lir_type(lir::Type::Pointer);
                self.push_instruction(lir::Instruction::AllocStack {
                    destination: array_ptr_reg,
                    ty: array_ty,
                });

                for (i, e) in values.iter().enumerate() {
                    let element_ptr_reg = self.create_register_with_lir_type(lir::Type::Pointer);
                    self.push_instruction(lir::Instruction::GetArrayElementPointer {
                        destination: element_ptr_reg,
                        source: lir::Operand::Register(array_ptr_reg),
                        ty: inner_ty.as_ref().clone(),
                        index: i,
                    });

                    let expr_reg = self.expression_to_register_map[&e.hir_id.local_id];
                    self.push_instruction(lir::Instruction::StoreMem {
                        destination: lir::Operand::Register(element_ptr_reg),
                        source: lir::Operand::Register(expr_reg),
                    });
                }

                self.expression_to_register_map
                    .insert(expression.hir_id.local_id, array_ptr_reg);
            }
            hir::ExpressionKind::Tuple(expressions) => {
                let ty = self.type_map.get_type(expression.hir_id);
                let lir::Type::Struct(structure) = self.lower_type(ty) else {
                    unreachable!()
                };

                /* Create a temporary if a destination was not already allocated */

                let struct_ptr_reg = self.destination_register.unwrap_or_else(|| {
                    let reg = self.create_register_with_lir_type(lir::Type::Pointer);

                    self.push_instruction(lir::Instruction::AllocStack {
                        destination: reg,
                        ty: lir::Type::Struct(structure.clone()),
                    });

                    reg
                });

                /* Set each field */

                for (i, e) in expressions.iter().enumerate() {
                    self.push_comment(format!("field {i}"));

                    // get field address

                    let element_ptr_reg = self.create_register_with_lir_type(lir::Type::Pointer);
                    self.push_instruction(lir::Instruction::GetStructElementPointer {
                        destination: element_ptr_reg,
                        source: lir::Operand::Register(struct_ptr_reg),
                        ty: structure.clone(),
                        index: i,
                    });

                    // compute field value

                    let ty = self.type_map.get_type(e.hir_id);

                    let dest_reg = if ty.is_aggregate() {
                        element_ptr_reg
                    } else {
                        self.create_register(ty.clone())
                    };
                    self.with_destination(Some(dest_reg), |this| this.visit_expression(e.clone()));

                    debug_assert_eq!(
                        self.expression_to_register_map[&e.hir_id.local_id], dest_reg,
                        "struct field destination was not respected for expr: {:#?}",
                        e
                    );

                    // store field value (if we didnt pass it to the expression)

                    if element_ptr_reg != dest_reg {
                        self.push_instruction(lir::Instruction::StoreMem {
                            destination: lir::Operand::Register(element_ptr_reg),
                            source: lir::Operand::Register(dest_reg),
                        });
                    }
                }

                self.expression_to_register_map
                    .insert(expression.hir_id.local_id, struct_ptr_reg);
            }
            hir::ExpressionKind::Struct { name: _, fields } => {
                let ty = self.type_map.get_type(expression.hir_id);
                let lir::Type::Struct(structure) = self.lower_type(ty) else {
                    unreachable!()
                };

                /* Create a temporary if a destination was not already allocated */

                let struct_ptr_reg = self.destination_register.unwrap_or_else(|| {
                    let reg = self.create_register_with_lir_type(lir::Type::Pointer);

                    self.push_instruction(lir::Instruction::AllocStack {
                        destination: reg,
                        ty: lir::Type::Struct(structure.clone()),
                    });

                    reg
                });

                /* Set each field */

                for (i, f) in fields.iter().enumerate() {
                    self.push_comment(format!("field {i}"));

                    // get field address

                    let element_ptr_reg = self.create_register_with_lir_type(lir::Type::Pointer);
                    self.push_instruction(lir::Instruction::GetStructElementPointer {
                        destination: element_ptr_reg,
                        source: lir::Operand::Register(struct_ptr_reg),
                        ty: structure.clone(),
                        index: i,
                    });

                    // compute field value

                    let ty = self.type_map.get_type(f.value.hir_id);

                    let dest_reg = if ty.is_aggregate() {
                        element_ptr_reg
                    } else {
                        self.create_register(ty.clone())
                    };
                    self.with_destination(Some(dest_reg), |this| {
                        this.visit_expression(f.value.clone())
                    });

                    debug_assert_eq!(
                        self.expression_to_register_map[&f.value.hir_id.local_id], dest_reg,
                        "struct field destination was not respected for expr: {:#?}",
                        f.value
                    );

                    // store field value (if we didnt pass it to the expression)

                    if element_ptr_reg != dest_reg {
                        self.push_instruction(lir::Instruction::StoreMem {
                            destination: lir::Operand::Register(element_ptr_reg),
                            source: lir::Operand::Register(dest_reg),
                        });
                    }
                }

                self.expression_to_register_map
                    .insert(expression.hir_id.local_id, struct_ptr_reg);
            }
            hir::ExpressionKind::Block(block) => {
                self.with_destination(self.destination_register, |this| {
                    hir::visit::walk_expression(this, expression.clone())
                });

                if let Some(reg) = self.expression_to_register_map.get(&block.hir_id.local_id) {
                    self.expression_to_register_map
                        .insert(expression.hir_id.local_id, *reg);
                }
            }
            hir::ExpressionKind::FieldAccess {
                target,
                name,
                is_method_call,
            } => {
                assert!(
                    !is_method_call,
                    "method calls should be handled in the function call visitor"
                );

                let mut target = target;
                let target_ty = self.type_map.get_type(target.hir_id);

                // for an owned struct (T), the object lives locally on the
                // stack, but we still only store a pointer to that local
                // memory. for a reference to a struct (*T or *mut T), the
                // object lives somewhere else and we store a pointer to that
                // non-local memory. in either case, the register associated
                // with the structure just stores a pointer so accessing a field
                // directly is the same exact operation as doing so through a
                // dereference.

                if let hir::ExpressionKind::Unary {
                    operator: UnaryOperatorKind::Deref,
                    operand,
                } = &target.kind
                    && target_ty.is_aggregate()
                {
                    target = operand;
                }

                self.with_destination(None, |this| this.visit_expression(target.clone()));

                let target_reg = self.expression_to_register_map[&target.hir_id.local_id];

                // target type is either be a struct or struct-like type (str,
                // slice, tuple, etc) . The register associated with this
                // expression stores a pointer to the structure and we need to
                // emit instructions for getting the pointer to the field and
                // getting loading the field from memory. If the field type is
                // >8 bytes in size, we just store the pointer to it instead of
                // copying the data out.

                match &*target_ty {
                    ty::TypeKind::Pointer(_) => todo!(),
                    ty::TypeKind::Str | ty::TypeKind::Slice(_) => {
                        let structure_ty = lir::Struct::slice();

                        let (field_index, field_ty) = match name.symbol.value() {
                            "ptr" => (0, lir::Type::Pointer),
                            "len" => (1, lir::Type::Integer(lir::IntegerWidth::I64)),
                            _ => unreachable!(),
                        };

                        let field_ptr_reg = self.create_register_with_lir_type(lir::Type::Pointer);
                        self.push_instruction(lir::Instruction::GetStructElementPointer {
                            destination: field_ptr_reg,
                            source: lir::Operand::Register(target_reg),
                            ty: structure_ty,
                            index: field_index,
                        });
                        let field_reg = self
                            .destination_register
                            .unwrap_or_else(|| self.create_register_with_lir_type(field_ty));
                        self.push_instruction(lir::Instruction::LoadMem {
                            destination: field_reg,
                            source: lir::Operand::Register(field_ptr_reg),
                        });

                        self.expression_to_register_map
                            .insert(expression.hir_id.local_id, field_reg);
                    }
                    ty::TypeKind::Tuple(items) => {
                        let index = name
                            .symbol
                            .value()
                            .strip_prefix("v")
                            .unwrap()
                            .parse::<usize>()
                            .unwrap();

                        let lir::Type::Struct(structure_ty) = self.lower_type(target_ty) else {
                            unreachable!();
                        };
                        let field_ty = structure_ty.0[index].clone();

                        let field_ptr_reg = self.create_register_with_lir_type(lir::Type::Pointer);
                        self.push_instruction(lir::Instruction::GetStructElementPointer {
                            destination: field_ptr_reg,
                            source: lir::Operand::Register(target_reg),
                            ty: structure_ty,
                            index,
                        });
                        let field_reg = self
                            .destination_register
                            .unwrap_or_else(|| self.create_register_with_lir_type(field_ty));
                        self.push_instruction(lir::Instruction::LoadMem {
                            destination: field_reg,
                            source: lir::Operand::Register(field_ptr_reg),
                        });

                        self.expression_to_register_map
                            .insert(expression.hir_id.local_id, field_reg);
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

                        let field_ptr_reg = self.create_register_with_lir_type(lir::Type::Pointer);
                        self.push_instruction(lir::Instruction::GetStructElementPointer {
                            destination: field_ptr_reg,
                            source: lir::Operand::Register(target_reg),
                            ty: structure_ty,
                            index: field_index,
                        });
                        let field_reg = self
                            .destination_register
                            .unwrap_or_else(|| self.create_register_with_lir_type(field_ty));
                        self.push_instruction(lir::Instruction::LoadMem {
                            destination: field_reg,
                            source: lir::Operand::Register(field_ptr_reg),
                        });

                        self.expression_to_register_map
                            .insert(expression.hir_id.local_id, field_reg);
                    }
                    _ => unreachable!(),
                }
            }
            hir::ExpressionKind::FunctionCall { target, arguments } => {
                self.with_destination(None, |this| {
                    hir::visit::walk_expression(this, target.clone())
                });

                match &target.kind {
                    hir::ExpressionKind::Path(path) => {
                        match path.resolution() {
                            hir::Resolution::Definition(hir::DefinitionKind::Function, def_id) => {
                                let mut args = Vec::with_capacity(arguments.len());

                                self.push_comment("copy arguments to function");

                                // allocate a destination register for all
                                // function arguments. as we traverse the
                                // argument nodes, if they would have allocated
                                // a temporary, we make them use these registers
                                // instead. for example, encountering a path
                                // will move or copy into the register (based on
                                // whether its a scalar or aggregate).
                                for (i, arg) in arguments.iter().enumerate() {
                                    self.push_comment(format!("argument {i}"));

                                    let ty = self.type_map.get_type(arg.hir_id);
                                    let reg = self.create_register(ty.clone());

                                    if ty.is_aggregate() {
                                        let ty = self.lower_type(ty);
                                        self.push_instruction(lir::Instruction::AllocStack {
                                            destination: reg,
                                            ty: ty,
                                        });
                                    }

                                    self.with_destination(Some(reg), |this| {
                                        this.visit_expression(arg.clone())
                                    });

                                    debug_assert_eq!(
                                        self.expression_to_register_map[&arg.hir_id.local_id], reg,
                                        "function arg destination was not respected for expr: {arg:#?}"
                                    );

                                    args.push(reg);
                                }

                                let hir::ItemKind::Function {
                                    name, signature, ..
                                } = &self
                                    .module
                                    .get_owner(*def_id)
                                    .node()
                                    .as_item()
                                    .unwrap()
                                    .kind
                                else {
                                    unreachable!()
                                };

                                let return_ty = signature
                                    .return_type
                                    .as_ref()
                                    .map(|ty| self.type_map.get_type(ty.hir_id));

                                let destination_reg = return_ty.clone().map(|ty| {
                                    self.destination_register.unwrap_or_else(|| {
                                        let reg = self.create_register(ty.clone());

                                        if ty.is_aggregate() {
                                            let ty = self.lower_type(ty);
                                            self.push_instruction(lir::Instruction::AllocStack {
                                                destination: reg,
                                                ty: ty,
                                            });
                                        }

                                        reg
                                    })
                                });

                                let args = return_ty
                                    .clone()
                                    .zip(destination_reg)
                                    .and_then(|(ty, destination_reg)| {
                                        if !ty.is_aggregate() {
                                            return None;
                                        }

                                        Some(lir::Operand::Register(destination_reg))
                                    })
                                    .into_iter()
                                    .chain(args.into_iter().map(lir::Operand::Register))
                                    .collect();

                                // returning a struct:
                                //
                                // caller allocates room for the struct on the stack
                                // caller passes a pointer to this struct as a hidden argument (rdi)
                                // callee does alloc stack
                                // move exprs into fields
                                // memcpy from stack into return struct
                                //
                                // if optimizer recognizes that struct return is
                                // the last block, above can be simplified to
                                // move exprs directly into struct fields
                                // instead of calling memcpy

                                // passing a struct:
                                // caller

                                let symbol = self.module.global_symbol_for(name);
                                self.push_instruction(lir::Instruction::FunctionCall {
                                    target: lir::Operand::Immediate(lir::Immediate::FunctionLabel(
                                        symbol,
                                    )),
                                    arguments: args,
                                    // we pass through the destination reg if
                                    // there is no return type (already None),
                                    // or if the return type is not a struct
                                    // since struct returns are handled
                                    // differently
                                    destination: return_ty
                                        .is_none_or(|ty| !ty.is_aggregate())
                                        .then_some(destination_reg)
                                        .flatten(),
                                });

                                if let Some(dest) = destination_reg {
                                    self.expression_to_register_map
                                        .insert(expression.hir_id.local_id, dest);
                                }
                            }
                            hir::Resolution::Definition(..) => {
                                unreachable!(
                                    "other definition kinds may not be function call targets"
                                )
                            }
                            hir::Resolution::Local(_) => todo!("locals as function pointers"),
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
                                        self.visit_expression(arg.clone());
                                    }

                                    let str_ptr_reg = self.expression_to_register_map
                                        [&arguments[0].hir_id.local_id];

                                    let dest_reg = self.print_string(str_ptr_reg);

                                    // FIXME: should this function care about the return value?
                                    self.expression_to_register_map
                                        .insert(expression.hir_id.local_id, dest_reg);

                                    return;
                                }

                                for arg in arguments.iter().skip(1) {
                                    self.visit_expression(arg.clone());
                                }

                                for part in parts {
                                    match part {
                                        FormatStringItem::String(symbol) => {
                                            let str_ptr_reg = self.lower_string(symbol, None);

                                            let dest_reg = self.print_string(str_ptr_reg);

                                            // FIXME: should this function care about the return value?
                                            self.expression_to_register_map
                                                .insert(expression.hir_id.local_id, dest_reg);
                                        }
                                        FormatStringItem::Argument(index) => {
                                            let arg = &arguments[index + 1];
                                            let arg_reg = self.expression_to_register_map
                                                [&arg.hir_id.local_id];
                                            let ty = self.type_map.get_type(arg.hir_id);

                                            match &*ty {
                                                ty::TypeKind::Integer(int_kind) => {
                                                    let width: lir::IntegerWidth =
                                                        (*int_kind).into();

                                                    let dest_reg = self
                                                        .create_register_with_lir_type(
                                                            lir::Type::Integer(width),
                                                        );

                                                    let fn_name = match width {
                                                        lir::IntegerWidth::I8 => "__$print_i8",
                                                        lir::IntegerWidth::I16 => "__$print_i16",
                                                        lir::IntegerWidth::I32 => "__$print_i32",
                                                        lir::IntegerWidth::I64 => "__$print_i64",
                                                    };

                                                    self.push_instruction(
                                                        lir::Instruction::FunctionCall {
                                                            target: lir::Operand::Immediate(
                                                                lir::Immediate::FunctionLabel(
                                                                    InternedSymbol::new(fn_name),
                                                                ),
                                                            ),
                                                            arguments: vec![
                                                                lir::Operand::Register(arg_reg),
                                                            ],
                                                            destination: Some(dest_reg),
                                                        },
                                                    );

                                                    self.expression_to_register_map.insert(
                                                        expression.hir_id.local_id,
                                                        dest_reg,
                                                    );
                                                }
                                                ty::TypeKind::UnsignedInteger(uint_kind) => {
                                                    let width: lir::IntegerWidth =
                                                        (*uint_kind).into();

                                                    let dest_reg = self
                                                        .create_register_with_lir_type(
                                                            lir::Type::Integer(width),
                                                        );

                                                    let fn_name = match width {
                                                        lir::IntegerWidth::I8 => "__$print_u8",
                                                        lir::IntegerWidth::I16 => "__$print_u16",
                                                        lir::IntegerWidth::I32 => "__$print_u32",
                                                        lir::IntegerWidth::I64 => "__$print_u64",
                                                    };

                                                    self.push_instruction(
                                                        lir::Instruction::FunctionCall {
                                                            target: lir::Operand::Immediate(
                                                                lir::Immediate::FunctionLabel(
                                                                    InternedSymbol::new(fn_name),
                                                                ),
                                                            ),
                                                            arguments: vec![
                                                                lir::Operand::Register(arg_reg),
                                                            ],
                                                            destination: Some(dest_reg),
                                                        },
                                                    );

                                                    self.expression_to_register_map.insert(
                                                        expression.hir_id.local_id,
                                                        dest_reg,
                                                    );
                                                }
                                                ty::TypeKind::Pointer(_) => {
                                                    let dest_reg = self
                                                        .create_register_with_lir_type(
                                                            lir::Type::Pointer,
                                                        );

                                                    self.push_instruction(
                                                        lir::Instruction::FunctionCall {
                                                            target: lir::Operand::Immediate(
                                                                lir::Immediate::FunctionLabel(
                                                                    InternedSymbol::new(
                                                                        "__$print_i64_hex",
                                                                    ),
                                                                ),
                                                            ),
                                                            arguments: vec![
                                                                lir::Operand::Register(arg_reg),
                                                            ],
                                                            destination: Some(dest_reg),
                                                        },
                                                    );

                                                    self.expression_to_register_map.insert(
                                                        expression.hir_id.local_id,
                                                        dest_reg,
                                                    );
                                                }
                                                _ => todo!(),
                                            }
                                        }
                                    }
                                }
                            }
                            hir::Resolution::IntrinsicFunction(name) if name.value() == "exit" => {
                                self.visit_expression(arguments[0].clone());

                                let arg_reg =
                                    self.expression_to_register_map[&arguments[0].hir_id.local_id];

                                self.push_instruction(lir::Instruction::FunctionCall {
                                    target: lir::Operand::Immediate(lir::Immediate::FunctionLabel(
                                        InternedSymbol::new("__$exit"),
                                    )),
                                    arguments: vec![lir::Operand::Register(arg_reg)],
                                    destination: None,
                                });
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
                        is_method_call: true,
                        ..
                    } => {
                        for arg in arguments.iter() {
                            self.visit_expression(arg.clone());
                        }

                        let method_def_id = self.type_map.function_results[&self.owner_id]
                            .method_resolutions[&target.hir_id.local_id];

                        let hir::ItemKind::Function {
                            name, signature, ..
                        } = &self
                            .module
                            .get_owner(method_def_id)
                            .node()
                            .as_item()
                            .unwrap()
                            .kind
                        else {
                            unreachable!()
                        };

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
                        let self_reg = match (signature.self_parameter.unwrap(), &*self_target_ty) {
                            (
                                hir::SelfParameter::Owned,
                                ty::TypeKind::Struct {
                                    def_id,
                                    name,
                                    fields,
                                },
                            ) => todo!(),
                            (hir::SelfParameter::Owned, ty::TypeKind::Pointer(_)) => todo!(),
                            (
                                hir::SelfParameter::Pointer { is_mutable: _ },
                                ty::TypeKind::Pointer(_),
                            ) => self.expression_to_register_map[&self_target.hir_id.local_id],
                            (
                                hir::SelfParameter::Pointer { is_mutable: _ },
                                ty::TypeKind::Struct {
                                    def_id,
                                    name,
                                    fields,
                                },
                            ) => {
                                let src_reg =
                                    self.expression_to_register_map[&self_target.hir_id.local_id];
                                let dest_reg =
                                    self.create_register_with_lir_type(lir::Type::Pointer);

                                let lir::Type::Struct(structure_ty) =
                                    self.lower_type(self_target_ty)
                                else {
                                    unreachable!()
                                };

                                self.push_instruction(lir::Instruction::GetStructElementPointer {
                                    destination: dest_reg,
                                    source: lir::Operand::Register(src_reg),
                                    ty: structure_ty,
                                    index: 0,
                                });

                                dest_reg
                            }

                            (_, ty) => unreachable!("method call on illegal type: {ty}"),
                        };

                        // FIXME: handle aggregate types the same way we do in normal functions (create copies)

                        let args = core::iter::once(lir::Operand::Register(self_reg))
                            .chain(
                                arguments
                                    .iter()
                                    .map(|arg| {
                                        self.expression_to_register_map[&arg.hir_id.local_id]
                                    })
                                    .inspect(|id| match &self.register_map[*id].ty {
                                        lir::Type::Struct(_) | lir::Type::Array(_, _) => {
                                            todo!("pass aggregate types stored in registers")
                                        }
                                        _ => {}
                                    })
                                    .map(lir::Operand::Register),
                            )
                            .collect();

                        let destination_reg = signature.return_type.as_ref().map(|ty| {
                            self.destination_register.unwrap_or_else(|| {
                                let ty = self.type_map.get_type(ty.hir_id);
                                let reg = self.create_register(ty.clone());

                                if ty.is_aggregate() {
                                    let ty = self.lower_type(ty);
                                    self.push_instruction(lir::Instruction::AllocStack {
                                        destination: reg,
                                        ty: ty,
                                    });
                                }

                                reg
                            })
                        });

                        let symbol = self.module.global_symbol_for(name);
                        self.push_instruction(lir::Instruction::FunctionCall {
                            target: lir::Operand::Immediate(lir::Immediate::FunctionLabel(symbol)),
                            arguments: args,
                            destination: destination_reg,
                        });

                        if let Some(dest) = destination_reg {
                            self.expression_to_register_map
                                .insert(expression.hir_id.local_id, dest);
                        }
                    }
                    _ => todo!("lower function pointer calls"),
                }
            }
            hir::ExpressionKind::Binary { lhs, operator, rhs } => {
                self.with_destination(None, |this| {
                    hir::visit::walk_expression(this, expression.clone())
                });

                let ty = self.type_map.get_type(expression.hir_id);
                let dest_reg = self
                    .destination_register
                    .unwrap_or_else(|| self.create_register(ty));

                let operand_ty = self.type_map.get_type(lhs.hir_id);

                let lhs_reg = self.expression_to_register_map[&lhs.hir_id.local_id];
                let rhs_reg = self.expression_to_register_map[&rhs.hir_id.local_id];

                self.lower_binary_op(operand_ty, lhs_reg, *operator, rhs_reg, dest_reg);

                self.expression_to_register_map
                    .insert(expression.hir_id.local_id, dest_reg);
            }
            hir::ExpressionKind::Unary { operator, operand } => {
                if let hir::ExpressionKind::Path(path) = &operand.kind
                    && path.resolution().as_static_definition().is_some()
                    && matches!(operator, UnaryOperatorKind::AddressOf { .. })
                {
                    let dest_reg = self.create_register_with_lir_type(lir::Type::Pointer);

                    self.push_instruction(lir::Instruction::UnaryOperation {
                        operator: *operator,
                        destination: dest_reg,
                        operand: lir::Operand::Immediate(lir::Immediate::NamedStaticLabel(
                            path.as_local_symbol(),
                        )),
                    });

                    self.expression_to_register_map
                        .insert(expression.hir_id.local_id, dest_reg);

                    return;
                }

                // FIXME: coerce array address of operations into slice creation

                // FIXME: create a local copy of a struct when dereferencing

                self.with_destination(None, |this| {
                    hir::visit::walk_expression(this, expression.clone())
                });

                let ty = self.type_map.get_type(expression.hir_id);
                let dest_reg = self
                    .destination_register
                    .unwrap_or_else(|| self.create_register(ty));

                let operand = self.expression_to_register_map[&operand.hir_id.local_id];

                self.push_instruction(lir::Instruction::UnaryOperation {
                    operator: *operator,
                    destination: dest_reg,
                    operand: lir::Operand::Register(operand),
                });

                self.expression_to_register_map
                    .insert(expression.hir_id.local_id, dest_reg);
            }
            hir::ExpressionKind::Cast {
                expression: castee,
                ty: dest_ty,
            } => {
                self.with_destination(None, |this| {
                    hir::visit::walk_expression(this, expression.clone())
                });

                let src_ty = self.type_map.get_type(expression.hir_id);
                let dest_ty = self.type_map.get_type(dest_ty.hir_id);

                let castee = self.expression_to_register_map[&castee.hir_id.local_id];

                if src_ty == dest_ty {
                    if let Some(dest_reg) = self.destination_register {
                        self.push_instruction(lir::Instruction::Move {
                            destination: dest_reg,
                            source: lir::Operand::Register(castee),
                        });
                        self.expression_to_register_map
                            .insert(expression.hir_id.local_id, dest_reg);
                    } else {
                        self.expression_to_register_map
                            .insert(expression.hir_id.local_id, castee);
                    }

                    return;
                }

                // only integers and pointers can be casted

                let kind = match (&*src_ty, &*dest_ty) {
                    (ty::TypeKind::UnsignedInteger(src), ty::TypeKind::UnsignedInteger(dest))
                        if lir::IntegerWidth::from(*src) < lir::IntegerWidth::from(*dest) =>
                    {
                        lir::IntegerCastKind::ZeroExtension
                    }
                    (ty::TypeKind::UnsignedInteger(_), ty::TypeKind::UnsignedInteger(_)) => {
                        lir::IntegerCastKind::Truncate
                    }
                    (src, dest) => unreachable!("src = {src:?}, dest = {dest:?}"),
                };

                let dest_reg = self
                    .destination_register
                    .unwrap_or_else(|| self.create_register(dest_ty.clone()));
                self.push_instruction(lir::Instruction::IntegerCast {
                    kind,
                    destination: dest_reg,
                    operand: lir::Operand::Register(castee),
                });

                self.expression_to_register_map
                    .insert(expression.hir_id.local_id, dest_reg);
            }
            hir::ExpressionKind::If {
                condition,
                positive,
                negative,
            } => {
                self.with_destination(None, |this| this.visit_expression(condition.clone()));
                let condition = self.expression_to_register_map[&condition.hir_id.local_id];

                let ty = self.type_map.get_type(expression.hir_id);

                let mut destination_register = None;

                // If this conditional has a return value, allocate a register
                // for it and set it in the context so that we know which
                // register to put the block result in later
                if !ty.is_unit() && !ty.is_never() {
                    let reg = self
                        .destination_register
                        .unwrap_or_else(|| self.create_register(ty));
                    destination_register = Some(reg);

                    self.expression_to_register_map
                        .insert(expression.hir_id.local_id, reg);
                }

                // For if expressions, there are 2 possible cases. In the first
                // case where there is no else, we allocate a new block for the
                // positive branch and a new block to act as both the negative
                // fallthrough and the merge point. In the second case where
                // there is an else, we allocate a new block for the positive
                // branch, a new block for the negative branch, and a new block
                // for the merge point.

                let current_block_id = *self.block_stack.back().unwrap();

                let positive_block_id = self.create_block();
                self.block_map[positive_block_id]
                    .predecessors
                    .insert(current_block_id);

                let positive_branch_last_block: lir::BlockId;
                {
                    self.block_stack.push_back(positive_block_id);
                    self.with_destination(destination_register, |this| {
                        this.visit_block(positive.clone(), hir::visit::BlockContext::Scope)
                    });
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
                        .insert(current_block_id);

                    self.block_stack.push_back(negative_branch_block_id);
                    self.with_destination(destination_register, |this| {
                        this.visit_expression(n.clone())
                    });
                    self.block_stack.pop_back();

                    merge_block_id = self.create_block();

                    if !self.type_map.get_type(n.hir_id).is_never() {
                        let last_inserted_block = lir::BlockId::new(self.block_map.len() - 2);

                        // insert unconditional jump in the negative branch to the
                        // allocated merge block if the branch does not return
                        if !self.block_map[last_inserted_block].returns() {
                            self.block_map[last_inserted_block].instructions.push(
                                lir::Instruction::Jump {
                                    destination: merge_block_id,
                                },
                            );
                            self.block_map[merge_block_id]
                                .predecessors
                                .insert(last_inserted_block);
                        }
                    }

                    negative_branch_block_id
                } else {
                    // in this case the negative fallthrough is the same as the
                    // merge block id

                    self.block_map[merge_block_id]
                        .predecessors
                        .insert(current_block_id);

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
                }

                self.block_map[current_block_id]
                    .instructions
                    .push(lir::Instruction::Branch {
                        condition: lir::Operand::Register(condition),
                        positive: positive_block_id,
                        negative: negative_block_id,
                    });

                self.block_stack.pop_back();
                self.block_stack.push_back(merge_block_id);
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

                // TODO: add continue predecessors to condition block

                self.block_stack.push_back(condition_block_id);
                self.visit_expression(condition.clone());
                self.block_stack.pop_back();

                let last_inserted_condition_block = lir::BlockId::new(self.block_map.len() - 1);

                // Loop Body

                let body_block_id = self.create_block();

                self.block_stack.push_back(body_block_id);
                self.visit_block(block.clone(), hir::visit::BlockContext::Loop);
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

                let condition_reg = self.expression_to_register_map[&condition.hir_id.local_id];
                self.block_map[last_inserted_condition_block]
                    .instructions
                    .push(lir::Instruction::Branch {
                        condition: lir::Operand::Register(condition_reg),
                        positive: body_block_id,
                        negative: end_block_id,
                    });
                self.block_map[body_block_id]
                    .predecessors
                    .insert(last_inserted_condition_block);
                self.block_map[end_block_id]
                    .predecessors
                    .insert(last_inserted_condition_block);

                // TODO: add break predecessors to end block

                self.block_stack.pop_back();
                self.block_stack.push_back(end_block_id);
            }
            hir::ExpressionKind::Assignment { lhs, rhs } => {
                // there are several different cases here. for assigning into a
                // local, we can just use a move, for assigning into a field, we
                // need to get the element ptr and do a memory store op, for
                // assigning into an array index, we need to get the element ptr
                // and do a store, for a deref assignment, we need to do a
                // memory store op.

                match &lhs.kind {
                    hir::ExpressionKind::Path(path) => match path.resolution() {
                        hir::Resolution::Definition(hir::DefinitionKind::Static, _) => {
                            self.visit_expression(rhs.clone());

                            let rhs = self.expression_to_register_map[&rhs.hir_id.local_id];

                            self.push_instruction(lir::Instruction::StoreMem {
                                destination: lir::Operand::Immediate(
                                    lir::Immediate::NamedStaticLabel(path.as_local_symbol()),
                                ),
                                source: lir::Operand::Register(rhs),
                            });
                        }
                        hir::Resolution::Local(_) => {
                            hir::visit::walk_expression(self, expression.clone());

                            let lhs = self.expression_to_register_map[&lhs.hir_id.local_id];
                            let rhs = self.expression_to_register_map[&rhs.hir_id.local_id];

                            self.push_instruction(lir::Instruction::Move {
                                destination: lhs,
                                source: lir::Operand::Register(rhs),
                            });
                        }
                        _ => unreachable!("illegal path in lhs of assignment"),
                    },
                    hir::ExpressionKind::FieldAccess {
                        target,
                        name,
                        is_method_call: false,
                    } => {
                        let mut target = target;
                        let target_ty = self.type_map.get_type(target.hir_id);

                        if let hir::ExpressionKind::Unary {
                            operator: UnaryOperatorKind::Deref,
                            operand,
                        } = &target.kind
                            && target_ty.is_struct()
                        {
                            target = operand;
                        }

                        self.visit_expression(target.clone());
                        self.visit_expression(rhs.clone());

                        let ty::TypeKind::Struct { fields, .. } = &*target_ty else {
                            unreachable!("{target_ty}")
                        };

                        let field_index =
                            fields.iter().position(|f| f.name == name.symbol).unwrap();

                        let lir::Type::Struct(structure_ty) = self.lower_type(target_ty) else {
                            unreachable!()
                        };

                        let struct_ptr_reg =
                            self.expression_to_register_map[&target.hir_id.local_id];
                        let rhs = self.expression_to_register_map[&rhs.hir_id.local_id];

                        assert_eq!(
                            self.register_map[struct_ptr_reg].ty,
                            lir::Type::Pointer,
                            "{} => {target:#?}",
                            name.symbol.value()
                        );

                        let element_ptr_reg =
                            self.create_register_with_lir_type(lir::Type::Pointer);

                        self.push_instruction(lir::Instruction::GetStructElementPointer {
                            destination: element_ptr_reg,
                            source: lir::Operand::Register(struct_ptr_reg),
                            ty: structure_ty,
                            index: field_index,
                        });

                        self.push_instruction(lir::Instruction::StoreMem {
                            destination: lir::Operand::Register(element_ptr_reg),
                            source: lir::Operand::Register(rhs),
                        });
                    }
                    hir::ExpressionKind::Unary {
                        operator: UnaryOperatorKind::Deref,
                        operand,
                    } => {
                        self.visit_expression(operand.clone());
                        self.visit_expression(rhs.clone());

                        let ptr_reg = self.expression_to_register_map[&operand.hir_id.local_id];
                        let rhs = self.expression_to_register_map[&rhs.hir_id.local_id];

                        self.push_instruction(lir::Instruction::StoreMem {
                            destination: lir::Operand::Register(ptr_reg),
                            source: lir::Operand::Register(rhs),
                        });
                    }
                    _ => unreachable!("illegal lhs of assignment"),
                }
            }
            hir::ExpressionKind::OperatorAssignment { operator, lhs, rhs } => todo!(),
            hir::ExpressionKind::Break => todo!(),
            hir::ExpressionKind::Continue => todo!(),
            hir::ExpressionKind::Return(value) => {
                hir::visit::walk_expression(self, expression.clone());

                // If we're returning a struct, we need to copy all of it's
                // fields into the pointer stored in the sret register
                if let Some(v) = value.clone()
                    && let ty = self.type_map.get_type(v.hir_id)
                    && ty.is_aggregate()
                {
                    let dest_struct_ptr_reg = self
                        .struct_return
                        .expect("functions returning a struct should have an sret set");

                    self.lower_copy(
                        dest_struct_ptr_reg,
                        self.expression_to_register_map[&v.hir_id.local_id],
                        ty,
                    );
                    self.push_instruction(lir::Instruction::Return { value: None });
                    return;
                }

                let value = value
                    .as_ref()
                    .map(|e| self.expression_to_register_map[&e.hir_id.local_id])
                    .map(lir::Operand::Register);

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

    fn visit_path_segment(&mut self, segment: std::rc::Rc<hir::PathSegment>) {
        match &segment.resolution {
            hir::Resolution::Local(local_id) => {
                let src_reg = self.local_to_register_map[local_id];

                // if we have a destination register, make a copy into it
                if let Some(dest_reg) = self.destination_register {
                    let ty = self.type_map.get_type(segment.hir_id);
                    self.lower_copy(dest_reg, src_reg, ty);

                    self.expression_to_register_map
                        .insert(segment.hir_id.local_id, dest_reg);
                } else {
                    self.expression_to_register_map
                        .insert(segment.hir_id.local_id, src_reg);
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
                    .node()
                    .as_item()
                    .unwrap()
                    .kind
                else {
                    unreachable!()
                };

                let ty = self.type_map.get_type(ty.hir_id);

                // FIXME: perform copy here if value is an aggregate type
                if ty.is_aggregate() {
                    todo!()
                }

                let destination_reg = self.create_register(ty);

                self.push_instruction(lir::Instruction::LoadMem {
                    destination: destination_reg,
                    source: lir::Operand::Immediate(lir::Immediate::NamedStaticLabel(name.symbol)),
                });

                self.expression_to_register_map
                    .insert(segment.hir_id.local_id, destination_reg);
            }
            hir::Resolution::Definition(..)
            | hir::Resolution::IntrinsicFunction(..)
            | hir::Resolution::Primitive(..) => {}
        }
    }

    fn visit_block(&mut self, block: Rc<hir::Block>, _context: hir::visit::BlockContext) {
        // hir::visit::walk_block(self, block.clone());

        for statement in block.statements.iter() {
            self.with_destination(None, |this| this.visit_statement(statement.clone()));
        }

        if let Some(e) = &block.expression {
            self.visit_expression(e.clone());
        }

        if let Some(e) = &block.expression {
            let ty = self.type_map.get_type(e.hir_id);
            if ty.is_unit() || ty.is_never() {
                return;
            }

            let reg = self.expression_to_register_map[&e.hir_id.local_id];

            self.expression_to_register_map
                .insert(block.hir_id.local_id, reg);
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
        let item = module.get_owner(owner_id).node().as_item().unwrap();

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
                    local_to_register_map: BTreeMap::new(),
                    expression_to_register_map: BTreeMap::new(),
                    destination_register: None,
                };

                let hir::OwnerNode::Item(item) = module.get_owner(owner_id).node();
                hir::visit::walk_item(&mut ctx, item);

                function_definitions.insert(owner_id, ctx.into_output());
            }
            hir::ItemKind::Struct { .. } | hir::ItemKind::TypeAlias { .. } => continue,
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
                    local_to_register_map: BTreeMap::new(),
                    expression_to_register_map: BTreeMap::new(),
                    destination_register: None,
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
