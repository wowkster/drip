//! Trait definition for an AST visitor which walks the tree in DFS order

use super::{
    Block, Expression, ExpressionKind, FunctionCallArgumentList, FunctionDefinition,
    FunctionParameter, FunctionParameterList, FunctionSignature, Identifier, Item, ItemKind,
    Literal, Local, LocalKind, Module, QualifiedIdentifier, Statement, StatementKind, Type,
    TypeAlias, TypeKind,
};
use crate::{
    frontend::ast::{
        ArrayInitializer, Static, StructDefinition, StructField, StructInitializerField,
    },
    middle::resolve::Namespace,
};

pub trait Visitor<'ast>: Sized {
    fn visit_item(&mut self, item: &'ast Item) {
        walk_item(self, item)
    }

    fn visit_function_definition(&mut self, function: &'ast FunctionDefinition) {
        walk_function_definition(self, function)
    }

    fn visit_function_signature(&mut self, signature: &'ast FunctionSignature) {
        walk_function_signature(self, signature)
    }

    fn visit_function_parameter_list(&mut self, parameters: &'ast FunctionParameterList) {
        walk_function_parameter_list(self, parameters)
    }

    fn visit_function_parameter(&mut self, parameter: &'ast FunctionParameter) {
        walk_function_parameter(self, parameter)
    }

    fn visit_struct_definition(&mut self, struct_definition: &'ast StructDefinition) {
        walk_struct_definition(self, struct_definition)
    }

    fn visit_struct_field(&mut self, struct_field: &'ast StructField) {
        walk_struct_field(self, struct_field)
    }

    fn visit_type_alias(&mut self, type_alias: &'ast TypeAlias) {
        walk_type_alias(self, type_alias)
    }

    fn visit_static(&mut self, static_: &'ast Static) {
        walk_static(self, static_)
    }

    fn visit_identifier(&mut self, _identifier: &'ast Identifier) {}

    fn visit_type(&mut self, ty: &'ast Type) {
        walk_type(self, ty)
    }

    fn visit_qualified_identifier(
        &mut self,
        qualified_identifier: &'ast QualifiedIdentifier,
        _namespace: Namespace,
    ) {
        walk_qualified_identifier(self, qualified_identifier)
    }

    fn visit_block(&mut self, block: &'ast Block) {
        walk_block(self, block)
    }

    fn visit_statement(&mut self, statement: &'ast Statement) {
        walk_statement(self, statement)
    }

    fn visit_local(&mut self, local: &'ast Local) {
        walk_local(self, local)
    }

    fn visit_expression(&mut self, expression: &'ast Expression) {
        walk_expression(self, expression)
    }

    fn visit_struct_initializer_field(&mut self, field: &'ast StructInitializerField) {
        walk_struct_initializer_field(self, field)
    }

    fn visit_literal(&mut self, _literal: &'ast Literal) {}

    fn visit_function_call_argument_list(&mut self, arguments: &'ast FunctionCallArgumentList) {
        walk_function_call_argument_list(self, arguments)
    }
}

pub fn walk_module<'a>(visitor: &mut impl Visitor<'a>, module: &'a Module<'a>) {
    for item in &module.items {
        visitor.visit_item(item);
    }
}

pub fn walk_item<'a>(visitor: &mut impl Visitor<'a>, item: &'a Item) {
    match &item.kind {
        ItemKind::FunctionDefinition(function) => {
            visitor.visit_function_definition(function);
        }
        ItemKind::StructDefinition(struct_definition) => {
            visitor.visit_struct_definition(struct_definition);
        }
        ItemKind::TypeAlias(type_alias) => {
            visitor.visit_type_alias(type_alias);
        }
        ItemKind::Static(static_) => {
            visitor.visit_static(static_);
        }
    }
}

pub fn walk_function_definition<'a>(
    visitor: &mut impl Visitor<'a>,
    function: &'a FunctionDefinition,
) {
    visitor.visit_function_signature(&function.signature);
    visitor.visit_block(&function.body);
}

pub fn walk_function_signature<'a>(
    visitor: &mut impl Visitor<'a>,
    signature: &'a FunctionSignature,
) {
    visitor.visit_qualified_identifier(&signature.name, Namespace::Value);
    visitor.visit_function_parameter_list(&signature.parameters);

    if let Some(ty) = &signature.return_type {
        visitor.visit_type(ty)
    }
}

pub fn walk_function_parameter_list<'a>(
    visitor: &mut impl Visitor<'a>,
    parameters: &'a FunctionParameterList,
) {
    for parameter in &parameters.parameters {
        visitor.visit_function_parameter(parameter)
    }
}

pub fn walk_function_parameter<'a>(
    visitor: &mut impl Visitor<'a>,
    parameter: &'a FunctionParameter,
) {
    visitor.visit_identifier(&parameter.name);
    visitor.visit_type(&parameter.ty);
}

pub fn walk_struct_definition<'a>(
    visitor: &mut impl Visitor<'a>,
    struct_definition: &'a StructDefinition,
) {
    visitor.visit_identifier(&struct_definition.name);

    for field in &struct_definition.fields {
        visitor.visit_struct_field(field);
    }
}

pub fn walk_struct_field<'a>(visitor: &mut impl Visitor<'a>, field: &'a StructField) {
    visitor.visit_identifier(&field.name);
    visitor.visit_type(&field.ty);
}

pub fn walk_type_alias<'a>(visitor: &mut impl Visitor<'a>, alias: &'a TypeAlias) {
    visitor.visit_identifier(&alias.name);
    visitor.visit_type(&alias.ty);
}

pub fn walk_static<'a>(visitor: &mut impl Visitor<'a>, static_: &'a Static) {
    visitor.visit_identifier(&static_.name);
    visitor.visit_type(&static_.ty);
    visitor.visit_expression(&static_.initializer);
}

pub fn walk_type<'a>(visitor: &mut impl Visitor<'a>, ty: &'a Type) {
    match &ty.kind {
        TypeKind::QualifiedIdentifier(qualified_identifier) => {
            visitor.visit_qualified_identifier(qualified_identifier, Namespace::Type)
        }
        TypeKind::Pointer(ty) => visitor.visit_type(ty),
        TypeKind::Slice(ty) => visitor.visit_type(ty),
        TypeKind::Array { ty, .. } => visitor.visit_type(ty),
        TypeKind::Tuple(tys) => {
            for ty in tys.iter() {
                visitor.visit_type(ty);
            }
        }
        TypeKind::Unit | TypeKind::Any => {}
    }
}

pub fn walk_qualified_identifier<'a>(
    visitor: &mut impl Visitor<'a>,
    qualified_identifier: &'a QualifiedIdentifier,
) {
    for segment in &qualified_identifier.segments {
        visitor.visit_identifier(segment);
    }
}

pub fn walk_block<'a>(visitor: &mut impl Visitor<'a>, block: &'a Block) {
    for statement in &block.statements {
        visitor.visit_statement(statement);
    }
}

pub fn walk_statement<'a>(visitor: &mut impl Visitor<'a>, statement: &'a Statement) {
    match &statement.kind {
        StatementKind::Local(local) => visitor.visit_local(local),
        StatementKind::BareExpr(expression) => visitor.visit_expression(expression),
        StatementKind::SemiExpr(expression) => visitor.visit_expression(expression),
        StatementKind::Empty => {}
    }
}

pub fn walk_local<'a>(visitor: &mut impl Visitor<'a>, local: &'a Local) {
    visitor.visit_identifier(&local.name);

    if let Some(ty) = &local.ty {
        visitor.visit_type(ty);
    }

    match &local.kind {
        LocalKind::Declaration => {}
        LocalKind::Initialization(expression) => visitor.visit_expression(expression),
    }
}

pub fn walk_expression<'a>(visitor: &mut impl Visitor<'a>, expression: &'a Expression) {
    match &expression.kind {
        ExpressionKind::Literal(literal) => visitor.visit_literal(literal),
        ExpressionKind::QualifiedIdentifier(qualified_identifier) => {
            visitor.visit_qualified_identifier(qualified_identifier, Namespace::Value)
        }
        ExpressionKind::This => {}
        ExpressionKind::Grouping(expression) => visitor.visit_expression(expression),
        ExpressionKind::Tuple(expressions) => {
            expressions.iter().for_each(|e| visitor.visit_expression(e))
        }
        ExpressionKind::Array(array_initializer) => match array_initializer.as_ref() {
            ArrayInitializer::Repeated { value, length } => {
                visitor.visit_expression(value);
                visitor.visit_literal(length);
            }
            ArrayInitializer::Specific(expressions) => {
                expressions.iter().for_each(|e| visitor.visit_expression(e))
            }
        },
        ExpressionKind::Struct { name, fields } => {
            visitor.visit_qualified_identifier(name, Namespace::Type);
            fields
                .iter()
                .for_each(|e| visitor.visit_struct_initializer_field(e))
        }
        ExpressionKind::Block(block) => visitor.visit_block(block),
        ExpressionKind::FieldAccess { target, name, .. } => {
            visitor.visit_expression(target);
            visitor.visit_identifier(name);
        }
        ExpressionKind::FunctionCall { target, arguments } => {
            visitor.visit_expression(target);
            visitor.visit_function_call_argument_list(arguments);
        }
        ExpressionKind::Binary { lhs, rhs, .. } => {
            visitor.visit_expression(lhs);
            visitor.visit_expression(rhs);
        }
        ExpressionKind::Unary { operand, .. } => visitor.visit_expression(operand),
        ExpressionKind::Cast { expression, ty } => {
            visitor.visit_expression(expression);
            visitor.visit_type(ty);
        }
        ExpressionKind::If {
            condition,
            positive,
            negative,
        } => {
            visitor.visit_expression(condition);
            visitor.visit_block(positive);

            if let Some(n) = &negative {
                visitor.visit_expression(n);
            }
        }
        ExpressionKind::While { condition, block } => {
            visitor.visit_expression(condition);
            visitor.visit_block(block);
        }
        ExpressionKind::Assignment { lhs, rhs } => {
            visitor.visit_expression(lhs);
            visitor.visit_expression(rhs);
        }
        ExpressionKind::OperatorAssignment { lhs, rhs, .. } => {
            visitor.visit_expression(lhs);
            visitor.visit_expression(rhs);
        }
        ExpressionKind::Break => {}
        ExpressionKind::Continue => {}
        ExpressionKind::Return(expression) => {
            if let Some(e) = &expression {
                visitor.visit_expression(e)
            }
        }
    }
}

pub fn walk_struct_initializer_field<'a>(
    visitor: &mut impl Visitor<'a>,
    field: &'a StructInitializerField,
) {
    visitor.visit_identifier(&field.name);
    visitor.visit_expression(&field.value);
}

pub fn walk_function_call_argument_list<'a>(
    visitor: &mut impl Visitor<'a>,
    arguments: &'a FunctionCallArgumentList,
) {
    for argument in &arguments.arguments {
        visitor.visit_expression(argument)
    }
}
