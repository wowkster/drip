use std::panic::Location;

use super::{
    ast::{AssignmentOperator, Item, ItemKind, NodeId},
    intern::InternedSymbol,
};
use crate::frontend::{
    SourceFile,
    ast::{
        ArrayInitializer, AssignmentOperatorKind, BinaryOperator, BinaryOperatorKind, Block,
        EnumDefinition, EnumVariant, Expression, ExpressionKind, FunctionCallArgumentList,
        FunctionDefinition, FunctionParameter, FunctionParameterList, FunctionSignature,
        Identifier, Literal, LiteralKind, Local, LocalKind, Module, QualifiedIdentifier,
        SelfParameter, Statement, StatementKind, Static, StructDefinition, StructField,
        StructInitializerField, Type, TypeAlias, TypeKind, UnaryOperator, UnaryOperatorKind,
        Visibility,
    },
    lexer::{Keyword, Lexer, Span, Token, TokenKind},
};

#[derive(Debug)]
pub struct Parser<'source> {
    lexer: Lexer<'source>,
    next_node_id: u32,
}

impl<'source> Parser<'source> {
    pub fn parse_module(source_file: &'source SourceFile) -> Module<'source> {
        let mut parser = Self {
            lexer: Lexer::new(source_file),
            next_node_id: 0,
        };

        let mut module = Module {
            source_file,
            items: Vec::new(),
        };

        while !parser.lexer.is_eof() && parser.lexer.peek().is_some() {
            module.items.push(parser.parse_module_item());
        }

        module
    }

    fn create_node_id(&mut self) -> NodeId {
        let id = NodeId(self.next_node_id);
        self.next_node_id += 1;
        id
    }

    #[track_caller]
    fn report_fatal_error(&self, offending_span: Span, message: &str) -> ! {
        #[cfg(feature = "error-backtrace")]
        eprintln!("error backtrace: {}", Location::caller());

        eprintln!(
            "{} (at {})",
            message,
            self.lexer.source().format_span_position(offending_span)
        );
        self.lexer.source().highlight_span(offending_span);
        std::process::exit(1);
    }

    #[track_caller]
    fn report_fatal_error_old(&self, message: &str) -> ! {
        #[cfg(feature = "error-backtrace")]
        eprintln!("error backtrace: {}", Location::caller());

        eprintln!(
            "Fatal error reported in Parser at {}:{}:{}:",
            self.lexer.source().origin,
            self.lexer.line_number() + 1,
            self.lexer.column() + 1
        );
        eprintln!("{message}");
        std::process::exit(1);
    }

    fn expect_peek(&mut self, expecting: &str) -> Token {
        let Some(token) = self.lexer.peek() else {
            self.report_fatal_error_old(&format!("Expected {expecting} but reached end of file",))
        };

        token
    }

    #[track_caller]
    fn expect_peek_to_be(&mut self, kind: TokenKind) -> Token {
        let token = self.expect_peek(&format!("{kind:?}"));

        if token.kind != kind {
            self.report_fatal_error_old(&format!(
                "Expected {:?} but found {:?} ({})",
                kind,
                token.kind,
                self.lexer.source().value_of_span(token.span)
            ))
        }

        token
    }

    fn expect_next(&mut self, expecting: &str) -> Token {
        let Some(token) = self.lexer.next() else {
            self.report_fatal_error_old(&format!("Expected {expecting} but reached end of file",))
        };

        token
    }

    #[track_caller]
    fn expect_next_to_be(&mut self, kind: TokenKind) -> Token {
        let token = self.expect_next(&format!("{kind:?}"));

        if token.kind != kind {
            self.report_fatal_error_old(&format!(
                "Expected {:?} but found {:?} ({})",
                kind,
                token.kind,
                self.lexer.source().value_of_span(token.span)
            ))
        }

        token
    }

    #[track_caller]
    fn expect_keyword(&mut self, keyword: Keyword) -> Token {
        self.expect_next_to_be(TokenKind::Keyword(keyword))
    }

    fn parse_module_item(&mut self) -> Item {
        let Some(peeked) = self.lexer.peek() else {
            self.report_fatal_error_old("Unexpected EOF while trying to parse module item")
        };

        match peeked.kind {
            TokenKind::Keyword(Keyword::Fn) => {
                let function = Box::new(self.parse_function_definition());

                Item {
                    id: self.create_node_id(),
                    span: function.span,
                    kind: ItemKind::FunctionDefinition(function),
                }
            }
            TokenKind::Keyword(Keyword::Struct) => {
                let structure = Box::new(self.parse_struct_definition());

                Item {
                    id: self.create_node_id(),
                    span: structure.span,
                    kind: ItemKind::StructDefinition(structure),
                }
            }
            TokenKind::Keyword(Keyword::Enum) => {
                let enumeration = Box::new(self.parse_enum_definition());

                Item {
                    id: self.create_node_id(),
                    span: enumeration.span,
                    kind: ItemKind::EnumDefinition(enumeration),
                }
            }
            TokenKind::Keyword(Keyword::Type) => {
                let type_alias = Box::new(self.parse_type_alias());

                Item {
                    id: self.create_node_id(),
                    span: type_alias.span,
                    kind: ItemKind::TypeAlias(type_alias),
                }
            }
            TokenKind::Keyword(Keyword::Static) => {
                let static_ = Box::new(self.parse_static());

                Item {
                    id: self.create_node_id(),
                    span: static_.span,
                    kind: ItemKind::Static(static_),
                }
            }

            _ => self.report_fatal_error(
                peeked.span,
                &format!(
                    "Expected item in module but found: {} ({:?})",
                    self.lexer.source().value_of_span(peeked.span),
                    peeked.kind
                ),
            ),
        }
    }

    /// fn name(param: ty) -> return_type {}
    fn parse_function_definition(&mut self) -> FunctionDefinition {
        let fn_keyword = self.expect_keyword(Keyword::Fn);

        let signature = self.parse_function_signature();
        let body = self.parse_block();

        FunctionDefinition {
            id: self.create_node_id(),
            span: Span::new(fn_keyword.span.start, body.span.end),
            visibility: Visibility::Private,
            signature,
            body,
        }
    }

    /// name(param: ty) -> return_type
    fn parse_function_signature(&mut self) -> FunctionSignature {
        let name = self.parse_qualified_identifier();
        let parameters = self.parse_function_parameter_list();

        let return_type = (self.expect_peek("arrow or opening brace").kind == TokenKind::Arrow)
            .then(|| {
                self.expect_next_to_be(TokenKind::Arrow);
                self.parse_type()
            });

        let span = Span::new(
            name.span.start,
            return_type
                .as_ref()
                .map(|return_type| return_type.span.end)
                .unwrap_or(parameters.span.end),
        );

        FunctionSignature {
            id: self.create_node_id(),
            span,
            name,
            parameters,
            return_type: return_type.map(Box::new),
        }
    }

    // (argc: usize, argv: &[str])
    // (*self, argc: usize, argv: &[str])
    fn parse_function_parameter_list(&mut self) -> FunctionParameterList {
        let mut self_parameter = None;
        let mut parameters = Vec::new();

        let open_paren = self.expect_next_to_be(TokenKind::OpenParen);

        // If the next token is not a closing paren, try parsing function
        // parameters
        if self.expect_peek("function parameter or closing paren").kind != TokenKind::CloseParen {
            let next = self.expect_peek("identifier or self parameter");

            if next.kind == TokenKind::Keyword(Keyword::This) {
                self_parameter = Some(SelfParameter::Owned)
            } else if next.kind == TokenKind::Asterisk {
                self.expect_next_to_be(TokenKind::Asterisk);

                let is_mutable = if self.expect_peek("mut keyword or self keyword").kind
                    == TokenKind::Keyword(Keyword::Mut)
                {
                    self.expect_keyword(Keyword::Mut);
                    true
                } else {
                    false
                };

                self.expect_keyword(Keyword::This);

                self_parameter = Some(SelfParameter::Pointer { is_mutable })
            }

            if self_parameter.is_some()
                && self.expect_peek("comma or closing paren").kind != TokenKind::CloseParen
            {
                self.expect_next_to_be(TokenKind::Comma);
            }

            // FIXME: change this to the same way struct literals are parsed

            if self.expect_peek("function parameter or closing paren").kind != TokenKind::CloseParen
            {
                // If a close paren was not found then there MUST be at least one
                // parameter
                parameters.push(self.parse_function_parameter());

                // While the next token is a comma try and parse more parameters
                while self
                    .lexer
                    .peek()
                    .is_some_and(|t| t.kind == TokenKind::Comma)
                {
                    self.expect_next_to_be(TokenKind::Comma);
                    parameters.push(self.parse_function_parameter());
                }
            }
        }

        let close_paren = self.expect_next_to_be(TokenKind::CloseParen);

        FunctionParameterList {
            id: self.create_node_id(),
            span: Span::new(open_paren.span.start, close_paren.span.end),
            self_parameter,
            parameters,
        }
    }

    // argc: usize
    fn parse_function_parameter(&mut self) -> FunctionParameter {
        let name = self.parse_identifier();
        self.expect_next_to_be(TokenKind::Colon);
        let ty = self.parse_type();

        FunctionParameter {
            id: self.create_node_id(),
            span: Span::new(name.span.start, ty.span.end),
            name,
            ty: Box::new(ty),
        }
    }

    fn parse_struct_definition(&mut self) -> StructDefinition {
        let struct_keyword = self.expect_keyword(Keyword::Struct);
        let name = self.parse_identifier();

        let mut fields = Vec::new();

        self.expect_next_to_be(TokenKind::OpenBrace);

        // If the next token is not a closing paren, try parsing function
        // parameters
        if self.expect_peek("function parameter or closing brace").kind != TokenKind::CloseBrace {
            // If a close paren was not found then there MUST be at least one
            // parameter
            fields.push(self.parse_struct_field());

            // While the next token is a comma try and parse more parameters
            while self
                .lexer
                .peek()
                .is_some_and(|t| t.kind == TokenKind::Comma)
            {
                self.expect_next_to_be(TokenKind::Comma);

                // Allow trailing commas
                if self.expect_peek("struct field or comma").kind == TokenKind::CloseBrace {
                    break;
                }

                fields.push(self.parse_struct_field());
            }
        }

        let closing_brace = self.expect_next_to_be(TokenKind::CloseBrace);

        StructDefinition {
            id: self.create_node_id(),
            span: Span::new(struct_keyword.span.start, closing_brace.span.end),
            visibility: Visibility::Private,
            name,
            fields,
        }
    }

    // field: i32
    fn parse_struct_field(&mut self) -> StructField {
        let name = self.parse_identifier();
        self.expect_next_to_be(TokenKind::Colon);
        let ty = self.parse_type();

        StructField {
            id: self.create_node_id(),
            span: Span::new(name.span.start, ty.span.end),
            visibility: Visibility::Private,
            name,
            ty: Box::new(ty),
        }
    }

    fn parse_enum_definition(&mut self) -> EnumDefinition {
        let enum_keyword = self.expect_keyword(Keyword::Enum);
        let name = self.parse_identifier();

        let mut variants = Vec::new();

        self.expect_next_to_be(TokenKind::OpenBrace);

        // If the next token is not a closing paren, try parsing function
        // parameters
        if self.expect_peek("function parameter or closing brace").kind != TokenKind::CloseBrace {
            // If a close paren was not found then there MUST be at least one
            // parameter
            let variant_name = self.parse_identifier();
            variants.push(EnumVariant {
                id: self.create_node_id(),
                span: variant_name.span,
                name: variant_name,
            });

            // While the next token is a comma try and parse more parameters
            while self
                .lexer
                .peek()
                .is_some_and(|t| t.kind == TokenKind::Comma)
            {
                self.expect_next_to_be(TokenKind::Comma);

                // Allow trailing commas
                if self.expect_peek("enum member or comma").kind == TokenKind::CloseBrace {
                    break;
                }

                let variant_name = self.parse_identifier();
                variants.push(EnumVariant {
                    id: self.create_node_id(),
                    span: variant_name.span,
                    name: variant_name,
                });
            }
        }

        let closing_brace = self.expect_next_to_be(TokenKind::CloseBrace);

        EnumDefinition {
            id: self.create_node_id(),
            span: Span::new(enum_keyword.span.start, closing_brace.span.end),
            visibility: Visibility::Private,
            name,
            variants,
        }
    }

    // type A = i32;
    fn parse_type_alias(&mut self) -> TypeAlias {
        let type_keyword = self.expect_keyword(Keyword::Type);
        let name = self.parse_identifier();
        self.expect_next_to_be(TokenKind::Equals);
        let ty = self.parse_type();
        let semi = self.expect_next_to_be(TokenKind::Semicolon);

        TypeAlias {
            id: self.create_node_id(),
            span: Span::new(type_keyword.span.start, semi.span.end),
            visibility: Visibility::Private,
            name,
            ty: Box::new(ty),
        }
    }

    // static mut A: i32 = 0;
    fn parse_static(&mut self) -> Static {
        let static_keyword = self.expect_keyword(Keyword::Static);

        let is_mutable = if self.expect_peek("mut keyword or identifier").kind
            == TokenKind::Keyword(Keyword::Mut)
        {
            self.expect_keyword(Keyword::Mut);
            true
        } else {
            false
        };

        let name = self.parse_identifier();
        self.expect_next_to_be(TokenKind::Colon);
        let ty = self.parse_type();
        self.expect_next_to_be(TokenKind::Equals);
        let initializer = self.parse_expression();
        let semi = self.expect_next_to_be(TokenKind::Semicolon);

        Static {
            id: self.create_node_id(),
            span: Span::new(static_keyword.span.start, semi.span.end),
            visibility: Visibility::Private,
            is_mutable,
            name,
            ty: Box::new(ty),
            initializer: Box::new(initializer),
        }
    }

    // main
    fn parse_identifier(&mut self) -> Identifier {
        let token = self.expect_next_to_be(TokenKind::Identifier);

        Identifier {
            id: self.create_node_id(),
            span: token.span,
            symbol: InternedSymbol::new(self.lexer.source().value_of_span(token.span)),
        }
    }

    // std::fs::read_to_string
    fn parse_qualified_identifier(&mut self) -> QualifiedIdentifier {
        // FIXME: rust-analyzer bug causing a false unsafe report??
        #[allow(unused_unsafe)]
        let mut segments = unsafe { vec![self.parse_identifier()] };

        // While the next token is a double colon try and parse more segments
        while self
            .lexer
            .peek()
            .is_some_and(|t| t.kind == TokenKind::DoubleColon)
        {
            self.expect_next_to_be(TokenKind::DoubleColon);
            segments.push(self.parse_identifier());
        }

        QualifiedIdentifier {
            id: self.create_node_id(),
            span: Span::new(
                segments.first().unwrap().span.start,
                segments.last().unwrap().span.end,
            ),
            segments,
        }
    }

    // type = "*" ( "mut" )? ( "any" | type )
    //        | "[" type ( ";" INTEGER )?  "]"
    //        | "(" type ( "," type )*  ")"
    //        | "fn" "(" ( type ( "," type )* )? ( "," "..." "[" type "]" ) ")" ( "->" type )?
    //        | PRIMITIVE | "str" | "cstr"
    //        | IDENTIFIER
    fn parse_type(&mut self) -> Type {
        // Raw pointers and `any` pointers
        if self
            .expect_peek("asterisk, open bracket, open paren, fn keyword, or identifier")
            .kind
            == TokenKind::Asterisk
        {
            let asterisk = self.expect_next_to_be(TokenKind::Asterisk);

            let maybe_mut_or_any = self.expect_peek("open bracket, keyword, or identifier");

            let maybe_any = if maybe_mut_or_any.kind == TokenKind::Keyword(Keyword::Mut) {
                let _mut = self.expect_next_to_be(TokenKind::Keyword(Keyword::Mut));

                self.expect_peek("open bracket, or identifier")
            } else {
                maybe_mut_or_any
            };

            if maybe_any.kind == TokenKind::Identifier
                && self.lexer.source().value_of_span(maybe_any.span) == "any"
            {
                let any = self.expect_next_to_be(TokenKind::Identifier);

                return Type {
                    id: self.create_node_id(),
                    span: Span::new(asterisk.span.start, any.span.end),
                    kind: TypeKind::Any,
                };
            } else {
                let ty = self.parse_type();

                return Type {
                    id: self.create_node_id(),
                    span: Span::new(asterisk.span.start, ty.span.end),
                    kind: TypeKind::Pointer(Box::new(ty)),
                };
            }
        }

        // Slices and Arrays

        if self
            .expect_peek("open bracket, open paren, fn keyword, or identifier")
            .kind
            == TokenKind::OpenBracket
        {
            let open_bracket = self.expect_next_to_be(TokenKind::OpenBracket);
            let ty = self.parse_type();

            if self.expect_peek("semicolon or close bracket").kind == TokenKind::Semicolon {
                self.expect_next_to_be(TokenKind::Semicolon);
                let length = self.parse_literal();

                // if length.kind != LiteralKind::Integer {
                //     // TODO: allow constant expressions
                //     self.report_fatal_error(length.span, "Array length must be an integer literal")
                // }

                let close_bracket = self.expect_next_to_be(TokenKind::CloseBracket);

                return Type {
                    id: self.create_node_id(),
                    span: Span::new(open_bracket.span.start, close_bracket.span.end),
                    kind: TypeKind::Array {
                        ty: Box::new(ty),
                        length: Box::new(length),
                    },
                };
            }

            let close_bracket = self.expect_next_to_be(TokenKind::CloseBracket);

            return Type {
                id: self.create_node_id(),
                span: Span::new(open_bracket.span.start, close_bracket.span.end),
                kind: TypeKind::Slice(Box::new(ty)),
            };
        }

        // Unit & Tuples

        if self
            .expect_peek("open paren, fn keyword, or identifier")
            .kind
            == TokenKind::OpenParen
        {
            let open_paren = self.expect_next_to_be(TokenKind::OpenParen);

            // Parse unit type `()`
            if self.expect_peek("close paren").kind == TokenKind::CloseParen {
                let close_paren = self.expect_next_to_be(TokenKind::CloseParen);

                return Type {
                    id: self.create_node_id(),
                    span: Span::new(open_paren.span.start, close_paren.span.end),
                    kind: TypeKind::Unit,
                };
            }

            let mut types = Vec::new();

            // If a close paren was not found then there MUST be at least one
            // parameter
            types.push(self.parse_type());

            // While the next token is a comma try and parse more parameters
            while self
                .lexer
                .peek()
                .is_some_and(|t| t.kind == TokenKind::Comma)
            {
                self.expect_next_to_be(TokenKind::Comma);
                types.push(self.parse_type());
            }

            let close_paren = self.expect_next_to_be(TokenKind::CloseParen);

            return Type {
                id: self.create_node_id(),
                span: Span::new(open_paren.span.start, close_paren.span.end),
                kind: TypeKind::Tuple(types.into()),
            };
        }

        // Function pointers

        if self.expect_peek("fn keyword or identifier").kind == TokenKind::Keyword(Keyword::Fn) {
            todo!("Parse function pointer type")
        }

        // Anything else must be a qualified identifier

        let qualified_identifier = self.parse_qualified_identifier();

        Type {
            id: self.create_node_id(),
            span: qualified_identifier.span,
            kind: TypeKind::QualifiedIdentifier(qualified_identifier),
        }
    }

    // "{" ( statement )* "}"
    fn parse_block(&mut self) -> Block {
        let mut statements = Vec::new();

        let open_brace = self.expect_next_to_be(TokenKind::OpenBrace);

        // If the next token is not a closing brace, try parsing statements
        if self.expect_peek("function parameter or closing paren").kind != TokenKind::CloseBrace {
            // If a close brace was not found then there MUST be at least one
            // statement
            statements.push(self.parse_statement());

            // While the next token is a comma try and parse more parameters
            while !self
                .lexer
                .peek()
                .is_some_and(|t| t.kind == TokenKind::CloseBrace)
            {
                statements.push(self.parse_statement());
            }
        }

        let close_brace = self.expect_next_to_be(TokenKind::CloseBrace);

        Block {
            id: self.create_node_id(),
            span: Span::new(open_brace.span.start, close_brace.span.end),
            statements,
        }
    }

    fn parse_statement(&mut self) -> Statement {
        if self.expect_peek("let keyword or expression").kind == TokenKind::Keyword(Keyword::Let) {
            let local = self.parse_local();

            return Statement {
                id: self.create_node_id(),
                span: local.span,
                kind: StatementKind::Local(Box::new(local)),
            };
        }

        if self.expect_peek("expression").kind == TokenKind::Semicolon {
            let semicolon = self.expect_next_to_be(TokenKind::Semicolon);

            return Statement {
                id: self.create_node_id(),
                span: semicolon.span,
                kind: StatementKind::Empty,
            };
        }

        let expression = self.parse_expression();

        let peeked = self.expect_peek("semicolon or closing brace");

        // If the next token is not a semicolon, we need to perform some extra
        // checks: it has to be a closing brace (reached end of block) or we
        // need to have just parsed an expression with a block
        if peeked.kind != TokenKind::Semicolon {
            if peeked.kind != TokenKind::CloseBrace
                && !matches!(
                    expression.kind,
                    ExpressionKind::Block(_)
                        | ExpressionKind::If { .. }
                        | ExpressionKind::While { .. }
                )
            {
                self.report_fatal_error_old(&format!(
                    "Expected semicolon after statement but found {:?} ({})",
                    peeked.kind,
                    self.lexer.source().value_of_span(peeked.span),
                ))
            }

            return Statement {
                id: self.create_node_id(),
                span: expression.span,
                kind: StatementKind::BareExpr(Box::new(expression)),
            };
        }

        let semicolon = self.expect_next_to_be(TokenKind::Semicolon);

        Statement {
            id: self.create_node_id(),
            span: Span::new(expression.span.start, semicolon.span.end),
            kind: StatementKind::SemiExpr(Box::new(expression)),
        }
    }

    fn parse_local(&mut self) -> Local {
        let let_keyword = self.expect_keyword(Keyword::Let);

        let is_mutable = if self
            .expect_peek("mut keyword, type qualifier, or assignment operator")
            .kind
            == TokenKind::Keyword(Keyword::Mut)
        {
            self.expect_keyword(Keyword::Mut);
            true
        } else {
            false
        };

        let name = self.parse_identifier();

        let ty = if self.expect_peek("colon, equals, or semicolon").kind == TokenKind::Colon {
            self.expect_next_to_be(TokenKind::Colon);
            Some(self.parse_type())
        } else {
            None
        };

        let (span, kind) = if self.expect_peek("equals or semicolon").kind == TokenKind::Semicolon {
            let semicolon = self.expect_next_to_be(TokenKind::Semicolon);

            (
                Span::new(let_keyword.span.start, semicolon.span.end),
                LocalKind::Declaration,
            )
        } else {
            self.expect_next_to_be(TokenKind::Equals);

            let expression = self.parse_expression();
            let semicolon = self.expect_next_to_be(TokenKind::Semicolon);

            (
                Span::new(let_keyword.span.start, semicolon.span.end),
                LocalKind::Initialization(Box::new(expression)),
            )
        };

        Local {
            id: self.create_node_id(),
            span,
            is_mutable,
            name,
            ty,
            kind,
        }
    }

    /// expression     -> return
    /// return         -> ( "break" | "continue" )
    ///                   | "return" ( assignment )?
    ///                   | assignment
    /// assignment     -> logical_or ( ( "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&&=" | "||=" | "&=" | "|=" | "^=" | "<<=" | ">>=" ) assignment )*
    /// logical_or     -> logical_and ( "||" logical_and )*
    /// logical_and    -> comparison ( "&&" comparison )*
    /// comparison     -> bitwise_or ( ( "!=" | "==" | "<" | "<=" | ">" | ">=" ) bitwise_or )*
    /// bitwise_or     -> bitwise_xor ( "|" bitwise_xor )*
    /// bitwise_xor    -> bitwise_and ( "^" bitwise_and )*
    /// bitwise_and    -> bit_shift ( "&" bit_shift )*
    /// bit_shift      -> term ( ( "<<" | ">>" ) term )*
    /// term           -> factor ( ( "-" | "+" ) factor )*
    /// factor         -> cast ( ( "/" | "*" | "%" ) cast )*
    /// cast           -> unary ( "as" TYPE )*
    /// unary          -> ( "!" | "~" | "-" | "*" ) unary
    ///                   | function_call
    /// function_call  -> postfix ( "(" ( expression ( "," expression )* )? ")" )*
    /// postfix        -> block ( ( "." | "->" ) IDENTIFIER )*
    /// block          -> BLOCK
    ///                   | "if" expression BLOCK ( "else" expression )?
    ///                   | "while" expression BLOCK
    ///                   | atom
    /// atom           -> IDENTIFIER ( "{" ( ( IDENTIFIER ":" expression ) ( "," IDENTIFIER ":" expression )* )?  "}")?
    ///                   | NUMBER | STRING | BOOL
    ///                   | "(" expression ( "," expression )* ")"
    ///                   | "[" ( expression ( "," expression )* ( "," )? )? "]"
    ///                   | "[" expression ";" NUMBER "]"
    fn parse_expression(&mut self) -> Expression {
        // We start from the top and work our way down.

        if self.expect_peek("expression").kind == TokenKind::Keyword(Keyword::Break) {
            let break_keyword = self.expect_keyword(Keyword::Break);

            return Expression {
                id: self.create_node_id(),
                span: break_keyword.span,
                kind: ExpressionKind::Break,
            };
        }

        if self.expect_peek("expression").kind == TokenKind::Keyword(Keyword::Continue) {
            let continue_keyword = self.expect_keyword(Keyword::Continue);

            return Expression {
                id: self.create_node_id(),
                span: continue_keyword.span,
                kind: ExpressionKind::Continue,
            };
        }

        if self.expect_peek("expression").kind == TokenKind::Keyword(Keyword::Return) {
            let return_keyword = self.expect_keyword(Keyword::Return);

            let peeked = self.expect_peek("semicolon, closing brace, or expression");

            // Unless we are at the end of a block or have a semicolon we expect an expression to follow
            let expression = (peeked.kind != TokenKind::Semicolon
                && peeked.kind != TokenKind::CloseBrace)
                .then(|| self.parse_assignment_expression());

            return Expression {
                id: self.create_node_id(),
                span: Span::new(
                    return_keyword.span.start,
                    expression
                        .as_ref()
                        .map(|e| e.span.end)
                        .unwrap_or(return_keyword.span.end),
                ),
                kind: ExpressionKind::Return(expression.map(Box::new)),
            };
        }

        self.parse_assignment_expression()
    }

    fn parse_assignment_expression(&mut self) -> Expression {
        let mut expression = self.parse_logical_or_expression();

        while self
            .expect_peek("assignment operator or expression")
            .kind
            .is_assignment_operator()
        {
            let operator = self.parse_assignment_operator();
            let rhs = self.parse_assignment_expression();

            let span = Span::new(expression.span.start, rhs.span.end);

            // We know that the operator was either an "=" or a special
            // assignment operator, but the parse_assignment_operator function
            // returns None in the case of "=" so we can easily branch based on
            // that fact
            expression = if let Some(operator) = operator {
                Expression {
                    id: self.create_node_id(),
                    span,
                    kind: ExpressionKind::OperatorAssignment {
                        operator,
                        lhs: Box::new(expression),
                        rhs: Box::new(rhs),
                    },
                }
            } else {
                Expression {
                    id: self.create_node_id(),
                    span,
                    kind: ExpressionKind::Assignment {
                        lhs: Box::new(expression),
                        rhs: Box::new(rhs),
                    },
                }
            }
        }

        expression
    }

    fn parse_assignment_operator(&mut self) -> Option<AssignmentOperator> {
        let operator = self.expect_next("assignment operator");

        let kind = match operator.kind {
            TokenKind::PlusEquals => AssignmentOperatorKind::Add,
            TokenKind::MinusEquals => AssignmentOperatorKind::Subtract,
            TokenKind::MultiplyEquals => AssignmentOperatorKind::Multiply,
            TokenKind::DivideEquals => AssignmentOperatorKind::Divide,
            TokenKind::ModulusEquals => AssignmentOperatorKind::Modulus,
            TokenKind::LogicalAndEquals => AssignmentOperatorKind::LogicalAnd,
            TokenKind::LogicalOrEquals => AssignmentOperatorKind::LogicalOr,
            TokenKind::BitwiseXorEquals => AssignmentOperatorKind::BitwiseXor,
            TokenKind::BitwiseAndEquals => AssignmentOperatorKind::BitwiseAnd,
            TokenKind::BitwiseOrEquals => AssignmentOperatorKind::BitwiseOr,
            TokenKind::ShiftLeftEquals => AssignmentOperatorKind::ShiftLeft,
            TokenKind::ShiftRightEquals => AssignmentOperatorKind::ShiftRight,
            _ => return None,
        };

        Some(AssignmentOperator {
            id: self.create_node_id(),
            span: operator.span,
            kind,
        })
    }

    fn parse_logical_or_expression(&mut self) -> Expression {
        let mut expression = self.parse_logical_and_expression();

        while self.expect_peek("logical or operator or expression").kind == TokenKind::LogicalOr {
            let operator = self.expect_next_to_be(TokenKind::LogicalOr);
            let rhs = self.parse_logical_and_expression();

            expression = Expression {
                id: self.create_node_id(),
                span: Span::new(expression.span.start, rhs.span.end),
                kind: ExpressionKind::Binary {
                    lhs: Box::new(expression),
                    operator: BinaryOperator {
                        id: self.create_node_id(),
                        span: operator.span,
                        kind: BinaryOperatorKind::LogicalOr,
                    },
                    rhs: Box::new(rhs),
                },
            }
        }

        expression
    }

    fn parse_logical_and_expression(&mut self) -> Expression {
        let mut expression = self.parse_comparison_expression();

        while self.expect_peek("logical and operator or expression").kind == TokenKind::LogicalAnd {
            let operator = self.expect_next_to_be(TokenKind::LogicalAnd);
            let rhs = self.parse_comparison_expression();

            expression = Expression {
                id: self.create_node_id(),
                span: Span::new(expression.span.start, rhs.span.end),
                kind: ExpressionKind::Binary {
                    lhs: Box::new(expression),
                    operator: BinaryOperator {
                        id: self.create_node_id(),
                        span: operator.span,
                        kind: BinaryOperatorKind::LogicalAnd,
                    },
                    rhs: Box::new(rhs),
                },
            }
        }

        expression
    }

    fn parse_comparison_expression(&mut self) -> Expression {
        let mut expression = self.parse_bitwise_or_expression();

        while self
            .expect_peek("comparison operator or expression")
            .kind
            .is_comparison_operator()
        {
            let operator = self.parse_comparison_operator();
            let rhs = self.parse_bitwise_or_expression();

            expression = Expression {
                id: self.create_node_id(),
                span: Span::new(expression.span.start, rhs.span.end),
                kind: ExpressionKind::Binary {
                    lhs: Box::new(expression),
                    operator,
                    rhs: Box::new(rhs),
                },
            }
        }

        expression
    }

    fn parse_comparison_operator(&mut self) -> BinaryOperator {
        let operator = self.expect_next("comparison operator");

        BinaryOperator {
            id: self.create_node_id(),
            span: operator.span,
            kind: match operator.kind {
                TokenKind::NotEquals => BinaryOperatorKind::NotEquals,
                TokenKind::DoubleEquals => BinaryOperatorKind::Equals,
                TokenKind::LessThan => BinaryOperatorKind::LessThan,
                TokenKind::LessThanOrEqualTo => BinaryOperatorKind::LessThanOrEqualTo,
                TokenKind::GreaterThan => BinaryOperatorKind::GreaterThan,
                TokenKind::GreaterThanOrEqualTo => BinaryOperatorKind::GreaterThanOrEqualTo,
                _ => unreachable!(),
            },
        }
    }

    fn parse_bitwise_or_expression(&mut self) -> Expression {
        let mut expression = self.parse_bitwise_xor_expression();

        while self.expect_peek("bitwise or operator or expression").kind == TokenKind::BitwiseOr {
            let operator = self.expect_next_to_be(TokenKind::BitwiseOr);
            let rhs = self.parse_bitwise_xor_expression();

            expression = Expression {
                id: self.create_node_id(),
                span: Span::new(expression.span.start, rhs.span.end),
                kind: ExpressionKind::Binary {
                    lhs: Box::new(expression),
                    operator: BinaryOperator {
                        id: self.create_node_id(),
                        span: operator.span,
                        kind: BinaryOperatorKind::BitwiseOr,
                    },
                    rhs: Box::new(rhs),
                },
            }
        }

        expression
    }

    fn parse_bitwise_xor_expression(&mut self) -> Expression {
        let mut expression = self.parse_bitwise_and_expression();

        while self.expect_peek("bitwise xor operator or expression").kind == TokenKind::BitwiseXor {
            let operator = self.expect_next_to_be(TokenKind::BitwiseXor);
            let rhs = self.parse_bitwise_and_expression();

            expression = Expression {
                id: self.create_node_id(),
                span: Span::new(expression.span.start, rhs.span.end),
                kind: ExpressionKind::Binary {
                    lhs: Box::new(expression),
                    operator: BinaryOperator {
                        id: self.create_node_id(),
                        span: operator.span,
                        kind: BinaryOperatorKind::BitwiseXor,
                    },
                    rhs: Box::new(rhs),
                },
            }
        }

        expression
    }

    fn parse_bitwise_and_expression(&mut self) -> Expression {
        let mut expression = self.parse_bit_shift_expression();

        while self.expect_peek("bitwise and operator or expression").kind == TokenKind::Ampersand {
            let operator = self.expect_next_to_be(TokenKind::Ampersand);
            let rhs = self.parse_bit_shift_expression();

            expression = Expression {
                id: self.create_node_id(),
                span: Span::new(expression.span.start, rhs.span.end),
                kind: ExpressionKind::Binary {
                    lhs: Box::new(expression),
                    operator: BinaryOperator {
                        id: self.create_node_id(),
                        span: operator.span,
                        kind: BinaryOperatorKind::BitwiseAnd,
                    },
                    rhs: Box::new(rhs),
                },
            }
        }

        expression
    }

    fn parse_bit_shift_expression(&mut self) -> Expression {
        let mut expression = self.parse_term_expression();

        while self
            .expect_peek("bit shift operator or expression")
            .kind
            .is_bit_shift_operator()
        {
            let operator = self.parse_bit_shift_operator();
            let rhs = self.parse_term_expression();

            expression = Expression {
                id: self.create_node_id(),
                span: Span::new(expression.span.start, rhs.span.end),
                kind: ExpressionKind::Binary {
                    lhs: Box::new(expression),
                    operator,
                    rhs: Box::new(rhs),
                },
            }
        }

        expression
    }

    fn parse_bit_shift_operator(&mut self) -> BinaryOperator {
        let operator = self.expect_next("bit shift operator");

        BinaryOperator {
            id: self.create_node_id(),
            span: operator.span,
            kind: match operator.kind {
                TokenKind::ShiftLeft => BinaryOperatorKind::ShiftLeft,
                TokenKind::ShiftRight => BinaryOperatorKind::ShiftRight,
                _ => unreachable!(),
            },
        }
    }

    fn parse_term_expression(&mut self) -> Expression {
        let mut expression = self.parse_factor_expression();

        while self
            .expect_peek("term operator or expression")
            .kind
            .is_term_operator()
        {
            let operator = self.parse_term_operator();
            let rhs = self.parse_factor_expression();

            expression = Expression {
                id: self.create_node_id(),
                span: Span::new(expression.span.start, rhs.span.end),
                kind: ExpressionKind::Binary {
                    lhs: Box::new(expression),
                    operator,
                    rhs: Box::new(rhs),
                },
            }
        }

        expression
    }

    fn parse_term_operator(&mut self) -> BinaryOperator {
        let operator = self.expect_next("term operator");

        BinaryOperator {
            id: self.create_node_id(),
            span: operator.span,
            kind: match operator.kind {
                TokenKind::Plus => BinaryOperatorKind::Add,
                TokenKind::Minus => BinaryOperatorKind::Subtract,
                _ => unreachable!(),
            },
        }
    }

    fn parse_factor_expression(&mut self) -> Expression {
        let mut expression = self.parse_cast_expression();

        if self.expect_peek("factor operator or expression").kind == TokenKind::Asterisk
            && matches!(
                &expression.kind,
                ExpressionKind::If { .. } | ExpressionKind::While { .. } | ExpressionKind::Block(_)
            )
        {
            return expression;
        }

        while self
            .expect_peek("factor operator or expression")
            .kind
            .is_factor_operator()
        {
            let operator = self.parse_factor_operator();
            let rhs = self.parse_cast_expression();

            expression = Expression {
                id: self.create_node_id(),
                span: Span::new(expression.span.start, rhs.span.end),
                kind: ExpressionKind::Binary {
                    lhs: Box::new(expression),
                    operator,
                    rhs: Box::new(rhs),
                },
            }
        }

        expression
    }

    fn parse_factor_operator(&mut self) -> BinaryOperator {
        let operator = self.expect_next("factor operator");

        BinaryOperator {
            id: self.create_node_id(),
            span: operator.span,
            kind: match operator.kind {
                TokenKind::Asterisk => BinaryOperatorKind::Multiply,
                TokenKind::Divide => BinaryOperatorKind::Divide,
                TokenKind::Modulus => BinaryOperatorKind::Modulus,
                _ => unreachable!(),
            },
        }
    }

    fn parse_cast_expression(&mut self) -> Expression {
        let mut expression = self.parse_unary_expression();

        while self.expect_peek("as keyword or expression").kind == TokenKind::Keyword(Keyword::As) {
            self.expect_keyword(Keyword::As);
            let ty = self.parse_type();

            expression = Expression {
                id: self.create_node_id(),
                span: Span::new(expression.span.start, ty.span.end),
                kind: ExpressionKind::Cast {
                    expression: Box::new(expression),
                    ty: Box::new(ty),
                },
            }
        }

        expression
    }

    fn parse_unary_expression(&mut self) -> Expression {
        if self
            .expect_peek("as keyword or expression")
            .kind
            .is_unary_operator()
        {
            let operator = self.parse_unary_operator();

            let operand = self.parse_unary_expression();

            return Expression {
                id: self.create_node_id(),
                span: Span::new(operator.span.start, operand.span.end),
                kind: ExpressionKind::Unary {
                    operator,
                    operand: Box::new(operand),
                },
            };
        }

        self.parse_function_call_expression()
    }

    fn parse_unary_operator(&mut self) -> UnaryOperator {
        let operator = self.expect_next("unary operator");

        let kind = match operator.kind {
            TokenKind::Asterisk => UnaryOperatorKind::Deref,
            TokenKind::Ampersand => {
                let is_mutable = if self.expect_peek("mut keyword or expression").kind
                    == TokenKind::Keyword(Keyword::Mut)
                {
                    self.expect_keyword(Keyword::Mut);
                    true
                } else {
                    false
                };

                UnaryOperatorKind::AddressOf { is_mutable }
            }
            TokenKind::Bang => UnaryOperatorKind::LogicalNot,
            TokenKind::Tilde => UnaryOperatorKind::BitwiseNot,
            TokenKind::Minus => UnaryOperatorKind::Negate,
            _ => unreachable!("Unexpected unary operator"),
        };

        UnaryOperator {
            id: self.create_node_id(),
            span: operator.span,
            kind,
        }
    }

    fn parse_function_call_expression(&mut self) -> Expression {
        let mut expression = self.parse_postfix_expression();

        loop {
            let peek = self
                .expect_peek("open parenthesis, open bracket, semicolon, or closing brace")
                .kind;

            match peek {
                TokenKind::OpenParen => {
                    let arguments = self.parse_function_call_arguments();

                    if let ExpressionKind::FieldAccess { is_method_call, .. } = &mut expression.kind
                    {
                        *is_method_call = true;
                    }

                    expression = Expression {
                        id: self.create_node_id(),
                        span: Span::new(expression.span.start, arguments.span.end),
                        kind: ExpressionKind::FunctionCall {
                            target: Box::new(expression),
                            arguments: Box::new(arguments),
                        },
                    }
                }
                TokenKind::OpenBracket => {
                    let _open_paren = self.expect_next_to_be(TokenKind::OpenBracket);
                    let index = self.parse_expression();
                    let close_paren = self.expect_next_to_be(TokenKind::CloseBracket);

                    expression = Expression {
                        id: self.create_node_id(),
                        span: Span::new(expression.span.start, close_paren.span.end),
                        kind: ExpressionKind::Subscript {
                            target: Box::new(expression),
                            index: Box::new(index),
                        },
                    }
                }
                _ => break,
            }
        }

        expression
    }

    fn parse_function_call_arguments(&mut self) -> FunctionCallArgumentList {
        let mut arguments = Vec::new();

        let open_paren = self.expect_next_to_be(TokenKind::OpenParen);

        // If the next token is not a closing paren, try parsing function call
        // arguments
        if self
            .expect_peek("function call argument or closing paren")
            .kind
            != TokenKind::CloseParen
        {
            // If a close paren was not found then there MUST be at least one
            // argument
            arguments.push(self.parse_expression());

            // While the next token is a comma try and parse more parameters
            while self
                .lexer
                .peek()
                .is_some_and(|t| t.kind == TokenKind::Comma)
            {
                self.expect_next_to_be(TokenKind::Comma);
                arguments.push(self.parse_expression());
            }
        }

        let close_paren = self.expect_next_to_be(TokenKind::CloseParen);

        FunctionCallArgumentList {
            id: self.create_node_id(),
            span: Span::new(open_paren.span.start, close_paren.span.end),
            arguments,
        }
    }

    fn parse_postfix_expression(&mut self) -> Expression {
        let mut expression = self.parse_expression_with_block();

        while [TokenKind::Dot, TokenKind::Arrow].contains(
            &self
                .expect_peek("dot, arrow,open parenthesis, semicolon, or closing brace")
                .kind,
        ) {
            let token = self.expect_next("dot or arrow");
            let dereference = token.kind == TokenKind::Arrow;

            let name = self.parse_identifier();

            expression = Expression {
                id: self.create_node_id(),
                span: Span::new(expression.span.start, name.span.end),
                kind: ExpressionKind::FieldAccess {
                    target: Box::new(expression),
                    name,
                    dereference,
                    is_method_call: false,
                },
            }
        }

        expression
    }

    fn parse_expression_with_block(&mut self) -> Expression {
        if self
            .expect_peek("opening brace, if expression, while expression, or atomic expression")
            .kind
            == TokenKind::OpenBrace
        {
            return self.parse_block_expression();
        }

        if self
            .expect_peek("if expression, while expression, or atomic expression")
            .kind
            == TokenKind::Keyword(Keyword::If)
        {
            return self.parse_if_expression();
        }

        if self
            .expect_peek("while expression or atomic expression")
            .kind
            == TokenKind::Keyword(Keyword::While)
        {
            return self.parse_while_expression();
        }

        self.parse_atomic_expression()
    }

    fn parse_block_expression(&mut self) -> Expression {
        let block = self.parse_block();

        Expression {
            id: self.create_node_id(),
            span: block.span,
            kind: ExpressionKind::Block(Box::new(block)),
        }
    }

    /// "if" expression BLOCK ( "else" expression )?
    fn parse_if_expression(&mut self) -> Expression {
        let if_keyword = self.expect_keyword(Keyword::If);
        let condition = self.parse_expression();
        let positive = self.parse_block();

        let negative = (self
            .expect_peek("else keyword, semicolon, or close brace")
            .kind
            == TokenKind::Keyword(Keyword::Else))
        .then(|| {
            self.expect_keyword(Keyword::Else);

            let peeked = self.expect_peek("if keyword or opening brace");

            if peeked.kind == TokenKind::Keyword(Keyword::If) {
                return self.parse_if_expression();
            }

            if peeked.kind == TokenKind::OpenBrace {
                return self.parse_block_expression();
            }

            self.report_fatal_error_old(&format!(
                "Expected if expression or block after else keyword but found {:?} ({})",
                peeked.kind,
                self.lexer.source().value_of_span(peeked.span)
            ))
        });

        Expression {
            id: self.create_node_id(),
            span: Span::new(
                if_keyword.span.start,
                negative
                    .as_ref()
                    .map(|n: &Expression| n.span.end)
                    .unwrap_or(positive.span.end),
            ),
            kind: ExpressionKind::If {
                condition: Box::new(condition),
                positive: Box::new(positive),
                negative: negative.map(Box::new),
            },
        }
    }

    /// "while" expression BLOCK
    fn parse_while_expression(&mut self) -> Expression {
        let while_keyword = self.expect_keyword(Keyword::While);
        let condition = self.parse_expression();
        let block = self.parse_block();

        Expression {
            id: self.create_node_id(),
            span: Span::new(while_keyword.span.start, block.span.end),
            kind: ExpressionKind::While {
                condition: Box::new(condition),
                block: Box::new(block),
            },
        }
    }

    fn parse_atomic_expression(&mut self) -> Expression {
        // Check for qualified identifier
        if self
            .expect_peek("qualified identifier, open paren, open bracket, or literal expression")
            .kind
            == TokenKind::Identifier
        {
            let qualified_identifier = self.parse_qualified_identifier();

            if self.lookahead_is_struct_initializer() {
                self.expect_next_to_be(TokenKind::OpenBrace);
                let fields = self.parse_struct_initializer_fields();
                let close_brace = self.expect_next_to_be(TokenKind::CloseBrace);

                return Expression {
                    id: self.create_node_id(),
                    span: Span::new(qualified_identifier.span.start, close_brace.span.end),
                    kind: ExpressionKind::Struct {
                        name: qualified_identifier,
                        fields,
                    },
                };
            }

            return Expression {
                id: self.create_node_id(),
                span: qualified_identifier.span,
                kind: ExpressionKind::QualifiedIdentifier(Box::new(qualified_identifier)),
            };
        }

        // Check for grouping
        if self
            .expect_peek("open paren, open bracket, or literal expression")
            .kind
            == TokenKind::OpenParen
        {
            return self.parse_grouping_expression();
        }

        // Check for array literal
        if self.expect_peek("open bracket or literal expression").kind == TokenKind::OpenBracket {
            return self.parse_array_initializer_expression();
        }

        // check for local self

        if self.expect_peek("self keyword or literal expression").kind
            == TokenKind::Keyword(Keyword::This)
        {
            let self_keyword = self.expect_keyword(Keyword::This);

            return Expression {
                id: self.create_node_id(),
                span: self_keyword.span,
                kind: ExpressionKind::This,
            };
        }

        // Assume it's a literal (no other valid options)
        let literal = self.parse_literal();

        Expression {
            id: self.create_node_id(),
            span: literal.span,
            kind: ExpressionKind::Literal(Box::new(literal)),
        }
    }

    fn lookahead_is_struct_initializer(&mut self) -> bool {
        self.lexer
            .peek_nth(0)
            .filter(|t| t.kind == TokenKind::OpenBrace)
            .and_then(|_| self.lexer.peek_nth(1))
            .filter(|t| t.kind == TokenKind::Identifier)
            .and_then(|_| self.lexer.peek_nth(2))
            .filter(|t| t.kind == TokenKind::Colon)
            .is_some()
    }

    fn parse_struct_initializer_fields(&mut self) -> Box<[StructInitializerField]> {
        let mut fields = Vec::new();

        while self.expect_peek("identifier or closing brace").kind == TokenKind::Identifier {
            let name = self.parse_identifier();
            self.expect_next_to_be(TokenKind::Colon);
            let value = self.parse_expression();

            if self.expect_peek("comma or closing brace").kind == TokenKind::Comma {
                self.expect_next_to_be(TokenKind::Comma);
            }

            fields.push(StructInitializerField {
                id: self.create_node_id(),
                span: Span::merge(name.span, value.span),
                name,
                value: Box::new(value),
            });
        }

        fields.into()
    }

    fn parse_grouping_expression(&mut self) -> Expression {
        let open_paren = self.expect_next_to_be(TokenKind::OpenParen);
        let expression = self.parse_expression();

        // Parse tuple
        if self.expect_peek("open paren, or literal expression").kind == TokenKind::Comma {
            let mut expressions = vec![expression];

            // FIXME: parse using struct algorithm for trailing comma

            // While the next token is a comma try and parse more parameters
            while self
                .lexer
                .peek()
                .is_some_and(|t| t.kind == TokenKind::Comma)
            {
                self.expect_next_to_be(TokenKind::Comma);
                expressions.push(self.parse_expression());
            }

            let close_paren = self.expect_next_to_be(TokenKind::CloseParen);

            return Expression {
                id: self.create_node_id(),
                span: Span::new(open_paren.span.start, close_paren.span.end),
                kind: ExpressionKind::Tuple(expressions.into()),
            };
        }

        let close_paren = self.expect_next_to_be(TokenKind::CloseParen);

        Expression {
            id: self.create_node_id(),
            span: Span::new(open_paren.span.start, close_paren.span.end),
            kind: ExpressionKind::Grouping(Box::new(expression)),
        }
    }

    fn parse_array_initializer_expression(&mut self) -> Expression {
        let open_bracket = self.expect_next_to_be(TokenKind::OpenBracket);

        let array_initializer = if self.expect_peek("expression or close bracket").kind
            == TokenKind::CloseBracket
        {
            ArrayInitializer::Specific(Box::new([]))
        } else {
            let first_expression = self.parse_expression();
            let token = self.expect_peek("expression or close bracket");

            match token.kind {
                TokenKind::Semicolon => {
                    let _semi = self.expect_next_to_be(TokenKind::Semicolon);
                    let length = self.parse_literal();

                    if length.kind != LiteralKind::Integer {
                        // TODO: add this to accumulated error list since
                        // this is trivially recoverable

                        // TODO: allow constant expressions

                        self.report_fatal_error(
                            length.span,
                            "Array length must be an integer literal",
                        )
                    }

                    ArrayInitializer::Repeated {
                        value: Box::new(first_expression),
                        length: Box::new(length),
                    }
                }
                TokenKind::CloseBracket => ArrayInitializer::Specific(Box::new([first_expression])),
                TokenKind::Comma => {
                    let mut values = vec![first_expression];

                    self.expect_next_to_be(TokenKind::Comma);

                    while self.expect_peek("expression or closing bracket").kind
                        != TokenKind::CloseBracket
                    {
                        let value = self.parse_expression();

                        if self.expect_peek("comma or closing brace").kind == TokenKind::Comma {
                            self.expect_next_to_be(TokenKind::Comma);
                        }

                        values.push(value);
                    }

                    ArrayInitializer::Specific(values.into())
                }
                k => self.report_fatal_error_old(&format!(
                    "Unexpected token in array literal {:?} ({})",
                    k,
                    self.lexer.source().value_of_span(token.span)
                )),
            }
        };

        let close_bracket = self.expect_next_to_be(TokenKind::CloseBracket);

        Expression {
            id: self.create_node_id(),
            span: Span::new(open_bracket.span.start, close_bracket.span.end),
            kind: ExpressionKind::Array(Box::new(array_initializer)),
        }
    }

    fn parse_literal(&mut self) -> Literal {
        let token = self.expect_next("literal");

        let kind = match token.kind {
            TokenKind::BooleanLiteral => LiteralKind::Boolean,
            TokenKind::ByteLiteral => LiteralKind::Byte,
            TokenKind::CharLiteral => LiteralKind::Char,
            TokenKind::IntegerLiteral => LiteralKind::Integer,
            TokenKind::FloatLiteral => LiteralKind::Float,
            TokenKind::StringLiteral => LiteralKind::String,
            TokenKind::ByteStringLiteral => LiteralKind::ByteString,
            TokenKind::CStringLiteral => LiteralKind::CString,
            k => self.report_fatal_error_old(&format!(
                "Expected literal but found {:?} ({})",
                k,
                self.lexer.source().value_of_span(token.span)
            )),
        };

        let value = self.lexer.source().value_of_span(token.span);

        let symbol = match kind {
            LiteralKind::String => InternedSymbol::new(
                &value[1..value.len() - 1]
                    .replace("\\n", "\n")
                    .replace("\\r", "\r")
                    .replace("\\0", "\0"),
            ),
            _ => InternedSymbol::new(value),
        };

        Literal {
            id: self.create_node_id(),
            span: token.span,
            kind,
            symbol,
        }
    }
}
