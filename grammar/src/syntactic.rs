use chumsky::{error::Simple, Parser};

use crate::lexical::{SrcSpan, Token};

#[derive(Clone, Debug)]
pub enum ParseTree<'a> {
    Literal(&'a str),
    Implicit(Box<Self>),

    Import(Box<Self>),

    Module {
        name: Box<Self>,
        definitions: Vec<Box<Self>>,
    },

    Underscore,
    Variable {
        name: Box<Self>,
        annotation: Option<Box<Self>>,
    },

    Type,
    TypeExpr {
        name: Box<Self>,
        params: Vec<Box<Self>>,
    },
    Telescope {
        name: Box<Self>,
        annotation: Box<Self>,
    },
    Arrow {
        lhs: Box<Self>,
        rhs: Box<Self>,
    },
    TypeDecl {
        former: Box<Self>,
        constructors: Vec<Box<Self>>,
    },
    TypeFormer {
        name: Box<Self>,
        params: Vec<Box<Self>>,
    },
    Constructor {
        name: Box<Self>,
        r#type: Box<Self>,
    },

    FuncDecl {
        name: Box<Self>,
        r#type: Box<Self>,
    },
    FuncDefine {
        name: Box<Self>,
        params: Vec<Box<Self>>,
        body: Box<Self>,
    },
    FuncApply {
        func: Box<Self>,
        args: Vec<Box<Self>>,
    },

    Branch {
        r#if: Box<Self>,
        then: Box<Self>,
        r#else: Box<Self>,
    },
    // no nested destructure for now
    PatternRule {
        constructor: Box<Self>,
        variables: Vec<Box<Self>>,
        body: Box<Self>,
    },
    PatternMatch {
        expr: Box<Self>,
        rules: Vec<Box<Self>>,
    },
    Let {
        var: Box<Self>,
        binding: Box<Self>,
        body: Box<Self>,
    },
    Lambda {
        params: Vec<Box<Self>>,
        body: Box<Self>,
    },
}

pub type ParserError<'src> = Simple<Token, SrcSpan<'src>>;

pub fn parse<'a>(src: &'a str) -> (Option<Box<ParseTree<'a>>>, Vec<ParserError<'a>>) {
    let stream = crate::lexical::LexerStream::chumsky_stream(src.as_ref());
    implementation::parse_module().parse_recovery_verbose(stream)
}

mod implementation {
    use chumsky::prelude::*;
    use ParseTree::*;

    use super::*;

    pub(crate) trait MyParser<'a, O = Box<ParseTree<'a>>>:
        Parser<Token, O, Error = ParserError<'a>>
    {
    }

    impl<'a, O, T> MyParser<'a, O> for T where T: Parser<Token, O, Error = ParserError<'a>> {}

    pub(crate) fn parse_module<'a>() -> impl MyParser<'a> {
        let consume_module = just(Token::Module);
        let name = parse_literal(Token::BigCase);
        let expr = parse_expr().boxed();
        let r#type = parse_type(expr.clone()).boxed();
        consume_module
            .ignore_then(name)
            .then(parse_definitions(expr, r#type))
            .then_ignore(end())
            .map(|(name, definitions)| Box::new(Module { name, definitions }))
    }

    fn parse_function_decl<'a, T>(r#type: T) -> impl MyParser<'a>
    where
        T: MyParser<'a> + 'a,
    {
        let name = parse_literal(Token::SmallCase);
        let consume_colon = just(Token::Colon);
        name.then_ignore(consume_colon)
            .then(r#type)
            .map(|(name, r#type)| Box::new(FuncDecl { name, r#type }))
    }

    fn parse_function_def<'a, T>(expr: T) -> impl MyParser<'a>
    where
        T: MyParser<'a> + Clone + 'a,
    {
        let name = parse_literal(Token::SmallCase);
        let params = parse_variable(expr.clone()).repeated();
        let consume_equal = just(Token::Equal);
        name.then(params)
            .then_ignore(consume_equal)
            .then(expr)
            .map(|((name, params), body)| Box::new(FuncDefine { name, params, body }))
    }

    fn parse_literal<'a>(token: Token) -> impl MyParser<'a> {
        just(token).map_with_span(|_, span: SrcSpan<'a>| Box::new(Literal(span.slice())))
    }

    fn parse_definitions<'a, E, T>(expr: E, r#type: T) -> impl MyParser<'a, Vec<Box<ParseTree<'a>>>>
    where
        E: MyParser<'a> + Clone + 'a,
        T: MyParser<'a> + Clone + 'a,
    {
        parse_import()
            .or(parse_type_decl(r#type.clone()))
            .or(parse_function_decl(r#type))
            .or(parse_function_def(expr))
            .repeated()
    }

    // data List (a : Type) = {
    //      Nil : List a;
    //      Cons : a -> List;
    // }
    fn parse_type_former<'a, T>(r#type: T) -> impl MyParser<'a>
    where
        T: MyParser<'a> + Clone + 'a,
    {
        let consume_data = just(Token::Data);
        let name = parse_literal(Token::BigCase);
        let telescopes = parse_telescope(true, r#type.clone())
            .or(parse_telescope(false, r#type.clone()))
            .repeated();
        consume_data
            .ignore_then(name)
            .then(telescopes)
            .map(|(name, params)| Box::new(TypeFormer { name, params }))
    }

    fn parse_constructor<'a, T>(r#type: T) -> impl MyParser<'a>
    where
        T: MyParser<'a> + Clone + 'a,
    {
        let name = parse_literal(Token::BigCase);
        let consume_colon = just(Token::Colon);
        let consume_semicolon = just(Token::SemiColon);
        name.then_ignore(consume_colon)
            .then(r#type)
            .then_ignore(consume_semicolon)
            .map(|(name, r#type)| Box::new(Constructor { name, r#type }))
    }

    fn parse_type_decl<'a, T>(r#type: T) -> impl MyParser<'a>
    where
        T: MyParser<'a> + Clone + 'a,
    {
        let former = parse_type_former(r#type.clone());
        let consume_equal = just(Token::Equal);
        let consume_lbrace = just(Token::LBrace);
        let constructors = parse_constructor(r#type).repeated();
        let consume_rbrace = just(Token::RBrace);
        former
            .then_ignore(consume_equal)
            .then_ignore(consume_lbrace)
            .then(constructors)
            .then_ignore(consume_rbrace)
            .map(|(former, constructors)| {
                Box::new(TypeDecl {
                    former,
                    constructors,
                })
            })
    }

    fn parse_import<'a>() -> impl MyParser<'a> {
        let consume_import = just(Token::Import);
        let name = parse_literal(Token::BigCase);
        consume_import
            .ignore_then(name)
            .map(|name| Box::new(Import(name)))
    }

    // "Type"
    // Arrow
    // "type expr"

    fn parse_type<'a, E>(expr: E) -> impl MyParser<'a>
    where
        E: MyParser<'a> + Clone + 'a,
    {
        let type_literal = just(Token::Type).to(Box::new(Type));
        recursive(move |r#type| {
            type_literal
                .or(parse_arrow_expr(expr.clone(), r#type))
                .or(parse_type_expr(expr))
        })
    }

    fn parse_type_variable<'a>() -> impl MyParser<'a> {
        let name = parse_literal(Token::SmallCase);
        name.map(|name| {
            Box::new(Variable {
                name,
                annotation: None,
            })
        })
    }

    fn parse_simple_type_expr<'a, E, T>(expr: E, r#type: T) -> impl MyParser<'a>
    where
        T: MyParser<'a> + Clone,
        E: MyParser<'a> + 'a,
    {
        parse_type_expr(expr)
            .or(parse_type_variable())
            .or(parse_telescope(true, r#type.clone()))
            .or(parse_telescope(false, r#type))
    }

    fn parse_arrow_expr<'a, E, T>(expr: E, r#type: T) -> impl MyParser<'a>
    where
        T: MyParser<'a> + Clone + 'a,
        E: MyParser<'a> + Clone + 'a,
    {
        recursive(|arrow| {
            let primitive = parse_simple_type_expr(expr, r#type);
            let delimited_arrow = arrow.delimited_by(just(Token::LParen), just(Token::RParen));
            primitive
                .or(delimited_arrow)
                .separated_by(just(Token::Arrow))
                .at_least(1)
                .map(|mut v: Vec<Box<ParseTree<'a>>>| unsafe {
                    let last = v.pop().unwrap_unchecked();
                    v.into_iter().rfold(last, |prev, current| {
                        Box::new(Arrow {
                            lhs: current,
                            rhs: prev,
                        })
                    })
                })
        })
    }

    fn parse_type_expr<'a, E>(expr: E) -> impl MyParser<'a>
    where
        E: MyParser<'a>,
    {
        let name = parse_literal(Token::BigCase);
        let params = expr.repeated();
        name.then(params)
            .map(|(name, params)| Box::new(TypeExpr { name, params }))
    }

    fn parse_telescope<'a, P>(implicit: bool, r#type: P) -> impl MyParser<'a>
    where
        P: MyParser<'a>,
    {
        let consume_lparen = just(if implicit {
            Token::LSquare
        } else {
            Token::LParen
        });
        let name = parse_literal(Token::SmallCase);
        let consume_colon = just(Token::Colon);
        let consume_rparen = just(if implicit {
            Token::RSquare
        } else {
            Token::RParen
        });

        consume_lparen
            .ignore_then(name)
            .then_ignore(consume_colon)
            .then(r#type)
            .then_ignore(consume_rparen)
            .map(move |(name, annotation)| {
                if implicit {
                    Box::new(Implicit(Box::new(Telescope { name, annotation })))
                } else {
                    Box::new(Telescope { name, annotation })
                }
            })
    }

    fn parse_expr<'a>() -> impl MyParser<'a> {
        // variable
        // function/constructor apply
        // lambda
        // pattern matching
        // let in
        // type expr
        recursive(|expr| {
            parse_variable(expr.clone())
                .or(parse_function_apply(expr.clone()))
                .or(parse_lambda(expr.clone()))
                .or(parse_pattern_match(expr.clone()))
                .or(parse_let_in_expr(expr.clone()).or(parse_type(expr)))
        })
    }

    fn parse_pattern_match<'a, P>(expr: P) -> impl MyParser<'a>
    where
        P: MyParser<'a> + Clone + 'a,
    {
        let consume_case = just(Token::Case);
        let consume_of = just(Token::Of);
        let consume_lbrace = just(Token::LBrace);
        let rules = parse_pattern_rule(expr.clone()).repeated();
        let consume_rbrace = just(Token::RBrace);
        consume_case
            .ignore_then(expr)
            .then_ignore(consume_of)
            .then_ignore(consume_lbrace)
            .then(rules)
            .then_ignore(consume_rbrace)
            .map(|(expr, rules)| Box::new(PatternMatch { expr, rules }))
    }

    fn parse_pattern_rule<'a, P>(expr: P) -> impl MyParser<'a>
    where
        P: MyParser<'a> + Clone + 'a,
    {
        let constructor = parse_literal(Token::BigCase);
        let variables = parse_variable(expr.clone()).repeated();
        let consume_arrow = just(Token::Arrow);
        let consume_semicolon = just(Token::SemiColon);
        constructor
            .then(variables)
            .then_ignore(consume_arrow)
            .then(expr)
            .then_ignore(consume_semicolon)
            .map(|((constructor, variables), body)| {
                Box::new(PatternRule {
                    constructor,
                    variables,
                    body,
                })
            })
    }

    fn parse_lambda<'a, P>(expr: P) -> impl MyParser<'a>
    where
        P: MyParser<'a> + Clone + 'a,
    {
        let consume_lambda = just(Token::Lambda);
        let variables = parse_variable(expr.clone()).repeated();
        let consume_dot = just(Token::Dot);
        consume_lambda
            .ignore_then(variables)
            .then_ignore(consume_dot)
            .then(expr)
            .map(|(params, body)| Box::new(Lambda { params, body }))
    }

    // (func x x x)
    fn parse_function_apply<'a, P>(expr: P) -> impl MyParser<'a>
    where
        P: MyParser<'a> + Clone,
    {
        let consume_lparen = just(Token::LParen);
        let consume_rparen = just(Token::RParen);
        consume_lparen
            .ignore_then(expr.clone())
            .then(expr.repeated())
            .then_ignore(consume_rparen)
            .map(|(func, args)| Box::new(FuncApply { func, args }))
    }

    fn parse_let_in_expr<'a, P>(expr: P) -> impl MyParser<'a>
    where
        P: MyParser<'a> + Clone + 'a,
    {
        let consume_let = just(Token::Let);
        let consume_equal = just(Token::Equal);
        let consume_in = just(Token::In);
        consume_let
            .ignore_then(parse_variable(expr.clone()))
            .then_ignore(consume_equal)
            .then(expr.clone())
            .then_ignore(consume_in)
            .then(expr)
            .map(|((var, binding), body)| Box::new(Let { var, binding, body }))
    }

    fn parse_variable<'a, P>(expr: P) -> impl MyParser<'a>
    where
        P: MyParser<'a> + Clone + 'a,
    {
        let consume_lparen = || just(Token::LParen);
        let consume_lsquare = || just(Token::LSquare);
        let consume_rparen = || just(Token::RParen);
        let consume_rsquare = || just(Token::RSquare);
        let consume_colon = || just(Token::Colon);

        let annotation = || parse_type(expr.clone());

        let unannotated = || {
            parse_literal(Token::SmallCase).map(|name| {
                Box::new(Variable {
                    name,
                    annotation: None,
                })
            })
        };
        let annotated = || {
            parse_literal(Token::SmallCase)
                .then_ignore(consume_colon())
                .then(annotation())
                .map(|(name, annotation)| {
                    Box::new(Variable {
                        name,
                        annotation: Some(annotation),
                    })
                })
        };

        let explicit =
            unannotated().or(annotated().delimited_by(consume_lparen(), consume_rparen()));

        let implicit = unannotated()
            .delimited_by(consume_lsquare(), consume_rsquare())
            .or(annotated().delimited_by(consume_lsquare(), consume_rsquare()));

        explicit
            .or(implicit)
            .or(just(Token::Underscore).to(Box::new(Underscore)))
    }

    #[test]
    fn test_data() {
        let src = "
            module Test
            import Primitive
            data List (a : Type) = {
                Nil : List a;
                Cons : a -> List a -> List a;
            }
        ";
        let steam = crate::lexical::LexerStream::chumsky_stream(src);
        let parsed = parse_module().parse(steam);
        println!("{:?}", parsed.unwrap());
    }

    #[test]
    fn test_func_decl() {
        let src = "
            module Test
            import Primitive
            map : [a : Type] -> [b : Type] -> (a -> b) -> List a -> List b
        ";
        let steam = crate::lexical::LexerStream::chumsky_stream(src);
        let parsed = parse_module().parse(steam);
        println!("{:?}", parsed.unwrap());
    }

    #[test]
    fn test_func_def() {
        let src = "
            module Test
            import Primitive
            map f list = case list of {
                Nil -> Nil;
                Cons head tail -> Cons (f head) (map f tail);
            }
        ";
        let stream = crate::lexical::LexerStream::chumsky_stream(src);
        let parsed = parse_module().parse(stream);
        println!("{:?}", parsed.unwrap());
    }
}
