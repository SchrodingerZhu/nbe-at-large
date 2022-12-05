use chumsky::{error::Simple, Parser};

use crate::lexical::{SrcSpan, Token};

#[derive(Clone, Debug)]
pub struct Ptr<T> {
    pub location: std::ops::Range<usize>,
    pub data: Box<T>,
}

impl<T> std::ops::Deref for Ptr<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.data.as_ref()
    }
}

impl<T> Ptr<T> {
    fn new(location: std::ops::Range<usize>, data: T) -> Self {
        Self {
            location,
            data: Box::new(data),
        }
    }
}

#[derive(Clone, Debug)]
pub enum ParseTree<'a> {
    Literal(&'a str),

    Import(Ptr<Self>),

    Module {
        name: Ptr<Self>,
        definitions: Vec<Ptr<Self>>,
    },

    Underscore,
    TrustMe,

    Variable(Ptr<Self>),
    ConstructorRef(Ptr<Self>),
    AnnotableVariable {
        // in let expr
        name: Option<Ptr<Self>>,
        annotation: Option<Ptr<Self>>,
    },
    Parameter {
        name: Ptr<Self>,
        implicit: bool,
    },

    Type,
    TypeRef(Ptr<Self>),
    Telescope {
        name: Ptr<Self>,
        annotation: Ptr<Self>,
        implicit: bool,
    },
    Arrow {
        left: Ptr<Self>,
        right: Ptr<Self>,
    },
    TypeDecl {
        former: Ptr<Self>,
        constructors: Vec<Ptr<Self>>,
    },
    TypeFormer {
        name: Ptr<Self>,
        params: Vec<Ptr<Self>>,
    },
    Constructor {
        name: Ptr<Self>,
        r#type: Ptr<Self>,
    },

    FuncDecl {
        name: Ptr<Self>,
        r#type: Ptr<Self>,
    },
    FuncDefine {
        name: Ptr<Self>,
        params: Vec<Ptr<Self>>,
        body: Ptr<Self>,
    },
    FuncApply {
        func: Ptr<Self>,
        args: Vec<Ptr<Self>>,
    },

    // syntax suger for sigma type
    Sigma {
        left: Ptr<Self>,
        right: Ptr<Self>,
    },

    // no nested destructure for now
    PatternRule {
        constructor: Ptr<Self>,
        variables: Vec<Ptr<Self>>,
        body: Ptr<Self>,
    },
    PatternMatch {
        expr: Ptr<Self>,
        rules: Vec<Ptr<Self>>,
    },
    Let {
        var: Ptr<Self>,
        binding: Ptr<Self>,
        body: Ptr<Self>,
    },
    Lambda {
        params: Vec<Ptr<Self>>,
        body: Ptr<Self>,
    },
}

pub type ParserError<'src> = Simple<Token, SrcSpan<'src>>;

impl<'a> ParseTree<'a> {
    pub fn get_literal(&self) -> &'a str {
        match self {
            ParseTree::Literal(x) => *x,
            _ => assert_unreachable!(),
        }
    }
}

pub fn parse(src: &str) -> (Option<Ptr<ParseTree>>, Vec<ParserError>) {
    let stream = crate::lexical::LexerStream::chumsky_stream(src.as_ref());
    implementation::parse_module().parse_recovery_verbose(stream)
}

mod implementation {
    use chumsky::prelude::*;
    use ParseTree::*;

    use super::*;

    pub(super) trait Parse<'a, O = Ptr<ParseTree<'a>>>:
        Parser<Token, O, Error = ParserError<'a>> + Clone + 'a
    {
    }

    impl<'a, O, T> Parse<'a, O> for T where T: Parser<Token, O, Error = ParserError<'a>> + Clone + 'a {}

    pub(super) fn parse_module<'a>() -> impl Parse<'a> {
        let consume_module = just(Token::Module);
        let name = parse_literal(Token::BigCase);
        consume_module
            .ignore_then(name)
            .then(parse_definitions())
            .then_ignore(end())
            .map_with_span(|(name, definitions), span| {
                Ptr::new(span.span, Module { name, definitions })
            })
    }

    fn parse_dependent_syntax_super<'a>(token: Token, expr: impl Parse<'a>) -> impl Parse<'a> {
        let consume_symbol = just(token);
        let left = parse_telescope(false, expr.clone()).or(expr.clone());
        let consume_comma = just(Token::Comma);
        consume_symbol
            .ignore_then(left)
            .then_ignore(consume_comma)
            .then(expr)
            .map_with_span(move |(left, right), span| {
                Ptr::new(
                    span.span,
                    match token {
                        Token::Sigma => Sigma { left, right },
                        Token::Pi => Arrow { left, right },
                        _ => assert_unreachable!(),
                    },
                )
            })
    }

    fn parse_function_decl<'a>(expr: impl Parse<'a>) -> impl Parse<'a> {
        let name = parse_literal(Token::SmallCase);
        let consume_colon = just(Token::Colon);
        name.then_ignore(consume_colon)
            .then(expr)
            .map_with_span(|(name, r#type), span| Ptr::new(span.span, FuncDecl { name, r#type }))
    }

    fn parse_function_def<'a>(expr: impl Parse<'a>) -> impl Parse<'a> {
        let name = parse_literal(Token::SmallCase);
        let params = parse_parameter().repeated();
        let consume_equal = just(Token::Equal);
        name.then(params)
            .then_ignore(consume_equal)
            .then(expr)
            .map_with_span(|((name, params), body), span| {
                Ptr::new(span.span, FuncDefine { name, params, body })
            })
    }

    fn parse_literal<'a>(token: Token) -> impl Parse<'a> {
        just(token).map_with_span(|_, span: SrcSpan<'a>| {
            Ptr::new(span.span.clone(), Literal(span.slice()))
        })
    }

    fn parse_definitions<'a>() -> impl Parse<'a, Vec<Ptr<ParseTree<'a>>>> {
        parse_import()
            .or(parse_type_decl(parse_expr()))
            .or(parse_function_decl(parse_expr()))
            .or(parse_function_def(parse_expr()))
            .repeated()
    }

    // data List (a : Type) = {
    //      Nil : List a;
    //      Cons : a -> List;
    // }
    fn parse_type_former<'a>(expr: impl Parse<'a>) -> impl Parse<'a> {
        let consume_data = just(Token::Data);
        let name = parse_literal(Token::BigCase);
        let telescopes = parse_telescope(true, expr.clone())
            .or(parse_telescope(false, expr.clone()))
            .repeated();
        consume_data
            .ignore_then(name)
            .then(telescopes)
            .map_with_span(|(name, params), span| Ptr::new(span.span, TypeFormer { name, params }))
    }

    fn parse_constructor<'a>(expr: impl Parse<'a>) -> impl Parse<'a> {
        let name = parse_literal(Token::BigCase);
        let consume_colon = just(Token::Colon);
        let consume_semicolon = just(Token::SemiColon);
        name.then_ignore(consume_colon)
            .then(expr)
            .then_ignore(consume_semicolon)
            .map_with_span(|(name, r#type), span| Ptr::new(span.span, Constructor { name, r#type }))
    }

    fn parse_type_decl<'a>(expr: impl Parse<'a>) -> impl Parse<'a> {
        let former = parse_type_former(expr.clone());
        let consume_equal = just(Token::Equal);
        let consume_lbrace = just(Token::LBrace);
        let constructors = parse_constructor(expr).repeated();
        let consume_rbrace = just(Token::RBrace);
        former
            .then_ignore(consume_equal)
            .then_ignore(consume_lbrace)
            .then(constructors)
            .then_ignore(consume_rbrace)
            .map_with_span(|(former, constructors), span| {
                Ptr::new(
                    span.span,
                    TypeDecl {
                        former,
                        constructors,
                    },
                )
            })
    }

    fn parse_import<'a>() -> impl Parse<'a> {
        let consume_import = just(Token::Import);
        let name = parse_literal(Token::BigCase);
        consume_import
            .ignore_then(name)
            .map_with_span(|name, span| Ptr::new(span.span, Import(name)))
    }

    fn parse_variable<'a>() -> impl Parse<'a> {
        let name = parse_literal(Token::SmallCase);
        name.map_with_span(|name, span| Ptr::new(span.span, Variable(name)))
    }

    fn parse_constructor_ref<'a>() -> impl Parse<'a> {
        let consume_at = just(Token::At);
        let name = parse_literal(Token::BigCase);
        consume_at
            .ignore_then(name.map_with_span(|name, span| Ptr::new(span.span, ConstructorRef(name))))
    }

    fn parse_type_ref<'a>() -> impl Parse<'a> {
        let name = parse_literal(Token::BigCase);
        name.map_with_span(|name, span| Ptr::new(span.span, TypeRef(name)))
    }

    fn parse_simple_type_expr<'a>(expr: impl Parse<'a>) -> impl Parse<'a> {
        parse_arrow_expr_primitives(expr.clone())
            .or(parse_telescope(true, expr.clone()))
            .or(parse_telescope(false, expr))
    }

    fn parse_arrow_expr<'a>(expr: impl Parse<'a>) -> impl Parse<'a> {
        recursive(|arrow| {
            let primitive = parse_simple_type_expr(expr);
            let delimited_arrow = arrow.delimited_by(just(Token::LParen), just(Token::RParen));
            primitive
                .or(delimited_arrow)
                .separated_by(just(Token::Arrow))
                .at_least(1)
                .map(|mut v: Vec<Ptr<ParseTree<'a>>>| unsafe {
                    let last = v.pop().unwrap_unchecked();
                    v.into_iter().rfold(last, |prev, current| {
                        Ptr::new(
                            current.location.start()..prev.location.end(),
                            Arrow {
                                left: current,
                                right: prev,
                            },
                        )
                    })
                })
        })
    }

    fn parse_telescope<'a>(implicit: bool, expr: impl Parse<'a>) -> impl Parse<'a> {
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
            .then(expr)
            .then_ignore(consume_rparen)
            .map_with_span(move |(name, annotation), span| {
                Ptr::new(
                    span.span,
                    Telescope {
                        name,
                        annotation,
                        implicit,
                    },
                )
            })
    }

    fn parse_arrow_expr_primitives<'a>(expr: impl Parse<'a>) -> impl Parse<'a> {
        // variable
        // function/constructor apply
        // lambda
        // pattern matching
        // let in
        // type expr
        // trustme
        // arrow
        // Type
        let trustme =
            just(Token::TrustMe).map_with_span(|_, span: SrcSpan<'a>| Ptr::new(span.span, TrustMe));
        let r#type =
            just(Token::Type).map_with_span(|_, span: SrcSpan<'a>| Ptr::new(span.span, Type));

        parse_variable()
            .or(parse_constructor_ref())
            .or(parse_type_ref())
            .or(trustme)
            .or(parse_function_apply(expr.clone()))
            .or(parse_lambda(expr.clone()))
            .or(parse_pattern_match(expr.clone()))
            .or(parse_let_in_expr(expr.clone()))
            .or(parse_dependent_syntax_super(Token::Pi, expr.clone()))
            .or(parse_dependent_syntax_super(Token::Sigma, expr))
            .or(r#type)
    }

    fn parse_expr<'a>() -> impl Parse<'a> {
        // variable
        // function/constructor apply
        // lambda
        // pattern matching
        // let in
        // type expr
        // trustme
        // arrow
        // Type

        recursive(|expr| {
            let trustme = just(Token::TrustMe)
                .map_with_span(|_, span: SrcSpan<'a>| Ptr::new(span.span, TrustMe));
            let r#type =
                just(Token::Type).map_with_span(|_, span: SrcSpan<'a>| Ptr::new(span.span, Type));
            parse_arrow_expr(expr.clone())
                .or(parse_constructor_ref())
                .or(parse_type_ref())
                .or(trustme)
                .or(parse_function_apply(expr.clone()))
                .or(parse_lambda(expr.clone()))
                .or(parse_pattern_match(expr.clone()))
                .or(parse_let_in_expr(expr.clone()))
                .or(parse_variable())
                .or(parse_dependent_syntax_super(Token::Pi, expr.clone()))
                .or(parse_dependent_syntax_super(Token::Sigma, expr))
                .or(r#type)
        })
    }

    fn parse_pattern_match<'a>(expr: impl Parse<'a>) -> impl Parse<'a> {
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
            .map_with_span(|(expr, rules), span| Ptr::new(span.span, PatternMatch { expr, rules }))
    }

    fn parse_pattern_rule<'a>(expr: impl Parse<'a>) -> impl Parse<'a> {
        let constructor = parse_literal(Token::BigCase);
        let variables = parse_parameter().repeated();
        let consume_arrow = just(Token::Arrow);
        let consume_semicolon = just(Token::SemiColon);
        constructor
            .then(variables)
            .then_ignore(consume_arrow)
            .then(expr)
            .then_ignore(consume_semicolon)
            .map_with_span(|((constructor, variables), body), span| {
                Ptr::new(
                    span.span,
                    PatternRule {
                        constructor,
                        variables,
                        body,
                    },
                )
            })
    }

    fn parse_lambda<'a>(expr: impl Parse<'a>) -> impl Parse<'a> {
        let consume_lambda = just(Token::Lambda);
        let variables = parse_parameter().repeated();
        let consume_dot = just(Token::Dot);
        consume_lambda
            .ignore_then(variables)
            .then_ignore(consume_dot)
            .then(expr)
            .map_with_span(|(params, body), span| Ptr::new(span.span, Lambda { params, body }))
    }

    // (func x x x)
    fn parse_function_apply<'a>(expr: impl Parse<'a>) -> impl Parse<'a> {
        let consume_lparen = just(Token::LParen);
        let consume_rparen = just(Token::RParen);
        consume_lparen
            .ignore_then(expr.clone())
            .then(expr.repeated().at_least(1))
            .then_ignore(consume_rparen)
            .map_with_span(|(func, args), span| Ptr::new(span.span, FuncApply { func, args }))
    }

    fn parse_let_in_expr<'a>(expr: impl Parse<'a>) -> impl Parse<'a> {
        let consume_let = just(Token::Let);
        let consume_equal = just(Token::Equal);
        let consume_in = just(Token::In);
        consume_let
            .ignore_then(parse_annotable_variable(expr.clone()))
            .then_ignore(consume_equal)
            .then(expr.clone())
            .then_ignore(consume_in)
            .then(expr)
            .map_with_span(|((var, binding), body), span| {
                Ptr::new(span.span, Let { var, binding, body })
            })
    }

    fn parse_annotable_variable<'a>(expr: impl Parse<'a>) -> impl Parse<'a> {
        let consume_colon = just(Token::Colon);
        let name = || {
            parse_literal(Token::SmallCase)
                .map(|x| Some(x))
                .or(just(Token::Underscore).to(None))
        };
        let annotated = name().then_ignore(consume_colon).then(expr).map_with_span(
            |(name, annotation), span| {
                Ptr::new(
                    span.span,
                    AnnotableVariable {
                        name,
                        annotation: Some(annotation),
                    },
                )
            },
        );
        let unannotated = {
            name().map_with_span(|name, span| {
                Ptr::new(
                    span.span,
                    AnnotableVariable {
                        name,
                        annotation: None,
                    },
                )
            })
        };
        annotated.or(unannotated)
    }

    fn parse_parameter<'a>() -> impl Parse<'a> {
        let consume_lsquare = just(Token::LSquare);
        let consume_rsquare = just(Token::RSquare);

        let explicit = parse_literal(Token::SmallCase).map_with_span(|name, span| {
            let data = Parameter {
                name,
                implicit: false,
            };
            Ptr::new(span.span, data)
        });

        let implicit = consume_lsquare
            .ignore_then(parse_literal(Token::SmallCase))
            .then_ignore(consume_rsquare)
            .map_with_span(|name, span| {
                let data = Parameter {
                    name,
                    implicit: true,
                };
                Ptr::new(span.span, data)
            });

        let underscore = just(Token::Underscore)
            .map_with_span(|_, span: SrcSpan<'a>| Ptr::new(span.span, ParseTree::Underscore));

        implicit.or(explicit).or(underscore)
    }

    #[test]
    fn test_data() {
        let src = "
            module Test
            import Primitive
            data List (a : Type) = {
                Nil : (List a);
                Cons : a -> (List a) -> (List a);
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
            map : [a : Type] -> [b : Type] -> (a -> b) -> (List a) -> (List b) -> (let b = b in (A b))
        ";
        let steam = crate::lexical::LexerStream::chumsky_stream(src);
        let parsed = parse_module().parse(steam);
        println!("{:?}", parsed.unwrap());
    }

    #[test]
    fn test_suger() {
        let src = "
            module Test
            import Primitive
            map : `Pi (x : Nat) , `Sigma (y : Nat) , (Gt x y)
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
                Nil -> @Nil;
                Cons head tail -> (@Cons (f head) (map f tail));
            }
        ";
        let stream = crate::lexical::LexerStream::chumsky_stream(src);
        let parsed = parse_module().parse(stream);
        println!("{:#?}", parsed.unwrap());
    }

    #[test]
    fn test_simple() {
        let src = "
            module Test
            list = (List Nat)
            test = lambda a b . (@Cons a b)
        ";
        let stream = crate::lexical::LexerStream::chumsky_stream(src);
        let parsed = parse_module().parse(stream);
        println!("{:#?}", parsed.unwrap());
    }
}
