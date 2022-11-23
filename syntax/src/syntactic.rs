use crate::lexical::Token;
type Span = std::ops::Range<usize>;

#[derive(Debug)]
pub enum ParseTree<'a> {
    Implicit(Box<Self>),

    Module {
        name: &'a str,
        definitions: Vec<Box<Self>>,
    },

    Varibable {
        name: &'a str,
        annotation: Option<Box<Self>>,
    },

    TypeLit(&'a str),
    Type {
        name: &'a str,
        parms: Vec<Box<Self>>,
    },
    Telescope {
        name: &'a str,
        annotation: Box<Self>,
    },
    Arrow {
        lhs: Box<Self>,
        rhs: Box<Self>,
    }, // can be telescope, type lit, or type
    TypeDecl {
        name: &'a str,
        contructors: Vec<Box<Self>>,
    },
    Contructor {
        name: &'a str,
        r#type: Box<Self>,
    },

    FuncDecl {
        name: &'a str,
        r#type: Box<Self>,
    },
    FuncDefine {
        name: &'a str,
        params: Vec<Box<Self>>,
        body: Box<Self>,
    },
    FuncApply {
        func: Box<Self>,
        args: Vec<Box<Self>>,
    },

    // no nested destructure for now
    Destructure {
        constructor: &'a str,
        fields: Vec<Box<Self>>,
    },

    Branch {
        r#if: Box<Self>,
        then: Box<Self>,
        r#else: Box<Self>,
    },
    PatternRule {
        pattern: Box<Self>,
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

#[derive(Debug)]
struct Parser<'a> {
    source: &'a str,
}

#[derive(thiserror::Error, Debug)]
pub enum ParserError {
    #[error("internal parser error")]
    Internal,
    #[error("syntax error at {1:?}: {0}")]
    Syntax(String, Span),
}

impl<'a, I> pratt::PrattParser<I> for Parser<'a>
where
    I: Iterator<Item = (Token, Span)>,
{
    type Error = error_stack::Report<ParserError>;

    type Input = (Token, Span);

    type Output = Box<ParseTree<'a>>;

    fn query(&mut self, input: &Self::Input) -> std::result::Result<pratt::Affix, Self::Error> {
        let (token, span) = input;
        match token {
            Token::Module => todo!(),
            Token::Import => todo!(),
            Token::Where => todo!(),
            Token::Data => todo!(),
            Token::Arrow => todo!(),
            Token::Lambda => todo!(),
            Token::Colon => todo!(),
            Token::SemiColon => todo!(),
            Token::LBrace => todo!(),
            Token::RBrace => todo!(),
            Token::LSquare => todo!(),
            Token::RSquare => todo!(),
            Token::LParen => todo!(),
            Token::RParen => todo!(),
            Token::Dot => todo!(),
            Token::Case => todo!(),
            Token::Of => todo!(),
            Token::If => todo!(),
            Token::Then => todo!(),
            Token::Else => todo!(),
            Token::Equal => todo!(),
            Token::SmallCase => todo!(),
            Token::Type => todo!(),
            Token::BigCase => todo!(),
            Token::Underscope => todo!(),
            Token::Let => todo!(),
            Token::In => todo!(),
            Token::Error => todo!(),
            Token::_Slience => unreachable!(),
        }
    }

    fn primary(&mut self, input: Self::Input) -> std::result::Result<Self::Output, Self::Error> {
        todo!()
    }

    fn infix(
        &mut self,
        lhs: Self::Output,
        op: Self::Input,
        rhs: Self::Output,
    ) -> std::result::Result<Self::Output, Self::Error> {
        todo!()
    }

    fn prefix(
        &mut self,
        op: Self::Input,
        rhs: Self::Output,
    ) -> std::result::Result<Self::Output, Self::Error> {
        todo!()
    }

    fn postfix(
        &mut self,
        lhs: Self::Output,
        op: Self::Input,
    ) -> std::result::Result<Self::Output, Self::Error> {
        todo!()
    }
}
