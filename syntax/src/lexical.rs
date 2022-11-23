use logos::Logos;

#[derive(Logos, Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum Token {
    #[token("module")]
    Module,

    #[token("import")]
    Import,

    #[token("data")]
    Data,

    #[token("->")]
    #[token("→")]
    Arrow,

    #[token("lambda")]
    #[token("λ")]
    #[token("\\")]
    Lambda,

    #[token(":")]
    Colon,

    #[token(";")]
    SemiColon,

    #[token("{")]
    LBrace,

    #[token("}")]
    RBrace,

    #[token("[")]
    LSquare,

    #[token("]")]
    RSquare,

    #[token("(")]
    LParen,

    #[token(")")]
    RParen,

    #[token(".")]
    Dot,

    #[token("case")]
    Case,

    #[token("of")]
    Of,

    #[token("=")]
    Equal,

    #[regex("[a-z]+[0-9a-zA-Z']*")]
    SmallCase,

    #[token("Type")]
    Type,

    #[regex("[A-Z]+[0-9a-zA-Z']*")]
    BigCase,

    #[token("_")]
    Underscore,

    #[token("let")]
    Let,

    #[token("in")]
    In,

    // Logos requires one token variant to handle errors,
    // it can be named anything you wish.
    #[error]
    Error,
    // We can also use this variant to define whitespace,
    // or any other matches we wish to skip.
    #[regex(r"[ \t\n\f\r]+", logos::skip)]
    _Slience,
}

#[derive(Clone, Debug, PartialEq)]
pub struct SrcSpan<'a> {
    pub span: std::ops::Range<usize>,
    pub source: &'a str,
}

impl<'a> chumsky::Span for SrcSpan<'a> {
    type Context = &'a str;
    type Offset = usize;
    fn context(&self) -> Self::Context {
        self.source
    }
    fn start(&self) -> Self::Offset {
        self.span.start
    }
    fn end(&self) -> Self::Offset {
        self.span.end
    }
    fn new(context: Self::Context, range: std::ops::Range<Self::Offset>) -> Self {
        Self {
            source: context,
            span: range,
        }
    }
}

impl<'a> SrcSpan<'a> {
    pub fn slice(&self) -> &'a str {
        &self.source[self.span.start..self.span.end]
    }
}

pub struct LexerStream<'src> {
    lexer: logos::Lexer<'src, Token>,
}

impl<'src> Iterator for LexerStream<'src> {
    type Item = (Token, SrcSpan<'src>);
    fn next(&mut self) -> Option<Self::Item> {
        use chumsky::Span;
        match self.lexer.next() {
            None => None,
            Some(token) => Some((token, SrcSpan::new(self.lexer.source(), self.lexer.span()))),
        }
    }
}

impl<'src> LexerStream<'src> {
    pub fn chumsky_stream(src: &'src str) -> chumsky::Stream<'src, Token, SrcSpan<'src>, Self> {
        use chumsky::Span;
        chumsky::Stream::from_iter(
            SrcSpan::new(src, 0..src.len()),
            LexerStream {
                lexer: Token::lexer(src),
            },
        )
    }
}

#[cfg(test)]
mod test {
    use super::Token;
    use logos::Logos;
    #[test]
    fn test() {
        let input = r#"
module Main

data Bool = {
    True : Bool;
    False : Bool;
}

not : Bool -> Bool
not x = case x of {
    True -> False;
    False -> True;
}
        "#;
        let mut lexer = Token::lexer(input);
        use Token::*;
        let tokens = vec![
            Module, BigCase, Data, BigCase, Equal, LBrace, BigCase, Colon, BigCase, SemiColon,
            BigCase, Colon, BigCase, SemiColon, RBrace, SmallCase, Colon, BigCase, Arrow, BigCase,
            SmallCase, SmallCase, Equal, Case, SmallCase, Of, LBrace, BigCase, Arrow, BigCase,
            SemiColon, BigCase, Arrow, BigCase, SemiColon, RBrace,
        ];
        for i in tokens.into_iter() {
            assert_eq!(Some(i), lexer.next());
        }
    }
}
