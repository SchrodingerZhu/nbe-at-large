use logos::Logos;

#[derive(Logos, Debug, PartialEq)]
enum Token {
    #[token("module")]
    Module,

    #[token("import")]
    Import,

    #[token("where")]
    Where,

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

    #[token("if")]
    If,

    #[token("then")]
    Then,

    #[token("else")]
    Else,

    #[token("=")]
    Equal,

    #[regex("[a-z]+[0-9a-zA-Z']*")]
    SmallCase,

    #[token("Type")]
    Type,

    #[regex("[A-Z]+[0-9a-zA-Z']*")]
    BigCase,

    // Logos requires one token variant to handle errors,
    // it can be named anything you wish.
    #[error]
    Error,
    // We can also use this variant to define whitespace,
    // or any other matches we wish to skip.
    #[regex(r"[ \t\n\f\r]+", logos::skip)]
    _Slience,
}

#[cfg(test)]
mod test {
    use super::Token;
    use logos::Logos;
    #[test]
    fn test() {
        let input = r#"
module Main where

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
            Module, BigCase, Where, Data, BigCase, Equal, LBrace, BigCase, Colon, BigCase,
            SemiColon, BigCase, Colon, BigCase, SemiColon, RBrace, SmallCase, Colon, BigCase,
            Arrow, BigCase, SmallCase, SmallCase, Equal, Case, SmallCase, Of, LBrace, BigCase,
            Arrow, BigCase, SemiColon, BigCase, Arrow, BigCase, SemiColon, RBrace,
        ];
        for i in tokens.into_iter() {
            assert_eq!(Some(i), lexer.next());
        }
    }
}
