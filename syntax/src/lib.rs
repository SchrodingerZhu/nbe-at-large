pub mod lexical;
pub mod syntactic;

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
    Underline(&'a str),

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
