use grammar::syntactic::{ParseTree, Ptr};
use std::{rc::Rc, collections::HashMap};

#[derive(Clone, Debug)]
#[repr(transparent)]
pub struct Name(Rc<String>);

#[derive(Clone, Debug)]
pub struct RcPtr<T> {
    location: std::ops::Range<usize>,
    data: Rc<T>,
}

impl<T> std::ops::Deref for RcPtr<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.data.as_ref()
    }
}

// RcPtr because we may want to substitude
pub enum Term {
    Type,
    Variable(Name),
    Lam(Name, RcPtr<Self>),
    App(RcPtr<Self>, RcPtr<Self>),
    Pi(RcPtr<Self>, Name, RcPtr<Self>),
    Ann(RcPtr<Self>, RcPtr<Self>),
    Let(Name, RcPtr<Self>, RcPtr<Self>),
    UnitType,
    UnitIntro,
    BoolType,
    BoolIntro(bool),
    BoolElim(RcPtr<Self>, RcPtr<Self>, RcPtr<Self>),
    SigmaType(RcPtr<Self>, Name, RcPtr<Self>),
    SigmaIntro(RcPtr<Self>, RcPtr<Self>),
    SignaElim(Name, Name, RcPtr<Self>, RcPtr<Self>),
}

type Results<'a, T> = (
    Option<T>,
    Vec<ariadne::Report<(&'a str, std::ops::Range<usize>)>>,
);

struct SyntaxContext<'a> {
    source_name: &'a str,
    source: &'a str,
    variables: HashMap<&'a str, Name>
}

impl<'a> SyntaxContext<'a> {
    fn new(source_name: &'a str,
            source: &'a str) -> Self {
                Self {
                    source_name,
                    source,
                    variables: HashMap::new()
                }
    }   
    fn init_error(&self, offset: usize) -> ariadne::ReportBuilder<(&'a str, std::ops::Range<usize>)> 
    {
        ariadne::Report::build(ariadne::ReportKind::Error, self.source_name, offset)
    } 
    fn init_warning(&self, offset: usize) -> ariadne::ReportBuilder<(&'a str, std::ops::Range<usize>)> 
    {
        ariadne::Report::build(ariadne::ReportKind::Warning, self.source_name, offset)
    } 
}

impl Term {
    fn new_from_definition<'a>(ctx: &mut SyntaxContext<'a>, tree: &Ptr<ParseTree<'_>>) -> Results<'a, RcPtr<Self>> {
        use ariadne::*;
        match tree.data.as_ref() {
            ParseTree::Literal(_) => todo!(),
            ParseTree::Implicit(_) => todo!(),
            ParseTree::Import(_) => {
                let report = ctx.init_warning(tree.location.start)
                    .with_message("unsupported feature")
                    .with_label(Label::new((ctx.source_name, tree.location.clone())).with_color(Color::Yellow).with_message("import is not supported and will be ignored"))
                    .finish();
                (None, vec![report])
            },
            ParseTree::Module { .. } => unreachable!(),
            ParseTree::Underscore => todo!(),
            ParseTree::Variable { name, annotation } => todo!(),
            ParseTree::Type => todo!(),
            ParseTree::TypeExpr { name, params } => todo!(),
            ParseTree::Telescope { name, annotation } => todo!(),
            ParseTree::Arrow { lhs, rhs } => todo!(),
            ParseTree::TypeDecl {
                former,
                constructors,
            } => todo!(),
            ParseTree::TypeFormer { name, params } => todo!(),
            ParseTree::Constructor { name, r#type } => todo!(),
            ParseTree::FuncDecl { name, r#type } => todo!(),
            ParseTree::FuncDefine { name, params, body } => todo!(),
            ParseTree::FuncApply { func, args } => todo!(),
            ParseTree::Branch { r#if, then, r#else } => todo!(),
            ParseTree::PatternRule {
                constructor,
                variables,
                body,
            } => todo!(),
            ParseTree::PatternMatch { expr, rules } => todo!(),
            ParseTree::Let { var, binding, body } => todo!(),
            ParseTree::Lambda { params, body } => todo!(),
        }
    }

    fn new_from_module<'a>(
        source_name: &'a str,
        source: &'a str,
        tree: &Ptr<ParseTree<'_>>,
    ) -> Results<'a, Vec<RcPtr<Self>>> {
        match tree.data.as_ref() {
            ParseTree::Module { definitions, .. } => {
                let mut report = Vec::new();
                let mut translated = Vec::new();
                let mut ctx = SyntaxContext::new(source_name, source);
                for i in definitions {
                    let mut inner = Term::new_from_definition(&mut ctx, i);
                    inner.0.map(|x| translated.push(x));
                    report.append(&mut inner.1);
                }
                (Some(translated), report)
            }
            _ => unreachable!(),
        }
    }
}

trait AlphaEq {
    fn alpha_equal(&self, y: &Self) -> bool;
}

trait Subst: Sized {
    fn substitute(&self, name: &Name, with: &Self) -> Ptr<Self>;
}

#[test]
fn test() {
    let source = r#"
    module Test
    import A
    import B
"#;
    let parse_tree = grammar::syntactic::parse(source).0.unwrap();
    let module = Term::new_from_module("source.txt", source, &parse_tree);
    for i in module.1.iter() {
        i.eprint(("source.txt", ariadne::Source::from(source))).unwrap();
    }
}
