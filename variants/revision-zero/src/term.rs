use std::{collections::HashMap, rc::Rc};
use std::cell::UnsafeCell;
use std::hash::{Hash, Hasher};
use ariadne::{Color, Span};

use grammar::syntactic::{ParseTree, Ptr};

#[derive(Clone, Debug)]
#[repr(transparent)]
pub struct Name(Rc<String>);

impl PartialEq for Name {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl Hash for Name {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Rc::as_ptr(&self.0).hash(state);
    }
}

impl Name {
    fn new<S : AsRef<str>>(name : S) -> Self {
        Name(Rc::new(name.as_ref().to_string()))
    }
}

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

// RcPtr because we may want to substitute
pub enum Term {
    Type,
    Variable(Name),
    Lam(Option<Name>, RcPtr<Self>),
    App(RcPtr<Self>, RcPtr<Self>),
    Pi(RcPtr<Self>, Option<Name>, RcPtr<Self>),
    Ann(RcPtr<Self>, RcPtr<Self>),
    Let(Name, RcPtr<Self>, RcPtr<Self>),
    TrustMe,
    BottomType,
    BottomElim,
    UnitType,
    UnitIntro,
    UnitElim(RcPtr<Self>),
    BoolType,
    BoolIntro(bool),
    BoolElim(RcPtr<Self>, RcPtr<Self>, RcPtr<Self>),
    SigmaType(RcPtr<Self>, Name, RcPtr<Self>),
    SigmaIntro(RcPtr<Self>, RcPtr<Self>),
    SigmaElim(Name, Name, RcPtr<Self>, RcPtr<Self>),
}

pub enum Defintion {
    FuncDecl(Name, Term),
    FuncDefine(Name, Term)
}

type Results<'a, T> = (
    Option<T>,
    Vec<ariadne::Report<(&'a str, std::ops::Range<usize>)>>,
);

struct SyntaxContext<'a> {
    source_name: &'a str,
    source: &'a str,
    variables: UnsafeCell<HashMap<&'a str, Name>>,
}

struct Guard<'src, 'ctx> {
    context: &'ctx SyntaxContext<'src>,
    replacement: Option<(&'src str, Name)>,
}

impl<'a> SyntaxContext<'a> {
    fn new(source_name: &'a str, source: &'a str) -> Self {
        Self {
            source_name,
            source,
            variables: UnsafeCell::new(HashMap::new()),
        }
    }
    fn init_error(
        &self,
        offset: usize,
    ) -> ariadne::ReportBuilder<(&'a str, std::ops::Range<usize>)> {
        ariadne::Report::build(ariadne::ReportKind::Error, self.source_name, offset)
    }
    fn init_warning(
        &self,
        offset: usize,
    ) -> ariadne::ReportBuilder<(&'a str, std::ops::Range<usize>)> {
        ariadne::Report::build(ariadne::ReportKind::Warning, self.source_name, offset)
    }
    fn get_variable(&self, name: &str) -> Option<Name> {
        unsafe {
            let map = &*self.variables.get();
            map.get(name).cloned()
        }
    }
    fn push_variable<'ctx>(&'ctx self, name: &'a str) -> Guard<'a, 'ctx> {
        Guard {
            context: self,
            replacement: unsafe {
                (*self.variables.get()).insert(name, Name::new(name))
                    .map(|x| (name, x))
            }
        }
    }
}

impl Term {
    fn new_from_type<'a>(
        ctx: &mut SyntaxContext<'a>,
        tree: &Ptr<ParseTree<'_>>,
    ) -> Results<'a, RcPtr<Self>> {
        todo!()
    }

    fn new_from_expr<'a>(
        ctx: &mut SyntaxContext<'a>,
        tree: &Ptr<ParseTree<'_>>,
    ) -> Results<'a, RcPtr<Self>> {
        todo!()
    }

    fn new_from_variable<'a>(
        ctx: &mut SyntaxContext<'a>,
        tree: &Ptr<ParseTree<'a>>,
    ) -> Results<'a, RcPtr<Self>> {
        fn unresolved_var<'a>(ctx: &SyntaxContext<'a>, tree: &Ptr<ParseTree<'a>>, name: &Ptr<ParseTree<'a>>) -> ariadne::Report<(&'a str, std::ops::Range<usize>)> {
            ctx.init_error(tree.location.start)
                .with_message("unresolved variable")
                .with_label(ariadne::Label::new((ctx.source_name, name.location.clone()))
                    .with_color(ariadne::Color::Red)
                    .with_message(format!("variable {} cannot be resolved within scope", name.get_literal())))
                .finish()
        }
        match tree.data.as_ref() {
            ParseTree::Variable(name) => {
                let literal = name.get_literal();
                if let Some(var) = ctx.get_variable(literal) {
                    let term =  {
                        let location = name.location.clone();
                        let data = Rc::new(Term::Variable(var));
                        RcPtr {
                            location,
                            data
                        }
                    };
                    (Some(term), Vec::new())
                } else {
                    (None, vec![unresolved_var(ctx, tree, name)])
                }
            }
            _ => unreachable!()
        }
    }

    fn new_from_definition<'a>(
        ctx: &mut SyntaxContext<'a>,
        tree: &Ptr<ParseTree<'_>>,
    ) -> Results<'a, RcPtr<Self>> {
        use ariadne::*;
        match tree.data.as_ref() {
            ParseTree::Import(_) => {
                let report = ctx
                    .init_warning(tree.location.start)
                    .with_message("unsupported feature")
                    .with_label(
                        Label::new((ctx.source_name, tree.location.clone()))
                            .with_color(Color::Yellow)
                            .with_message("import is not supported and will be ignored"),
                    )
                    .finish();
                (None, vec![report])
            }
            ParseTree::TypeDecl { .. } => {
                let report = ctx
                    .init_warning(tree.location.start)
                    .with_message("unsupported feature")
                    .with_label(
                        Label::new((ctx.source_name, tree.location.clone()))
                            .with_color(Color::Yellow)
                            .with_message("custom data type is not supported and will be ignored"),
                    )
                    .finish();
                (None, vec![report])
            }
            ParseTree::FuncDecl { name, r#type } => {
                todo!()
            }
            ParseTree::FuncDefine { name, params, body } => {
                todo!()
            }
            _ => unreachable!(),
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
    data List (a : Type) = {
        Nil : List a;
        Cons : a -> List a -> List a;
    }
"#;
    let parse_tree = grammar::syntactic::parse(source).0.unwrap();
    let module = Term::new_from_module("source.txt", source, &parse_tree);
    for i in module.1.iter() {
        i.eprint(("source.txt", ariadne::Source::from(source)))
            .unwrap();
    }
}
