use ariadne::{Color, Label, Report, Span};
use std::cell::UnsafeCell;
use std::hash::{Hash, Hasher};
use std::{collections::HashMap, rc::Rc};

use crate::assert_unreachable;
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
    fn new<S: AsRef<str>>(name: S) -> Self {
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

#[derive(Debug)]
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
    SigmaIntro,
    SigmaElim(Name, Name, RcPtr<Self>, RcPtr<Self>),
}

pub enum Defintion {
    FuncDecl(Name, Term),
    FuncDefine(Name, Term),
}

impl Defintion {
    fn new_from_definition<'a>(
        ctx: &SyntaxContext<'a>,
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
            _ => assert_unreachable!(),
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
                    let mut inner = Self::new_from_definition(&mut ctx, i);
                    inner.0.map(|x| translated.push(x));
                    report.append(&mut inner.1);
                }
                (Some(translated), report)
            }
            _ => assert_unreachable!(),
        }
    }
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
    fn push_variable<'ctx>(&'ctx self, name: &'a str) -> (Name, Guard<'a, 'ctx>) {
        let unique_name = Name::new(name);
        let guard = Guard {
            context: self,
            replacement: unsafe {
                (*self.variables.get())
                    .insert(name, unique_name.clone())
                    .map(|x| (name, x))
            },
        };
        (unique_name, guard)
    }
}

impl<'src, 'ctx> Drop for Guard<'src, 'ctx> {
    fn drop(&mut self) {
        if let Some((name, value)) = self.replacement.take() {
            unsafe {
                (*self.context.variables.get()).insert(name, value);
            }
        }
    }
}

impl Term {
    fn new_from_type<'a>(
        ctx: &SyntaxContext<'a>,
        tree: &Ptr<ParseTree<'_>>,
    ) -> Results<'a, RcPtr<Self>> {
        todo!()
    }

    fn new_from_parameter<'a>(
        ctx: &SyntaxContext<'a>,
        tree: &Ptr<ParseTree<'a>>,
    ) -> Results<'a, Option<&'a str>> {
        match tree.data.as_ref() {
            ParseTree::Parameter { name, implicit } => {
                let name = name.get_literal();
                let mut reports = Vec::new();
                if *implicit {
                    let report = ctx.init_warning(tree.location.start)
                    .with_message("unsupported feature")
                    .with_label(ariadne::Label::new((ctx.source_name, tree.location.clone()))
                    .with_color(Color::Yellow)
                    .with_message(format!("implicit variable not supported, `{}` will be treated as explicit variable", name)))
                    .finish();
                    reports.push(report);
                }
                (Some(Some(name)), reports)
            }
            ParseTree::Underscore => (Some(None), Vec::new()),
            _ => assert_unreachable!(),
        }
    }

    fn new_from_expr<'a>(
        ctx: &SyntaxContext<'a>,
        tree: &Ptr<ParseTree<'a>>,
    ) -> Results<'a, RcPtr<Self>> {
        let location = tree.location.clone();
        match tree.data.as_ref() {
            ParseTree::Lambda { params, body } => Term::new_from_params_and_body(ctx, params, body),
            ParseTree::ConstructorRef(name) => match name.get_literal() {
                "Unit'" => (
                    Some(RcPtr {
                        location,
                        data: Rc::new(Term::UnitIntro),
                    }),
                    vec![],
                ),
                "Pair" => (
                    Some(RcPtr {
                        location,
                        data: Rc::new(Term::SigmaIntro),
                    }),
                    vec![],
                ),
                "True" => (
                    Some(RcPtr {
                        location,
                        data: Rc::new(Term::BoolIntro(true)),
                    }),
                    vec![],
                ),
                "False" => (
                    Some(RcPtr {
                        location,
                        data: Rc::new(Term::BoolIntro(false)),
                    }),
                    vec![],
                ),
                lit => {
                    let report = ctx
                        .init_error(location.start)
                        .with_message("unsupported feature")
                        .with_label(
                            ariadne::Label::new((ctx.source_name, location.clone()))
                                .with_color(Color::Red)
                                .with_message(format!("custom construct {} is not supported", lit)),
                        )
                        .finish();
                    (None, vec![report])
                }
            },
            ParseTree::Variable(_) => Term::new_from_variable(ctx, tree),
            ParseTree::FuncApply { func, args } => {
                let (func, mut reports) = Term::new_from_expr(ctx, func);
                let mut translated_args = Some(Vec::new());
                for i in args.iter() {
                    let (arg, mut arg_reports) = Term::new_from_expr(ctx, i);
                    reports.append(&mut arg_reports);
                    translated_args = translated_args.and_then(move |mut x| {
                        arg.map(|arg| {
                            x.push(arg);
                            x
                        })
                    });
                }
                let apply = func
                    .and_then(move |f| translated_args.map(move |args| (f, args)))
                    .and_then(move |(f, args)| {
                        let mut res = Some(f);
                        for i in args.into_iter() {
                            res = res.map(move |tree: RcPtr<Term>| RcPtr {
                                location: tree.location.start..i.location.end,
                                data: Rc::new(Term::App(tree, i)),
                            });
                        }
                        res
                    });
                (apply, reports)
            }
            ParseTree::TrustMe => {
                let term = RcPtr {
                    location,
                    data: Rc::new(Term::TrustMe),
                };
                (Some(term), vec![])
            }
            _ => assert_unreachable!(),
        }
    }

    fn new_from_params_and_body<'a>(
        ctx: &SyntaxContext<'a>,
        params: &Vec<Ptr<ParseTree<'a>>>,
        body: &Ptr<ParseTree<'a>>,
    ) -> Results<'a, RcPtr<Self>> {
        let mut guards = Vec::new();
        let mut reports = Vec::new();
        for i in params.iter().rev() {
            let (name, mut report) = Term::new_from_parameter(ctx, i);
            reports.append(&mut report);
            if let Some(Some(name)) = name {
                guards.push((i.location.clone(), Some(ctx.push_variable(name))));
            } else {
                guards.push((i.location.clone(), None));
            }
        }
        let (expr, mut report) = Term::new_from_expr(ctx, body);
        reports.append(&mut report);

        if let Some(mut expr) = expr {
            for mut i in guards.into_iter() {
                let name = i.1.take().map(|x| x.0);
                expr = RcPtr {
                    location: i.0.start..expr.location.end,
                    data: Rc::new(Term::Lam(name, expr)),
                };
            }
            (Some(expr), reports)
        } else {
            (None, reports)
        }
    }

    fn new_from_function_definition<'a>(
        ctx: &SyntaxContext<'a>,
        tree: &Ptr<ParseTree<'a>>,
    ) -> Results<'a, RcPtr<Self>> {
        match tree.data.as_ref() {
            ParseTree::FuncDefine { params, body, .. } => {
                Term::new_from_params_and_body(ctx, params, body)
            }
            _ => assert_unreachable!(),
        }
    }

    fn new_from_variable<'a>(
        ctx: &SyntaxContext<'a>,
        tree: &Ptr<ParseTree<'a>>,
    ) -> Results<'a, RcPtr<Self>> {
        fn unresolved_var<'a>(
            ctx: &SyntaxContext<'a>,
            tree: &Ptr<ParseTree<'a>>,
            name: &Ptr<ParseTree<'a>>,
        ) -> ariadne::Report<(&'a str, std::ops::Range<usize>)> {
            ctx.init_error(tree.location.start)
                .with_message("unresolved variable")
                .with_label(
                    ariadne::Label::new((ctx.source_name, name.location.clone()))
                        .with_color(ariadne::Color::Red)
                        .with_message(format!(
                            "variable {} cannot be resolved within scope",
                            name.get_literal()
                        )),
                )
                .finish()
        }
        match tree.data.as_ref() {
            ParseTree::Variable(name) => {
                let literal = name.get_literal();
                if let Some(var) = ctx.get_variable(literal) {
                    let term = {
                        let location = name.location.clone();
                        let data = Rc::new(Term::Variable(var));
                        RcPtr { location, data }
                    };
                    (Some(term), Vec::new())
                } else {
                    (None, vec![unresolved_var(ctx, tree, name)])
                }
            }
            _ => assert_unreachable!(),
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
        Nil : List<a>;
        Cons : a -> List<a> -> List<a>;
    }
"#;
    let parse_tree = grammar::syntactic::parse(source).0.unwrap();
    let module = Defintion::new_from_module("source.txt", source, &parse_tree);
    for i in module.1.iter() {
        i.eprint(("source.txt", ariadne::Source::from(source)))
            .unwrap();
    }
}

#[test]
fn test_2() {
    let source = r#"
    module Test
    test x = lambda y . (@Pair x y) 
"#;
    let parse_tree = grammar::syntactic::parse(source).1;
    eprintln!("{:#?}", parse_tree);
    let parse_tree = grammar::syntactic::parse(source).0.unwrap();
    let ctx = SyntaxContext::new("source.txt", source);
    if let ParseTree::Module { definitions, .. } = parse_tree.data.as_ref() {
        let func_def = Term::new_from_function_definition(&ctx, &definitions[0]);
        for i in func_def.1.iter() {
            i.eprint(("source.txt", ariadne::Source::from(source)))
                .unwrap();
        }
        println!("{:#?}", func_def.0)
    }
}
