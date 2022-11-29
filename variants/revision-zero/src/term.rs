use ariadne::{Color, Label, Report, Span};
use std::cell::{Cell, UnsafeCell};
use std::hash::{Hash, Hasher};
use std::ops::Range;
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
    location: Range<usize>,
    data: Rc<T>,
}

impl<T> RcPtr<T> {
    fn new(location: std::ops::Range<usize>, data: T) -> Self {
        Self {
            location,
            data: Rc::new(data),
        }
    }
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
    SigmaIntro(RcPtr<Self>, RcPtr<Self>),
    SigmaElim(Name, Name, RcPtr<Self>, RcPtr<Self>),
}

pub enum Definition {
    FuncDecl(Name, Term),
    FuncDefine(Name, Term),
}

impl Definition {
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
                (None, vec![report]).into()
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
                (None, vec![report]).into()
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
                    inner.tree.map(|x| translated.push(x));
                    report.append(&mut inner.reports);
                }
                (Some(translated), report).into()
            }
            _ => assert_unreachable!(),
        }
    }
}

struct Results<'a, T> {
    tree: Option<T>,
    reports: Vec<Report<(&'a str, std::ops::Range<usize>)>>,
}

impl<'a, T> From<(Option<T>, Vec<Report<(&'a str, Range<usize>)>>)> for Results<'a, T> {
    fn from(value: (Option<T>, Vec<Report<(&'a str, Range<usize>)>>)) -> Self {
        Results {
            tree: value.0,
            reports: value.1,
        }
    }
}

impl<'a, T> From<Option<T>> for Results<'a, T> {
    fn from(value: Option<T>) -> Self {
        Results {
            tree: value,
            reports: Vec::new(),
        }
    }
}

impl<'a, T> From<RcPtr<T>> for Results<'a, RcPtr<T>> {
    fn from(value: RcPtr<T>) -> Self {
        Results {
            tree: Some(value),
            reports: Vec::new(),
        }
    }
}

impl<'a, T> From<Vec<Report<(&'a str, Range<usize>)>>> for Results<'a, T> {
    fn from(value: Vec<Report<(&'a str, Range<usize>)>>) -> Self {
        Results {
            tree: None,
            reports: value,
        }
    }
}

impl<'a, T> From<Report<(&'a str, Range<usize>)>> for Results<'a, T> {
    fn from(value: Report<(&'a str, Range<usize>)>) -> Self {
        Results {
            tree: None,
            reports: vec![value],
        }
    }
}

impl<'a, T> Results<'a, T> {
    fn to_tuple(self) -> (Option<T>, Vec<Report<(&'a str, Range<usize>)>>) {
        (self.tree, self.reports)
    }
    fn and_then_optional<F>(mut self, f: F) -> Self
    where
        F: FnOnce(Option<T>) -> Self,
    {
        let mut results = f(self.tree);
        results.reports.append(&mut self.reports);
        results
    }
    fn and_then_mandatory<F>(mut self, f: F) -> Self
    where
        F: FnOnce(T) -> Self,
    {
        match self.tree.map(f) {
            Some(mut results) => {
                results.reports.append(&mut self.reports);
                results
            }
            None => (None, self.reports).into(),
        }
    }
    fn map_optional<F>(self, f: F) -> Self
    where
        F: FnOnce(Option<T>) -> Option<T>,
    {
        Results {
            tree: f(self.tree),
            ..self
        }
    }
    fn and_then_inside_optional<F>(self, f: F) -> Self
    where
        F: FnOnce(T) -> Option<T>,
    {
        Results {
            tree: self.tree.and_then(f),
            ..self
        }
    }
    fn map_inside_optional<F>(self, f: F) -> Self
    where
        F: FnOnce(T) -> T,
    {
        Results {
            tree: self.tree.map(f),
            ..self
        }
    }
}

struct SyntaxContext<'a> {
    source_name: &'a str,
    source: &'a str,
    variables: UnsafeCell<HashMap<&'a str, Name>>,
    fresh_counter: Cell<usize>,
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
            fresh_counter: Cell::new(0),
        }
    }
    fn init_error(
        &self,
        offset: usize,
    ) -> ariadne::ReportBuilder<(&'a str, std::ops::Range<usize>)> {
        Report::build(ariadne::ReportKind::Error, self.source_name, offset)
    }
    fn init_warning(
        &self,
        offset: usize,
    ) -> ariadne::ReportBuilder<(&'a str, std::ops::Range<usize>)> {
        Report::build(ariadne::ReportKind::Warning, self.source_name, offset)
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

    fn fresh(&self) -> Name {
        let counter = self.fresh_counter.get();
        self.fresh_counter.replace(counter + 1);
        Name::new(format!("fresh_{}", counter))
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
                (Some(Some(name)), reports).into()
            }
            ParseTree::Underscore => Some(None).into(),
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
                "Unit'" => RcPtr::new(location, Term::UnitIntro).into(),
                "Pair" => {
                    let a = ctx.fresh();
                    let b = ctx.fresh();
                    let var_a = RcPtr::new(location.clone(), Term::Variable(a.clone()));
                    let var_b = RcPtr::new(location.clone(), Term::Variable(b.clone()));
                    let sigma = RcPtr::new(location.clone(), Term::SigmaIntro(var_a, var_b));
                    let lambda = RcPtr::new(location.clone(), Term::Lam(Some(b), sigma));
                    let lambda = RcPtr {
                        location,
                        data: Rc::new(Term::Lam(Some(a), lambda)),
                    };
                    (Some(lambda), vec![]).into()
                }
                "True" => (
                    Some(RcPtr {
                        location,
                        data: Rc::new(Term::BoolIntro(true)),
                    }),
                    vec![],
                )
                    .into(),
                "False" => (
                    Some(RcPtr {
                        location,
                        data: Rc::new(Term::BoolIntro(false)),
                    }),
                    vec![],
                )
                    .into(),
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
                    (None, vec![report]).into()
                }
            },
            ParseTree::Let { var, binding, body } => {
               Term::new_from_expr(ctx, binding).and_then_optional(|mut binding| {
                   match var.data.as_ref() {
                       ParseTree::AnnotableVariable { name, annotation } => {
                           let (name, _guard) = ctx.push_variable(name.get_literal());
                           Term::new_from_expr(ctx, body).and_then_optional(|body| {
                               let mut reports = Vec::new();
                               if let Some(ann) = annotation {
                                   let (ann, ann_reports) = Term::new_from_type(ctx, ann).to_tuple();
                                   reports = ann_reports;
                                   binding = binding.and_then(move |binding| {
                                       ann.map(|ann| {
                                           RcPtr::new(
                                               binding.location.start..ann.location.end,
                                               Term::Ann(binding, ann),
                                           )
                                       })
                                   });
                               }
                               let expr = binding.and_then(move |binding| {
                                   body.map(move |body| {
                                       RcPtr::new(tree.location.clone(), Term::Let(name, binding, body))
                                   })
                               });
                               (expr, reports).into()
                           })
                       }
                       _ => assert_unreachable!(),
                   }
               })
            }
            ParseTree::Variable(_) => Term::new_from_variable(ctx, tree),
            ParseTree::FuncApply { func, args } => {
               Term::new_from_expr(ctx, func).and_then_optional(|func| {
                   let mut reports = Vec::new();
                   let mut translated_args = Some(Vec::new());
                   for i in args.iter() {
                       let (arg, mut arg_reports) = Term::new_from_expr(ctx, i).to_tuple();
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
                               res = res.map(move |tree: RcPtr<Term>| {
                                   RcPtr::new(tree.location.start..i.location.end, Term::App(tree, i))
                               });
                           }
                           res
                       });
                   (apply, reports).into()
               })
            }
            ParseTree::TrustMe => {
                let term = RcPtr {
                    location,
                    data: Rc::new(Term::TrustMe),
                };
                (Some(term), vec![]).into()
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
            let (name, mut report) = Term::new_from_parameter(ctx, i).to_tuple();
            reports.append(&mut report);
            if let Some(Some(name)) = name {
                guards.push((i.location.clone(), Some(ctx.push_variable(name))));
            } else {
                guards.push((i.location.clone(), None));
            }
        }
        let (expr, mut report) = Term::new_from_expr(ctx, body).to_tuple();
        reports.append(&mut report);

        if let Some(mut expr) = expr {
            for mut i in guards.into_iter() {
                let name = i.1.take().map(|x| x.0);
                expr = RcPtr::new(i.0.start..expr.location.end, Term::Lam(name, expr));
            }
            (Some(expr), reports).into()
        } else {
            (None, reports).into()
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
                    (Some(term), Vec::new()).into()
                } else {
                    (None, vec![unresolved_var(ctx, tree, name)]).into()
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
    let module = Definition::new_from_module("source.txt", source, &parse_tree);
    for i in module.reports.iter() {
        i.eprint(("source.txt", ariadne::Source::from(source)))
            .unwrap();
    }
}

#[test]
fn test_2() {
    let source = r#"
    module Test
    test x = let u = lambda y . (@Pair x y) in u 
"#;
    let parse_tree = grammar::syntactic::parse(source).1;
    eprintln!("{:#?}", parse_tree);
    let parse_tree = grammar::syntactic::parse(source).0.unwrap();
    let ctx = SyntaxContext::new("source.txt", source);
    if let ParseTree::Module { definitions, .. } = parse_tree.data.as_ref() {
        let func_def = Term::new_from_function_definition(&ctx, &definitions[0]);
        for i in func_def.reports.iter() {
            i.eprint(("source.txt", ariadne::Source::from(source)))
                .unwrap();
        }
        println!("{:?}", func_def.tree)
    }
}
