use crate::assert_unreachable;
use crate::builtin::{BuiltinBool, BuiltinBottom, BuiltinPair, BuiltinType, BuiltinUnit};
use ariadne::{Color, Label, Report, ReportBuilder};
use grammar::syntactic::{ParseTree, Ptr};
use std::cell::{Cell, UnsafeCell};
use std::collections::hash_map::Entry;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::ops::Range;
use std::{collections::HashMap, rc::Rc};

#[derive(Clone, Debug, Eq)]
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

#[derive(Debug)]
pub struct RcPtr<T> {
    location: Range<usize>,
    data: Rc<T>,
}

impl<T> Clone for RcPtr<T> {
    fn clone(&self) -> Self {
        Self {
            location: self.location.clone(),
            data: self.data.clone(),
        }
    }
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

type NamedSpan<'a> = (&'a str, Range<usize>);

impl<T: std::fmt::Display> std::fmt::Display for RcPtr<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.data.fmt(f)
    }
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Type => {
                write!(f, "Type")
            }
            Term::Variable(name) => std::fmt::Display::fmt(name.0.as_str(), f),
            Term::Lam(x, y) => match x {
                Some(n) => write!(f, "(λ {} . {})", n.0, y),
                None => write!(f, "(λ _ . {})", y),
            },
            Term::App(x, y) => {
                write!(f, "({} {})", x, y)
            }
            Term::Pi(x, y) => {
                write!(f, "(∏ {} {})", x, y)
            }
            Term::Ann(x, y) => {
                write!(f, "({} : {})", x, y)
            }
            Term::Let(x, y, z) => match x {
                Some(n) => write!(f, "(let {} = {} in {})", n.0, y, z),
                None => write!(f, "(let _ = {} in {})", y, z),
            },
            Term::TrustMe => {
                write!(f, "!!")
            }
            Term::BottomType => {
                write!(f, "𝟘")
            }
            Term::BottomElim(e) => {
                write!(f, "(𝟘-elim {})", e)
            }
            Term::UnitType => {
                write!(f, "𝟙")
            }
            Term::UnitIntro => {
                write!(f, "🟉")
            }
            Term::UnitElim(x, y) => {
                write!(f, "(𝟙-elim {} {})", x, y)
            }
            Term::BoolType => {
                write!(f, "𝟚")
            }
            Term::BoolIntro(x) => match x {
                true => write!(f, "True"),
                false => write!(f, "False"),
            },
            Term::BoolElim(x, y, z) => {
                write!(f, "(𝟚-elim {} {} {})", x, y, z)
            }
            Term::SigmaType(x, y) => {
                write!(f, "(∑ {} {})", x, y)
            }
            Term::SigmaIntro(x, y) => {
                write!(f, "({} , {})", x, y)
            }
            Term::SigmaElim(a, b, c, d) => {
                let b = b.as_ref().map(|x| x.0.as_str()).unwrap_or("_");
                let c = c.as_ref().map(|x| x.0.as_str()).unwrap_or("_");
                write!(f, "(let ({}, {}) = {} in {})", b, c, a, d)
            }
        }
    }
}

#[derive(Debug)]
// RcPtr because we may want to substitute
pub enum Term {
    Type,
    Variable(Name),
    Lam(Option<Name>, RcPtr<Self>),
    App(RcPtr<Self>, RcPtr<Self>),
    Pi(RcPtr<Self>, RcPtr<Self>),
    Ann(RcPtr<Self>, RcPtr<Self>),
    Let(Option<Name>, RcPtr<Self>, RcPtr<Self>),
    TrustMe,
    BottomType,
    BottomElim(RcPtr<Self>),
    UnitType,
    UnitIntro,
    UnitElim(RcPtr<Self>, RcPtr<Self>),
    BoolType,
    BoolIntro(bool),
    BoolElim(RcPtr<Self>, RcPtr<Self>, RcPtr<Self>),
    SigmaType(RcPtr<Self>, RcPtr<Self>),
    SigmaIntro(RcPtr<Self>, RcPtr<Self>),
    SigmaElim(RcPtr<Self>, Option<Name>, Option<Name>, RcPtr<Self>),
}

#[derive(Debug)]
pub struct Definition {
    pub name: Name,
    pub term: RcPtr<Term>,
}

impl Definition {
    pub(crate) fn new_from_module<'a>(
        source_name: &'a str,
        tree: &Ptr<ParseTree<'a>>,
    ) -> (Vec<Definition>, Vec<Report<NamedSpan<'a>>>) {
        match tree.data.as_ref() {
            ParseTree::Module { definitions, .. } => {
                let context = SyntaxContext::new(source_name);
                let records = scan_module_definitions(&context, definitions.as_slice());
                let mut global_guards = Vec::new();
                let mut definitions = Vec::new();
                if let Some(map) = records.as_ref() {
                    for i in map {
                        global_guards.push(context.push_variable(i.0));
                    }
                    for i in global_guards.iter() {
                        let name = i.0.clone();
                        let i = unsafe { map.get(name.0.as_str()).unwrap_unchecked() };
                        let type_tree = unsafe { i.0.as_ref().unwrap_unchecked() };
                        let def_tree = unsafe { i.1.as_ref().unwrap_unchecked() };
                        let term = Term::new_from_expr(&context, type_tree).and_then(|decl| {
                            Term::new_from_function_definition(&context, def_tree).map(move |def| {
                                RcPtr::new(def_tree.location.clone(), Term::Ann(def, decl))
                            })
                        });
                        if let Some(term) = term {
                            definitions.push(Definition { name, term });
                        }
                    }
                }
                drop(global_guards);
                (definitions, context.take_reports())
            }
            _ => assert_unreachable!(),
        }
    }
}

pub(crate) struct SyntaxContext<'a> {
    pub source_name: &'a str,
    variables: UnsafeCell<HashMap<&'a str, Name>>,
    fresh_counter: Cell<usize>,
    reports: UnsafeCell<Vec<Report<NamedSpan<'a>>>>,
}

pub(crate) struct Guard<'src, 'ctx> {
    context: &'ctx SyntaxContext<'src>,
    replacement: Option<(&'src str, Name)>,
}

impl<'a> SyntaxContext<'a> {
    pub(crate) fn new(source_name: &'a str) -> Self {
        Self {
            source_name,
            variables: UnsafeCell::new(HashMap::new()),
            fresh_counter: Cell::new(0),
            reports: UnsafeCell::new(Vec::new()),
        }
    }
    pub(crate) fn add_report(&self, report: Report<NamedSpan<'a>>) {
        unsafe { (*self.reports.get()).push(report) }
    }
    pub(crate) fn reports(&self) -> &[Report<NamedSpan<'a>>] {
        unsafe { (*self.reports.get()).as_slice() }
    }
    pub(crate) fn take_reports(self) -> Vec<Report<NamedSpan<'a>>> {
        self.reports.into_inner()
    }
    pub(crate) fn error<F>(&self, offset: usize, f: F)
    where
        F: FnOnce(ReportBuilder<NamedSpan<'a>>) -> Report<NamedSpan<'a>>,
    {
        self.add_report(f(Report::build(
            ariadne::ReportKind::Error,
            self.source_name,
            offset,
        )))
    }
    pub(crate) fn warning<F>(&self, offset: usize, f: F)
    where
        F: FnOnce(ReportBuilder<NamedSpan<'a>>) -> Report<NamedSpan<'a>>,
    {
        self.add_report(f(Report::build(
            ariadne::ReportKind::Warning,
            self.source_name,
            offset,
        )))
    }

    pub(crate) fn get_variable(&self, name: &str) -> Option<Name> {
        unsafe {
            let map = &*self.variables.get();
            map.get(name).cloned()
        }
    }
    pub(crate) fn push_variable<'ctx>(&'ctx self, name: &'a str) -> (Name, Guard<'a, 'ctx>) {
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

    pub(crate) fn fresh(&self) -> Name {
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
    pub(crate) fn new_from_parameter<'a>(
        ctx: &SyntaxContext<'a>,
        tree: &Ptr<ParseTree<'a>>,
    ) -> Option<&'a str> {
        match tree.data.as_ref() {
            ParseTree::Parameter { name, implicit } => {
                let name = name.get_literal();
                if *implicit {
                    ctx.warning(tree.location.start, |builder|
                        builder.with_message("unsupported feature")
                        .with_label(Label::new((ctx.source_name, tree.location.clone()))
                        .with_color(Color::Yellow)
                        .with_message(format!("implicit variable not supported, `{}` will be treated as explicit variable", name)))
                        .finish());
                }
                Some(name)
            }
            ParseTree::Underscore => None,
            _ => assert_unreachable!(),
        }
    }

    pub(crate) fn new_from_expr<'a>(
        ctx: &SyntaxContext<'a>,
        tree: &Ptr<ParseTree<'a>>,
    ) -> Option<RcPtr<Self>> {
        let location = tree.location.clone();
        match tree.data.as_ref() {
            ParseTree::Lambda { params, body } => Term::new_from_params_and_body(ctx, params, body),
            ParseTree::ConstructorRef(name) => match name.get_literal() {
                "Unit" => Some(RcPtr::new(location, Term::UnitIntro)),
                "Pair" => {
                    let a = ctx.fresh();
                    let b = ctx.fresh();
                    let var_a = RcPtr::new(location.clone(), Term::Variable(a.clone()));
                    let var_b = RcPtr::new(location.clone(), Term::Variable(b.clone()));
                    let sigma = RcPtr::new(location.clone(), Term::SigmaIntro(var_a, var_b));
                    let lambda = RcPtr::new(location.clone(), Term::Lam(Some(b), sigma));
                    let lambda = RcPtr::new(location, Term::Lam(Some(a), lambda));
                    Some(lambda)
                }
                "True" => Some(RcPtr::new(location, Term::BoolIntro(true))),
                "False" => Some(RcPtr::new(location, Term::BoolIntro(false))),
                lit => {
                    ctx.error(location.start, |builder| {
                        builder
                            .with_message("unsupported feature")
                            .with_label(
                                ariadne::Label::new((ctx.source_name, location.clone()))
                                    .with_color(Color::Red)
                                    .with_message(format!(
                                        "custom constructor {} is not supported",
                                        lit
                                    )),
                            )
                            .finish()
                    });
                    None
                }
            },
            ParseTree::Let {
                var,
                binding: binding_tree,
                body,
                recursive,
            } => {
                let mut binding = None;

                match var.data.as_ref() {
                    ParseTree::AnnotableVariable { name, annotation } => {
                        if !*recursive {
                            binding = Term::new_from_expr(ctx, binding_tree);
                        }
                        let (name, _guard) = name
                            .as_ref()
                            .map(|name| ctx.push_variable(name.get_literal()))
                            .map(|(x, y)| (Some(x), Some(y)))
                            .unwrap_or((None, None));
                        if *recursive {
                            binding = Term::new_from_expr(ctx, binding_tree);
                        }
                        let body = Term::new_from_expr(ctx, body);
                        if let Some(ann) = annotation {
                            let ann = Term::new_from_expr(ctx, ann);
                            binding = binding.and_then(move |binding| {
                                ann.map(|ann| {
                                    RcPtr::new(
                                        binding.location.start..ann.location.end,
                                        Term::Ann(binding, ann),
                                    )
                                })
                            });
                        }
                        binding.and_then(move |binding| {
                            body.map(move |body| {
                                RcPtr::new(tree.location.clone(), Term::Let(name, binding, body))
                            })
                        })
                    }
                    _ => assert_unreachable!(),
                }
            }
            ParseTree::Variable(_) => Term::new_from_variable(ctx, tree),
            ParseTree::FuncApply { func, args } => {
                let func = Term::new_from_expr(ctx, func);
                let mut translated_args = Some(Vec::new());
                for i in args.iter() {
                    let arg = Term::new_from_expr(ctx, i);
                    translated_args = translated_args.and_then(move |mut x| {
                        arg.map(|arg| {
                            x.push(arg);
                            x
                        })
                    });
                }
                func.and_then(move |f| translated_args.map(move |args| (f, args)))
                    .and_then(move |(f, args)| {
                        let mut res = Some(f);
                        for i in args.into_iter() {
                            res = res.map(move |tree: RcPtr<Term>| {
                                RcPtr::new(tree.location.start..i.location.end, Term::App(tree, i))
                            });
                        }
                        res
                    })
            }
            ParseTree::PatternMatch { expr, rules } => {
                let expr = Term::new_from_expr(ctx, expr);
                if expr.is_none() {
                    return None;
                }
                let expr = unsafe { expr.unwrap_unchecked() };
                match BuiltinUnit::new_from_pattern_rules(ctx, rules.as_slice()) {
                    Ok(None) => (),
                    Ok(Some(rule)) => {
                        return Some(RcPtr::new(location, Term::UnitElim(expr, rule)));
                    }
                    Err(_) => return None,
                }
                match BuiltinBottom::new_from_pattern_rules(ctx, rules.as_slice()) {
                    Ok(None) => (),
                    Ok(Some(_)) => {
                        return Some(RcPtr::new(location, Term::BottomElim(expr)));
                    }
                    Err(_) => return None,
                }
                match BuiltinPair::new_from_pattern_rules(ctx, rules.as_slice()) {
                    Ok(None) => (),
                    Ok(Some((left, right, body))) => {
                        return Some(RcPtr::new(
                            location,
                            Term::SigmaElim(expr, left, right, body),
                        ));
                    }
                    Err(_) => return None,
                }
                match BuiltinBool::new_from_pattern_rules(ctx, rules.as_slice()) {
                    Ok(None) => (),
                    Ok(Some((r#true, r#false))) => {
                        return Some(RcPtr::new(location, Term::BoolElim(expr, r#true, r#false)));
                    }
                    Err(_) => return None,
                }
                ctx.error(location.start, |builder| {
                    builder
                        .with_message("unsupported feature")
                        .with_label(Label::new((ctx.source_name, location.clone()))
                            .with_color(Color::Red)
                            .with_message("only pattern matchings on Sigma, Unit, Bottom, Bool are supported"))
                        .finish()
                });
                None
            }
            ParseTree::TrustMe => Some(RcPtr::new(location, Term::TrustMe)),
            ParseTree::Type => Some(RcPtr::new(location, Term::Type)),
            ParseTree::Sigma { left, right } => match left.data.as_ref() {
                ParseTree::Telescope {
                    name, annotation, ..
                } => {
                    let (name, _guard) = ctx.push_variable(name.get_literal());
                    let left = Term::new_from_expr(ctx, annotation);
                    let right = Term::new_from_expr(ctx, right);
                    left.and_then(move |left| {
                        right.map(move |right| {
                            RcPtr::new(
                                location.clone(),
                                Term::SigmaType(
                                    left,
                                    RcPtr::new(location.clone(), Term::Lam(Some(name), right)),
                                ),
                            )
                        })
                    })
                }
                _ => {
                    let left = Term::new_from_expr(ctx, left);
                    let right = Term::new_from_expr(ctx, right);
                    left.and_then(move |left| {
                        right.map(move |right| {
                            RcPtr::new(
                                location.clone(),
                                Term::SigmaType(
                                    left,
                                    RcPtr::new(location.clone(), Term::Lam(None, right)),
                                ),
                            )
                        })
                    })
                }
            },
            ParseTree::Arrow { left, right } => match left.data.as_ref() {
                ParseTree::Telescope {
                    name, annotation, ..
                } => {
                    let (name, _guard) = ctx.push_variable(name.get_literal());
                    let left = Term::new_from_expr(ctx, annotation);
                    let right = Term::new_from_expr(ctx, right);
                    left.and_then(move |left| {
                        right.map(move |right| {
                            RcPtr::new(
                                location.clone(),
                                Term::Pi(
                                    left,
                                    RcPtr::new(location.clone(), Term::Lam(Some(name), right)),
                                ),
                            )
                        })
                    })
                }
                _ => {
                    let left = Term::new_from_expr(ctx, left);
                    let right = Term::new_from_expr(ctx, right);
                    left.and_then(move |left| {
                        right.map(move |right| {
                            RcPtr::new(
                                location.clone(),
                                Term::Pi(
                                    left,
                                    RcPtr::new(location.clone(), Term::Lam(None, right)),
                                ),
                            )
                        })
                    })
                }
            },
            ParseTree::TypeRef(name) => match name.get_literal() {
                "Unit" => Some(RcPtr::new(location, Term::UnitType)),
                "Bottom" => Some(RcPtr::new(location, Term::BottomType)),
                "Bool" => Some(RcPtr::new(location, Term::BoolType)),
                "Sigma" => {
                    let a = ctx.fresh();
                    let b = ctx.fresh();
                    let var_a = RcPtr::new(location.clone(), Term::Variable(a.clone()));
                    let var_b = RcPtr::new(location.clone(), Term::Variable(b.clone()));
                    let sigma = RcPtr::new(location.clone(), Term::SigmaType(var_a, var_b));
                    let lambda = RcPtr::new(location.clone(), Term::Lam(Some(b), sigma));
                    let lambda = RcPtr::new(location, Term::Lam(Some(a), lambda));
                    Some(lambda)
                }
                _ => {
                    ctx.error(location.start, |builder| {
                        builder
                            .with_message("unsupported feature")
                            .with_label(
                                Label::new((ctx.source_name, location))
                                    .with_color(Color::Red)
                                    .with_message(format!(
                                        "custom type {} is not supported",
                                        name.get_literal()
                                    )),
                            )
                            .finish()
                    });
                    None
                }
            },
            _ => assert_unreachable!("{:#?}", tree),
        }
    }

    pub(crate) fn new_from_params_and_body<'a>(
        ctx: &SyntaxContext<'a>,
        params: &Vec<Ptr<ParseTree<'a>>>,
        body: &Ptr<ParseTree<'a>>,
    ) -> Option<RcPtr<Self>> {
        let mut guards = Vec::new();
        for i in params.iter().rev() {
            let name = Term::new_from_parameter(ctx, i);
            if let Some(name) = name {
                guards.push((i.location.clone(), Some(ctx.push_variable(name))));
            } else {
                guards.push((i.location.clone(), None));
            }
        }
        Term::new_from_expr(ctx, body).map(|mut expr| {
            for mut i in guards.into_iter() {
                let name = i.1.take().map(|x| x.0);
                expr = RcPtr::new(i.0.start..expr.location.end, Term::Lam(name, expr));
            }
            expr
        })
    }

    pub(crate) fn new_from_function_definition<'a>(
        ctx: &SyntaxContext<'a>,
        tree: &Ptr<ParseTree<'a>>,
    ) -> Option<RcPtr<Self>> {
        match tree.data.as_ref() {
            ParseTree::FuncDefine { params, body, .. } => {
                Term::new_from_params_and_body(ctx, params, body)
            }
            _ => assert_unreachable!(),
        }
    }

    pub(crate) fn new_from_variable<'a>(
        ctx: &SyntaxContext<'a>,
        tree: &Ptr<ParseTree<'a>>,
    ) -> Option<RcPtr<Self>> {
        match tree.data.as_ref() {
            ParseTree::Variable(name) => {
                let literal = name.get_literal();
                if let Some(var) = ctx.get_variable(literal) {
                    let term = {
                        let location = name.location.clone();
                        let data = Term::Variable(var);
                        RcPtr::new(location, data)
                    };
                    Some(term)
                } else {
                    ctx.error(tree.location.start, |builder| {
                        builder
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
                    });
                    None
                }
            }
            _ => assert_unreachable!(),
        }
    }
}

struct EvaluationContext {
    // local: HashMap<Name, RcPtr<Term>>,
    // remote: HashMap<Name, RcPtr<Term>>
}

impl Term {
    fn alpha_equal(&self, other: &Self) -> bool {
        struct UnificationContext(UnsafeCell<HashMap<Name, Name>>);
        struct Guard<'a>(&'a UnificationContext, Name);
        impl UnificationContext {
            fn unify(&self, x: Name, y: Name) -> Guard {
                unsafe { (*self.0.get()).insert(x.clone(), y) };
                Guard(self, x)
            }
            fn check(&self, x: &Name, y: &Name) -> bool {
                unsafe { (*self.0.get()).get(x).map(|x| x == y).unwrap_or(false) }
            }
        }
        impl<'a> Drop for Guard<'a> {
            fn drop(&mut self) {
                unsafe {
                    (*self.0 .0.get()).remove(&self.1);
                }
            }
        }
        fn alpha_equal_impl(a: &Term, b: &Term, ctx: &UnificationContext) -> bool {
            match (a, b) {
                (Term::Type, Term::Type)
                | (Term::TrustMe, Term::TrustMe)
                | (Term::BottomType, Term::BottomType)
                | (Term::UnitType, Term::UnitType)
                | (Term::UnitIntro, Term::UnitIntro)
                | (Term::BoolType, Term::BoolType) => true,
                (Term::Variable(x), Term::Variable(y)) => ctx.check(x, y),
                (Term::Lam(ax, ay), Term::Lam(bx, by)) => {
                    let _guard = if let (Some(ax), Some(bx)) = (ax, bx) {
                        Some(ctx.unify(ax.clone(), bx.clone()))
                    } else {
                        None
                    };
                    alpha_equal_impl(ay, by, ctx)
                }
                (Term::App(ax, ay), Term::App(bx, by))
                | (Term::Pi(ax, ay), Term::Pi(bx, by))
                | (Term::UnitElim(ax, ay), Term::UnitElim(bx, by))
                | (Term::SigmaType(ax, ay), Term::SigmaType(bx, by))
                | (Term::SigmaIntro(ax, ay), Term::SigmaIntro(bx, by)) => {
                    alpha_equal_impl(ax, bx, ctx) && alpha_equal_impl(ay, by, ctx)
                }
                (Term::Ann(ax, _), Term::Ann(bx, _)) => alpha_equal_impl(ax, bx, ctx),
                (Term::Let(ax, ay, az), Term::Let(bx, by, bz)) => {
                    let _guard = if let (Some(ax), Some(bx)) = (ax, bx) {
                        Some(ctx.unify(ax.clone(), bx.clone()))
                    } else {
                        None
                    };
                    alpha_equal_impl(ay, by, ctx) && alpha_equal_impl(az, bz, ctx)
                }
                (Term::BottomElim(ax), Term::BottomElim(bx)) => alpha_equal_impl(ax, bx, ctx),
                (Term::BoolIntro(ax), Term::BoolIntro(bx)) => ax == bx,
                (Term::BoolElim(ax, ay, az), Term::BoolElim(bx, by, bz)) => {
                    alpha_equal_impl(ax, bx, ctx)
                        && alpha_equal_impl(ay, by, ctx)
                        && alpha_equal_impl(az, bz, ctx)
                }
                (Term::SigmaElim(a0, a1, a2, a3), Term::SigmaElim(b0, b1, b2, b3)) => {
                    alpha_equal_impl(a0, b0, ctx) && {
                        let _guard1 = if let (Some(ax), Some(bx)) = (a1, b1) {
                            Some(ctx.unify(ax.clone(), bx.clone()))
                        } else {
                            None
                        };
                        let _guard2 = if let (Some(ax), Some(bx)) = (a2, b2) {
                            Some(ctx.unify(ax.clone(), bx.clone()))
                        } else {
                            None
                        };
                        alpha_equal_impl(a3, b3, ctx)
                    }
                }
                _ => false,
            }
        }
        let ctx = UnificationContext(UnsafeCell::new(HashMap::new()));
        alpha_equal_impl(self, other, &ctx)
    }
    fn whnf(ctx: &EvaluationContext, tree: RcPtr<Self>) -> RcPtr<Self> {
        match tree.data.as_ref() {
            Term::Type => tree,
            Term::Variable(_) => tree, // TODO: fix this
            Term::Lam(_, _) => tree,
            Term::App(x, y) => {
                let nf = Term::whnf(ctx, x.clone());
                match nf.data.as_ref() {
                    Term::Lam(name, body) => {
                        let body = match name {
                            None => body.clone(),
                            Some(name) => Term::instantiate(
                                body.clone(),
                                [(name.clone(), y.clone())].into_iter(),
                            ),
                        };
                        Term::whnf(ctx, body)
                    }
                    _ if Rc::ptr_eq(&x.data, &nf.data) => tree,
                    _ => RcPtr::new(tree.location, Term::App(nf, y.clone())),
                }
            }
            Term::Pi(_, _) => tree,
            Term::Ann(x, _) => x.clone(),
            Term::Let(x, y, z) => match x {
                Some(name) => {
                    let body =
                        Term::instantiate(z.clone(), [(name.clone(), y.clone())].into_iter());
                    Term::whnf(ctx, body)
                }
                None => Term::whnf(ctx, z.clone()),
            },
            Term::TrustMe => tree,
            Term::BottomType => tree,
            Term::BottomElim(_) => tree,
            Term::UnitType => tree,
            Term::UnitIntro => tree,
            Term::UnitElim(x, y) => {
                let nf = Term::whnf(ctx, x.clone());
                match nf.data.as_ref() {
                    Term::UnitIntro => Term::whnf(ctx, y.clone()),
                    _ if Rc::ptr_eq(&nf.data, &x.data) => tree,
                    _ => RcPtr::new(tree.location, Term::UnitElim(nf, y.clone())),
                }
            }
            Term::BoolType => tree,
            Term::BoolIntro(_) => tree,
            Term::BoolElim(x, y, z) => {
                let nf = Term::whnf(ctx, x.clone());
                match nf.data.as_ref() {
                    Term::BoolIntro(true) => Term::whnf(ctx, y.clone()),
                    Term::BoolIntro(false) => Term::whnf(ctx, z.clone()),
                    _ if Rc::ptr_eq(&nf.data, &x.data) => tree,
                    _ => RcPtr::new(tree.location, Term::BoolElim(nf, y.clone(), z.clone())),
                }
            }
            Term::SigmaType(_, _) => tree,
            Term::SigmaIntro(_, _) => tree,
            Term::SigmaElim(x, a, b, y) => {
                let nf = Term::whnf(ctx, x.clone());
                match nf.data.as_ref() {
                    Term::SigmaIntro(av, bv) => {
                        let mut vars = Vec::new();
                        if let Some(name) = a {
                            vars.push((name.clone(), av.clone()));
                        }
                        if let Some(name) = b {
                            vars.push((name.clone(), bv.clone()));
                        }
                        let y = Term::instantiate(y.clone(), vars.into_iter());
                        Term::whnf(ctx, y)
                    }
                    _ if Rc::ptr_eq(&nf.data, &x.data) => tree,
                    _ => RcPtr::new(
                        tree.location,
                        Term::SigmaElim(nf, a.clone(), b.clone(), y.clone()),
                    ),
                }
            }
        }
    }
    fn instantiate<I>(tree: RcPtr<Self>, iter: I) -> RcPtr<Self>
    where
        I: Iterator<Item = (Name, RcPtr<Self>)>,
    {
        let map = HashMap::from_iter(iter);
        fn instantiate_with_map(
            tree: RcPtr<Term>,
            map: &HashMap<Name, RcPtr<Term>>,
        ) -> RcPtr<Term> {
            match tree.data.as_ref() {
                Term::Type => tree,
                Term::Variable(a) => {
                    if let Some(tree) = map.get(a).cloned() {
                        tree
                    } else {
                        tree
                    }
                }
                Term::Lam(x, a) => {
                    let new_a = instantiate_with_map(a.clone(), map);
                    if Rc::ptr_eq(&a.data, &new_a.data) {
                        tree
                    } else {
                        RcPtr::new(tree.location, Term::Lam(x.clone(), new_a))
                    }
                }
                Term::App(a, b) => {
                    let new_a = instantiate_with_map(a.clone(), map);
                    let new_b = instantiate_with_map(b.clone(), map);
                    if Rc::ptr_eq(&a.data, &new_a.data) && Rc::ptr_eq(&b.data, &new_b.data) {
                        tree
                    } else {
                        RcPtr::new(tree.location, Term::App(new_a, new_b))
                    }
                }
                Term::Pi(a, b) => {
                    let new_a = instantiate_with_map(a.clone(), map);
                    let new_b = instantiate_with_map(b.clone(), map);
                    if Rc::ptr_eq(&a.data, &new_a.data) && Rc::ptr_eq(&b.data, &new_b.data) {
                        tree
                    } else {
                        RcPtr::new(tree.location, Term::Pi(new_a, new_b))
                    }
                }
                Term::Ann(a, b) => {
                    let new_a = instantiate_with_map(a.clone(), map);
                    let new_b = instantiate_with_map(b.clone(), map);
                    if Rc::ptr_eq(&a.data, &new_a.data) && Rc::ptr_eq(&b.data, &new_b.data) {
                        tree
                    } else {
                        RcPtr::new(tree.location, Term::Ann(new_a, new_b))
                    }
                }
                Term::Let(x, a, b) => {
                    let new_a = instantiate_with_map(a.clone(), map);
                    let new_b = instantiate_with_map(b.clone(), map);
                    if Rc::ptr_eq(&a.data, &new_a.data) && Rc::ptr_eq(&b.data, &new_b.data) {
                        tree
                    } else {
                        RcPtr::new(tree.location, Term::Let(x.clone(), new_a, new_b))
                    }
                }
                Term::TrustMe => tree,
                Term::BottomType => tree,
                Term::BottomElim(a) => {
                    let new_a = instantiate_with_map(a.clone(), map);
                    if Rc::ptr_eq(&a.data, &new_a.data) {
                        tree
                    } else {
                        RcPtr::new(tree.location, Term::BottomElim(new_a))
                    }
                }
                Term::UnitType => tree,
                Term::UnitIntro => tree,
                Term::UnitElim(a, b) => {
                    let new_a = instantiate_with_map(a.clone(), map);
                    let new_b = instantiate_with_map(b.clone(), map);
                    if Rc::ptr_eq(&a.data, &new_a.data) && Rc::ptr_eq(&b.data, &new_b.data) {
                        tree
                    } else {
                        RcPtr::new(tree.location, Term::UnitElim(new_a, new_b))
                    }
                }
                Term::BoolType => tree,
                Term::BoolIntro(_) => tree,
                Term::BoolElim(a, b, c) => {
                    let new_a = instantiate_with_map(a.clone(), map);
                    let new_b = instantiate_with_map(b.clone(), map);
                    let new_c = instantiate_with_map(c.clone(), map);
                    if Rc::ptr_eq(&a.data, &new_a.data)
                        && Rc::ptr_eq(&b.data, &new_b.data)
                        && Rc::ptr_eq(&c.data, &new_c.data)
                    {
                        tree
                    } else {
                        RcPtr::new(tree.location, Term::BoolElim(new_a, new_b, new_c))
                    }
                }
                Term::SigmaType(a, b) => {
                    let new_a = instantiate_with_map(a.clone(), map);
                    let new_b = instantiate_with_map(b.clone(), map);
                    if Rc::ptr_eq(&a.data, &new_a.data) && Rc::ptr_eq(&b.data, &new_b.data) {
                        tree
                    } else {
                        RcPtr::new(tree.location, Term::SigmaType(new_a, new_b))
                    }
                }
                Term::SigmaIntro(a, b) => {
                    let new_a = instantiate_with_map(a.clone(), map);
                    let new_b = instantiate_with_map(b.clone(), map);
                    if Rc::ptr_eq(&a.data, &new_a.data) && Rc::ptr_eq(&b.data, &new_b.data) {
                        tree
                    } else {
                        RcPtr::new(tree.location, Term::SigmaIntro(new_a, new_b))
                    }
                }
                Term::SigmaElim(a, x, y, b) => {
                    let new_a = instantiate_with_map(a.clone(), map);
                    let new_b = instantiate_with_map(b.clone(), map);
                    if Rc::ptr_eq(&a.data, &new_a.data) && Rc::ptr_eq(&b.data, &new_b.data) {
                        tree
                    } else {
                        RcPtr::new(
                            tree.location,
                            Term::SigmaElim(new_a, x.clone(), y.clone(), new_b),
                        )
                    }
                }
            }
        }
        instantiate_with_map(tree, &map)
    }
}

struct Record<'src, 'tree>(
    Option<&'tree Ptr<ParseTree<'src>>>,
    Option<&'tree Ptr<ParseTree<'src>>>,
);

fn scan_module_definitions<'tree, 'src: 'tree>(
    ctx: &SyntaxContext<'src>,
    defs: &'tree [Ptr<ParseTree<'src>>],
) -> Option<HashMap<&'src str, Record<'src, 'tree>>> {
    let mut map = Some(HashMap::new());
    for i in defs {
        match i.data.as_ref() {
            ParseTree::Import(_) => {
                ctx.warning(i.location.start, |builer| {
                    builer
                        .with_message("unsupported feature")
                        .with_label(
                            Label::new((ctx.source_name, i.location.clone()))
                                .with_color(Color::Yellow)
                                .with_message("import is not supported and will be ignored"),
                        )
                        .finish()
                });
            }
            ParseTree::TypeDecl { .. } => {
                ctx.warning(i.location.start, |builder| {
                    builder
                        .with_message("unsupported feature")
                        .with_label(
                            Label::new((ctx.source_name, i.location.clone()))
                                .with_color(Color::Yellow)
                                .with_message(
                                    "custom data type is not supported and will be ignored",
                                ),
                        )
                        .finish()
                });
            }
            ParseTree::FuncDecl { name, r#type } => {
                let name = name.get_literal();
                map = map.and_then(|mut map| {
                    let mut success = true;
                    match map.entry(name) {
                        Entry::Occupied(record) => {
                            let record: &mut Record = record.into_mut();
                            if record.0.is_some() {
                                ctx.error(i.location.start, |builder| {
                                    builder
                                        .with_message("Multiple declarations")
                                        .with_label(
                                            Label::new((ctx.source_name, i.location.clone()))
                                                .with_color(Color::Red)
                                                .with_message(format!(
                                                    "declaration of symbol {} is already provided",
                                                    name
                                                )),
                                        )
                                        .finish()
                                });
                                success = false;
                            } else {
                                record.0 = Some(r#type);
                            }
                        }
                        Entry::Vacant(position) => {
                            position.insert(Record(Some(r#type), None));
                        }
                    }
                    if success {
                        Some(map)
                    } else {
                        None
                    }
                })
            }
            ParseTree::FuncDefine { name, .. } => {
                let name = name.get_literal();
                map = map.and_then(|mut map| {
                    let mut success = true;
                    match map.entry(name) {
                        Entry::Occupied(record) => {
                            let record: &mut Record = record.into_mut();
                            if record.1.is_some() {
                                ctx.error(i.location.start, |builder| {
                                    builder
                                        .with_message("Multiple definitions")
                                        .with_label(
                                            Label::new((ctx.source_name, i.location.clone()))
                                                .with_color(Color::Red)
                                                .with_message(format!(
                                                    "Definition of symbol {} is already provided",
                                                    name
                                                )),
                                        )
                                        .finish()
                                });
                                success = false;
                            } else {
                                record.1 = Some(i);
                            }
                        }
                        Entry::Vacant(position) => {
                            position.insert(Record(None, Some(i)));
                        }
                    }
                    if success {
                        Some(map)
                    } else {
                        None
                    }
                })
            }
            _ => assert_unreachable!(),
        }
    }
    map.and_then(|map| {
        let mut success = true;
        for (name, record) in map.iter() {
            if record.0.is_none() {
                let provided = unsafe { record.1.as_ref().unwrap_unchecked() };
                ctx.error(provided.location.start, |builder| {
                    builder
                        .with_message("Incomplete term")
                        .with_label(
                            Label::new((ctx.source_name, provided.location.clone()))
                                .with_color(Color::Red)
                                .with_message(format!("Symbol {} does not have declaration", name)),
                        )
                        .finish()
                });
                success = false;
            }
            if record.1.is_none() {
                let provided = unsafe { record.0.as_ref().unwrap_unchecked() };
                ctx.error(provided.location.start, |builder| {
                    builder
                        .with_message("Incomplete term")
                        .with_label(
                            Label::new((ctx.source_name, provided.location.clone()))
                                .with_color(Color::Red)
                                .with_message(format!("Symbol {} does not have definition", name)),
                        )
                        .finish()
                });
                success = false
            }
        }
        if success {
            Some(map)
        } else {
            None
        }
    })
}
#[cfg(test)]
mod test {
    use super::{Definition, RcPtr, Term};

    fn get_definitions(source: &str) -> Vec<Definition> {
        let parse = grammar::syntactic::parse(source);
        let parse_errs = parse.1;
        for i in parse_errs {
            println!("{:?}", i);
        }
        let parse_tree = parse.0.unwrap();
        let definitions = Definition::new_from_module("source.txt", &parse_tree);
        for i in definitions.1.iter() {
            i.eprint(("source.txt", ariadne::Source::from(source)))
                .unwrap();
        }
        definitions.0
    }
    fn parse_from_source(source: &str, num: usize) {
        let definitions = get_definitions(source);
        {
            assert_eq!(definitions.len(), num);
            for i in definitions {
                println!("{} = {}", i.name.0, i.term)
            }
        }
    }

    macro_rules! test_source_parsing {
        ($name:ident, $src:literal) => {
            test_source_parsing!($name, 1, $src);
        };
        ($name:ident, $num:expr, $src:literal) => {
            #[test]
            fn $name() {
                parse_from_source($src, $num);
            }
        };
    }

    #[test]
    fn test_instantiate() {
        let source = r#"
        module Test
        test : Bool -> (`Sigma Bool, Bool)
        test x = case x of {
            True -> let u = x in (@Pair u x);
            False -> (@Pair x x);
        } 
        "#;
        let definitions = get_definitions(source);
        let tree = definitions.first().unwrap().term.clone();
        match tree.data.as_ref() {
            Term::Ann(x, _) => match x.data.as_ref() {
                Term::Lam(name, body) => {
                    let target = RcPtr::new(0..0, Term::BoolIntro(true));
                    let result = Term::instantiate(
                        body.clone(),
                        [(name.clone().unwrap(), target)].into_iter(),
                    );
                    assert_eq!(format!("{}", result), "(𝟚-elim True (let u = True in (((λ fresh_0 . (λ fresh_1 . (fresh_0 , fresh_1))) u) True)) (((λ fresh_2 . (λ fresh_3 . (fresh_2 , fresh_3))) True) True))")
                }
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_whnf() {
        let source = r#"
        module Test
        test : Bool -> (`Sigma Bool, Bool)
        test x = case x of {
            True -> let u = x in (@Pair u x);
            False -> (@Pair x x);
        } 
        "#;
        let definitions = get_definitions(source);
        let tree = definitions.first().unwrap().term.clone();
        match tree.data.as_ref() {
            Term::Ann(x, _) => match x.data.as_ref() {
                Term::Lam(name, body) => {
                    let target = RcPtr::new(0..0, Term::BoolIntro(true));
                    let result = Term::instantiate(
                        body.clone(),
                        [(name.clone().unwrap(), target)].into_iter(),
                    );
                    assert_eq!(
                        "(True , True)",
                        format!("{}", Term::whnf(&super::EvaluationContext {}, result))
                    )
                }
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }

    test_source_parsing! {
        test_warning, 0,
        r#"
    module Test
    import A
    import B
    data List (a : Type) = {
        Nil : (List a);
        Cons : a -> (List a) -> (List a);
    }"#}

    test_source_parsing!(
        test_func_def,
        2,
        r#"
    module Test

    myType : Type
    myType = Bool

    test : myType -> myType -> `Sigma myType, myType
    test x = let u = lambda y . (@Pair x y) in u"#
    );

    test_source_parsing!(
        test_match_unit,
        r#"
    module Test
    test : Unit -> Bool
    test x = case x of {
        Unit -> !!;
    }"#
    );

    test_source_parsing!(
        test_match_bottom,
        r#"
    module Test
    test : Bottom -> Bool
    test x = case x of {}
    "#
    );

    test_source_parsing!(
        test_match_pair,
        r#"
    module Test
    test : (`Sigma Bool, Bool) -> Bool
    test x = case x of {
        Pair l _ -> l;
    }
    "#
    );

    test_source_parsing!(
        test_match_bool,
        r#"
    module Test
    test : Bool -> Type
    test x = case x of {
        True -> Unit;
        False -> Bottom;
    }
    "#
    );

    test_source_parsing!(
        test_type_level,
        r#"
    module Test
    test : (Type -> Bool -> Type) -> Bool -> Type
    test check x = case x of {
        True -> `Pi (i : Bool), let u : Type ~= (check u i) in u;
        False -> `Sigma (i : Bool), (check Bool i);
    }
    "#
    );
}
