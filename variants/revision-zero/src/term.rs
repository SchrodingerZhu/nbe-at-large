use ariadne::{Color, Label, Report, ReportBuilder};
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

type NamedSpan<'a> = (&'a str, std::ops::Range<usize>);

#[derive(Debug)]
// RcPtr because we may want to substitute
pub enum Term {
    Type,
    Variable(Name),
    Lam(Option<Name>, RcPtr<Self>),
    App(RcPtr<Self>, RcPtr<Self>),
    Pi(RcPtr<Self>, Option<Name>, RcPtr<Self>),
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
    SigmaType(RcPtr<Self>, Option<Name>, RcPtr<Self>),
    SigmaIntro(RcPtr<Self>, RcPtr<Self>),
    SigmaElim(RcPtr<Self>, Option<Name>, Option<Name>, RcPtr<Self>),
}

pub enum Definition {
    FuncDecl(Name, Term),
    FuncDefine(Name, Term),
}

impl Definition {
    fn new_from_definition<'a>(
        ctx: &SyntaxContext<'a>,
        tree: &Ptr<ParseTree<'_>>,
    ) -> Option<RcPtr<Self>> {
        match tree.data.as_ref() {
            ParseTree::Import(_) => {
                ctx.warning(tree.location.start, |builer| {
                    builer
                        .with_message("unsupported feature")
                        .with_label(
                            Label::new((ctx.source_name, tree.location.clone()))
                                .with_color(Color::Yellow)
                                .with_message("import is not supported and will be ignored"),
                        )
                        .finish()
                });
                None
            }
            ParseTree::TypeDecl { .. } => {
                ctx.warning(tree.location.start, |builder| {
                    builder
                        .with_message("unsupported feature")
                        .with_label(
                            Label::new((ctx.source_name, tree.location.clone()))
                                .with_color(Color::Yellow)
                                .with_message(
                                    "custom data type is not supported and will be ignored",
                                ),
                        )
                        .finish()
                });
                None
            }
            ParseTree::FuncDecl { .. } => {
                todo!()
            }
            ParseTree::FuncDefine { .. } => {
                todo!()
            }
            _ => assert_unreachable!(),
        }
    }

    fn new_from_module<'a>(
        source_name: &'a str,
        source: &'a str,
        tree: &Ptr<ParseTree<'_>>,
    ) -> (Vec<RcPtr<Self>>, Vec<Report<NamedSpan<'a>>>) {
        match tree.data.as_ref() {
            ParseTree::Module { definitions, .. } => {
                let mut translated = Vec::new();
                let mut ctx = SyntaxContext::new(source_name, source);
                for i in definitions {
                    if let Some(x) = Self::new_from_definition(&mut ctx, i) {
                        translated.push(x);
                    }
                }
                (translated, ctx.take_reports())
            }
            _ => assert_unreachable!(),
        }
    }
}

struct SyntaxContext<'a> {
    source_name: &'a str,
    source: &'a str,
    variables: UnsafeCell<HashMap<&'a str, Name>>,
    fresh_counter: Cell<usize>,
    reports: UnsafeCell<Vec<Report<NamedSpan<'a>>>>,
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
            reports: UnsafeCell::new(Vec::new()),
        }
    }
    fn add_report(&self, report: Report<NamedSpan<'a>>) {
        unsafe { (*self.reports.get()).push(report) }
    }
    fn reports(&self) -> &[Report<NamedSpan<'a>>] {
        unsafe { (*self.reports.get()).as_slice() }
    }
    fn take_reports(self) -> Vec<Report<NamedSpan<'a>>> {
        unsafe { self.reports.into_inner() }
    }
    fn error<F>(&self, offset: usize, f: F)
    where
        F: FnOnce(ReportBuilder<NamedSpan<'a>>) -> Report<NamedSpan<'a>>,
    {
        self.add_report(f(Report::build(
            ariadne::ReportKind::Error,
            self.source_name,
            offset,
        )))
    }
    fn warning<F>(&self, offset: usize, f: F)
    where
        F: FnOnce(ReportBuilder<NamedSpan<'a>>) -> Report<NamedSpan<'a>>,
    {
        self.add_report(f(Report::build(
            ariadne::ReportKind::Warning,
            self.source_name,
            offset,
        )))
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

trait BuiltinType {
    type ElimRules;
    fn new_from_pattern_rules<'src>(
        ctx: &SyntaxContext<'src>,
        rules: &[Ptr<ParseTree<'src>>],
    ) -> Result<Option<Self::ElimRules>, ()>;
}

struct BuiltinUnit;
struct BuiltinPair;
struct BuiltinBool;
struct BuiltinBottom;

impl BuiltinType for BuiltinUnit {
    type ElimRules = RcPtr<Term>;

    fn new_from_pattern_rules<'src>(
        ctx: &SyntaxContext<'src>,
        rules: &[Ptr<ParseTree<'src>>],
    ) -> Result<Option<Self::ElimRules>, ()> {
        if rules.len() != 1 {
            return Ok(None);
        }
        match rules.first() {
            Some(Ptr {
                location,
                data:
                    box ParseTree::PatternRule {
                        constructor,
                        variables,
                        body,
                    },
            }) => match constructor.get_literal() {
                "Unit" if variables.is_empty() => match Term::new_from_expr(ctx, body) {
                    None => Err(()),
                    Some(tree) => Ok(Some(tree)),
                },
                "Unit" => Err(ctx.error(location.start, |builder| {
                    builder
                        .with_message("Illegal elimination for Unit type")
                        .with_label(
                            Label::new((ctx.source_name, variables[0].location.clone()))
                                .with_color(Color::Red)
                                .with_message("unexpected variable(s)"),
                        )
                        .finish()
                })),
                _ => Ok(None),
            },
            _ => assert_unreachable!(),
        }
    }
}

impl BuiltinType for BuiltinPair {
    type ElimRules = (Option<Name>, Option<Name>, RcPtr<Term>);

    fn new_from_pattern_rules<'src>(
        ctx: &SyntaxContext<'src>,
        rules: &[Ptr<ParseTree<'src>>],
    ) -> Result<Option<Self::ElimRules>, ()> {
        if rules.len() != 1 {
            return Ok(None);
        }
        match rules.first() {
            Some(Ptr {
                location,
                data:
                    box ParseTree::PatternRule {
                        constructor,
                        variables,
                        body,
                    },
            }) => match constructor.get_literal() {
                "Pair" if variables.len() == 2 => {
                    let (left, _left_guard) = Term::new_from_parameter(ctx, &variables[0])
                        .map(|name| ctx.push_variable(name))
                        .map(|(x, y)| (Some(x), Some(y)))
                        .unwrap_or((None, None));
                    let (right, _right_guard) = Term::new_from_parameter(ctx, &variables[1])
                        .map(|name| ctx.push_variable(name))
                        .map(|(x, y)| (Some(x), Some(y)))
                        .unwrap_or((None, None));
                    match Term::new_from_expr(ctx, body) {
                        None => Err(()),
                        Some(body) => Ok(Some((left, right, body))),
                    }
                }
                "Pair" => Err(ctx.error(location.start, |builder| {
                    builder
                        .with_message("Illegal elimination for Sigma type")
                        .with_label(
                            Label::new((ctx.source_name, location.clone()))
                                .with_color(Color::Red)
                                .with_message(
                                    "the number parameter is not unmatched for Pair constructor",
                                ),
                        )
                        .finish()
                })),
                _ => Ok(None),
            },
            _ => assert_unreachable!(),
        }
    }
}

impl BuiltinType for BuiltinBottom {
    type ElimRules = ();

    fn new_from_pattern_rules<'src>(
        _: &SyntaxContext<'src>,
        rules: &[Ptr<ParseTree<'src>>],
    ) -> Result<Option<Self::ElimRules>, ()> {
        if rules.is_empty() {
            Ok(Some(()))
        } else {
            Ok(None)
        }
    }
}

impl BuiltinType for BuiltinBool {
    type ElimRules = (RcPtr<Term>, RcPtr<Term>);

    fn new_from_pattern_rules<'src>(
        ctx: &SyntaxContext<'src>,
        rules: &[Ptr<ParseTree<'src>>],
    ) -> Result<Option<Self::ElimRules>, ()> {
        if rules.len() != 2 {
            return Ok(None);
        }
        todo!()
    }
}

impl Term {
    fn new_from_type<'a>(
        ctx: &SyntaxContext<'a>,
        tree: &Ptr<ParseTree<'a>>,
    ) -> Option<RcPtr<Self>> {
        todo!()
    }

    fn new_from_parameter<'a>(
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

    fn new_from_expr<'a>(
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
                                        "custom construct {} is not supported",
                                        lit
                                    )),
                            )
                            .finish()
                    });
                    None
                }
            },
            ParseTree::Let { var, binding, body } => {
                let mut binding = Term::new_from_expr(ctx, binding);
                match var.data.as_ref() {
                    ParseTree::AnnotableVariable { name, annotation } => {
                        let (name, _guard) = name
                            .as_ref()
                            .map(|name| ctx.push_variable(name.get_literal()))
                            .map(|(x, y)| (Some(x), Some(y)))
                            .unwrap_or((None, None));
                        let body = Term::new_from_expr(ctx, body);
                        if let Some(ann) = annotation {
                            let ann = Term::new_from_type(ctx, ann);
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
            _ => assert_unreachable!(),
        }
    }

    fn new_from_params_and_body<'a>(
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

    fn new_from_function_definition<'a>(
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

    fn new_from_variable<'a>(
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
    let (_, reports) = Definition::new_from_module("source.txt", source, &parse_tree);
    for i in reports.iter() {
        i.eprint(("source.txt", ariadne::Source::from(source)))
            .unwrap();
    }
}

#[test]
fn test_func_def() {
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
        for i in ctx.reports().iter() {
            i.eprint(("source.txt", ariadne::Source::from(source)))
                .unwrap();
        }
        println!("{:?}", func_def.unwrap())
    }
}

#[test]
fn test_match_unit() {
    let source = r#"
    module Test
    test x = case x of {
        Unit -> !!;
    } 
"#;
    let parse_tree = grammar::syntactic::parse(source).1;
    eprintln!("{:#?}", parse_tree);
    let parse_tree = grammar::syntactic::parse(source).0.unwrap();
    let ctx = SyntaxContext::new("source.txt", source);
    if let ParseTree::Module { definitions, .. } = parse_tree.data.as_ref() {
        let func_def = Term::new_from_function_definition(&ctx, &definitions[0]);
        for i in ctx.reports().iter() {
            i.eprint(("source.txt", ariadne::Source::from(source)))
                .unwrap();
        }
        println!("{:?}", func_def.unwrap())
    }
}

#[test]
fn test_match_bottom() {
    let source = r#"
    module Test
    test x = case x of {} 
"#;
    let parse_tree = grammar::syntactic::parse(source).1;
    eprintln!("{:#?}", parse_tree);
    let parse_tree = grammar::syntactic::parse(source).0.unwrap();
    let ctx = SyntaxContext::new("source.txt", source);
    if let ParseTree::Module { definitions, .. } = parse_tree.data.as_ref() {
        let func_def = Term::new_from_function_definition(&ctx, &definitions[0]);
        for i in ctx.reports().iter() {
            i.eprint(("source.txt", ariadne::Source::from(source)))
                .unwrap();
        }
        println!("{:?}", func_def.unwrap())
    }
}

#[test]
fn test_match_pair() {
    let source = r#"
    module Test
    test x = case x of {
        Pair l _ -> l;
    } 
"#;
    let parse_tree = grammar::syntactic::parse(source).1;
    eprintln!("{:#?}", parse_tree);
    let parse_tree = grammar::syntactic::parse(source).0.unwrap();
    let ctx = SyntaxContext::new("source.txt", source);
    if let ParseTree::Module { definitions, .. } = parse_tree.data.as_ref() {
        let func_def = Term::new_from_function_definition(&ctx, &definitions[0]);
        for i in ctx.reports().iter() {
            i.eprint(("source.txt", ariadne::Source::from(source)))
                .unwrap();
        }
        println!("{:?}", func_def.unwrap())
    }
}
