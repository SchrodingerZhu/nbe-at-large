use crate::assert_unreachable;
use crate::builtin::{BuiltinBool, BuiltinBottom, BuiltinPair, BuiltinType, BuiltinUnit};
use ariadne::{Color, Label, Report, ReportBuilder};
use grammar::syntactic::{ParseTree, Ptr};
use std::cell::{Cell, UnsafeCell};
use std::collections::hash_map::Entry;
use std::hash::{Hash, Hasher};
use std::ops::Range;
use std::{collections::HashMap, rc::Rc};
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

type NamedSpan<'a> = (&'a str, Range<usize>);

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
    name: Name,
    term: RcPtr<Term>,
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
        Nil : (List a);
        Cons : a -> (List a) -> (List a);
    }
"#;
    let parse_tree = grammar::syntactic::parse(source).0.unwrap();
    let (_, reports) = Definition::new_from_module("source.txt", &parse_tree);
    for i in reports.iter() {
        i.eprint(("source.txt", ariadne::Source::from(source)))
            .unwrap();
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
    use super::Definition;
    fn parse_from_source(source: &str) {
        let parse_tree = grammar::syntactic::parse(source).1;
        eprintln!("{:#?}", parse_tree);
        let parse_tree = grammar::syntactic::parse(source).0.unwrap();
        let definitions = Definition::new_from_module("source.txt", &parse_tree);
        for i in definitions.1.iter() {
            i.eprint(("source.txt", ariadne::Source::from(source)))
                .unwrap();
        }
        {
            println!("{:#?}", definitions.0)
        }
    }

    #[test]
    fn test_func_def() {
        let source = r#"
    module Test

    myType : Type
    myType = Bool

    test : myType -> myType -> `Sigma myType, myType
    test x = let u = lambda y . (@Pair x y) in u
"#;
        parse_from_source(source);
    }

    #[test]
    fn test_match_unit() {
        let source = r#"
    module Test
    test : Unit -> Bool
    test x = case x of {
        Unit -> !!;
    } 
"#;
        parse_from_source(source);
    }

    #[test]
    fn test_match_bottom() {
        let source = r#"
    module Test
    test : Bottom -> Bool
    test x = case x of {} 
"#;
        parse_from_source(source);
    }

    #[test]
    fn test_match_pair() {
        let source = r#"
    module Test
    test : `Sigma Bool, Bool -> Bool
    test x = case x of {
        Pair l _ -> l;
    } 
"#;
        parse_from_source(source);
    }

    #[test]
    fn test_match_bool() {
        let source = r#"
    module Test
    test : Bool -> Type
    test x = case x of {
        True -> Bool;
        False -> Unit;
    } 
"#;
        parse_from_source(source);
    }

    #[test]
    fn test_type_level() {
        let source = r#"
    module Test
    test : (Type -> Bool -> Type) -> Bool -> Type
    test check x = case x of {
        True -> `Pi (i : Bool), let u : Type ~= (check u i) in u;
        False -> `Sigma (i : Bool), (check !! i);
    } 
"#;
        parse_from_source(source);
    }
}
