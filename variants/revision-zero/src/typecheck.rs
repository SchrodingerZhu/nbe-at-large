use crate::equalization::Equalization;
use crate::instantiation::Instantiation;
use crate::term::{Definition, Name, RcPtr, Term};
use crate::whnf::WeakHeadNF;
use ariadne::{Color, Label, Report, ReportBuilder, Span};
use std::cell::{Cell, UnsafeCell};
use std::collections::HashMap;
use std::ops::Range;

#[allow(clippy::needless_lifetimes)]
trait BidirectionalTypeCheck: Sized + WeakHeadNF {
    fn check_term<'a>(
        term: Self::Wrapper<Self>,
        target: Option<Self::Wrapper<Self>>,
        ctx: &Self::Context<'a>,
    ) -> Option<Self::Wrapper<Self>>;

    fn infer_type<'a>(
        term: Self::Wrapper<Self>,
        ctx: &Self::Context<'a>,
    ) -> Option<Self::Wrapper<Self>> {
        Self::check_term(Self::whnf(ctx, term), None, ctx)
    }

    fn check_type<'a>(
        term: Self::Wrapper<Self>,
        target: Self::Wrapper<Self>,
        ctx: &Self::Context<'a>,
    ) -> bool {
        let nf = Self::whnf(ctx, target);
        Self::check_term(term, Some(nf), ctx).is_some()
    }
}

type NamedSpan<'a> = (&'a str, Range<usize>);

pub struct TypeCheckContext<'a> {
    source_name: &'a str,
    global_defs: HashMap<Name, Definition>,

    reports: UnsafeCell<Vec<Report<NamedSpan<'a>>>>,
    local_defs: UnsafeCell<HashMap<Name, RcPtr<Term>>>,
    local_types: UnsafeCell<HashMap<Name, RcPtr<Term>>>,
    fresh_counter: Cell<usize>,
}

enum ChangeLog {
    LocalDef(Name, Option<RcPtr<Term>>),
    LocalType(Name, Option<RcPtr<Term>>),
}
pub struct Guard<'src, 'ctx> {
    ctx: &'ctx TypeCheckContext<'src>,
    changelog: ChangeLog,
}

impl<'src, 'ctx> Drop for Guard<'src, 'ctx> {
    fn drop(&mut self) {
        let (name, delta, map) = match &mut self.changelog {
            ChangeLog::LocalDef(name, delta) => (name.clone(), delta, unsafe {
                &mut *self.ctx.local_defs.get()
            }),
            ChangeLog::LocalType(name, delta) => (name.clone(), delta, unsafe {
                &mut *self.ctx.local_types.get()
            }),
        };
        match delta.take() {
            Some(old) => {
                map.insert(name, old);
            }
            None => {
                map.remove(&name);
            }
        }
    }
}

impl<'a> TypeCheckContext<'a> {
    pub fn lookup_def(&self, name: &Name) -> Option<RcPtr<Term>> {
        unsafe {
            (*self.local_defs.get())
                .get(name)
                .cloned()
                .or_else(|| self.global_defs.get(name).map(|x| x.term.clone()))
        }
    }
    pub fn lookup_type(&self, name: &Name) -> Option<RcPtr<Term>> {
        unsafe {
            (*self.local_types.get())
                .get(name)
                .cloned()
                .or_else(|| self.global_defs.get(name).map(|x| x.signature.clone()))
        }
    }

    pub fn push_type<'b>(&'b self, name: Name, value: RcPtr<Term>) -> Guard<'a, 'b> {
        Guard {
            ctx: self,
            changelog: ChangeLog::LocalType(name.clone(), unsafe {
                (*self.local_types.get()).insert(name, value)
            }),
        }
    }

    pub fn push_def<'b>(&'b self, name: Name, value: RcPtr<Term>) -> Guard<'a, 'b> {
        Guard {
            ctx: self,
            changelog: ChangeLog::LocalDef(name.clone(), unsafe {
                (*self.local_defs.get()).insert(name, value)
            }),
        }
    }

    pub fn add_report(&self, report: Report<NamedSpan<'a>>) {
        unsafe { (*self.reports.get()).push(report) }
    }
    pub fn reports(&self) -> &[Report<NamedSpan<'a>>] {
        unsafe { (*self.reports.get()).as_slice() }
    }
    pub fn take_reports(self) -> Vec<Report<NamedSpan<'a>>> {
        self.reports.into_inner()
    }

    pub fn error<F>(&self, offset: usize, f: F)
    where
        F: FnOnce(ReportBuilder<NamedSpan<'a>>) -> Report<NamedSpan<'a>>,
    {
        self.add_report(f(Report::build(
            ariadne::ReportKind::Error,
            self.source_name,
            offset,
        )))
    }
    pub fn warning<F>(&self, offset: usize, f: F)
    where
        F: FnOnce(ReportBuilder<NamedSpan<'a>>) -> Report<NamedSpan<'a>>,
    {
        self.add_report(f(Report::build(
            ariadne::ReportKind::Warning,
            self.source_name,
            offset,
        )))
    }
    pub fn source_name(&self) -> &'a str {
        self.source_name
    }
}

impl Default for TypeCheckContext<'static> {
    fn default() -> Self {
        Self {
            source_name: "default-context",
            global_defs: Default::default(),
            reports: Default::default(),
            local_defs: Default::default(),
            local_types: Default::default(),
            fresh_counter: Cell::new(0),
        }
    }
}

impl<'src> TypeCheckContext<'src> {
    pub fn new<'def, I>(source_name: &'src str, definitions: I) -> Self
    where
        I: Iterator<Item = &'def Definition>,
    {
        Self {
            source_name,
            global_defs: { HashMap::from_iter(definitions.map(|x| (x.name.clone(), x.clone()))) },
            reports: Default::default(),
            local_defs: Default::default(),
            local_types: Default::default(),
            fresh_counter: Cell::new(0),
        }
    }
    pub(crate) fn fresh(&self) -> Name {
        let counter = self.fresh_counter.get();
        self.fresh_counter.replace(counter + 1);
        Name::new(format!("hole_{}", counter))
    }
}

fn ensure_type(term: RcPtr<Term>, ctx: &TypeCheckContext) -> bool {
    let target = RcPtr::new(term.location.clone(), Term::Type);
    Term::check_type(term, target, ctx)
}

fn ensure_pi(term: RcPtr<Term>, ctx: &TypeCheckContext) -> Option<(RcPtr<Term>, RcPtr<Term>)> {
    let location = term.location.clone();
    let term = Term::whnf(ctx, term);
    match term.data.as_ref() {
        Term::Pi(x, y) => Some((x.clone(), y.clone())),
        _ => {
            ctx.error(location.start, |builder| builder
                .with_message("Type error")
                .with_label(Label::new((ctx.source_name, location))
                    .with_message(format!("expect this expression to be of Pi type, but the normal form {} failed to conform the requirement", term))
                    .with_color(Color::Red))
                .finish());
            None
        }
    }
}

fn def<'src, 'ctx>(
    x: RcPtr<Term>,
    y: RcPtr<Term>,
    ctx: &'ctx TypeCheckContext<'src>,
) -> Option<Guard<'src, 'ctx>> {
    let nfx = Term::whnf(ctx, x);
    let nfy = Term::whnf(ctx, y);
    match (nfx.data.as_ref(), nfy.data.as_ref()) {
        (Term::Variable(_), Term::Variable(_)) => None,
        (Term::Variable(x), _) => Some(ctx.push_def(x.clone(), nfy)),
        (_, Term::Variable(y)) => Some(ctx.push_def(y.clone(), nfx)),
        _ => None,
    }
}
#[allow(clippy::needless_lifetimes)]
impl BidirectionalTypeCheck for Term {
    fn check_term<'a>(
        term: Self::Wrapper<Self>,
        target: Option<Self::Wrapper<Self>>,
        ctx: &Self::Context<'a>,
    ) -> Option<Self::Wrapper<Self>> {
        let debug_target = target.clone();
        let debug_term = term.clone();
        let result = match (
            term.data.as_ref(),
            target
                .as_ref()
                .map(|x| (x.location.clone(), x.data.as_ref())),
        ) {
            (Term::Variable(x), None) => {
                match ctx.lookup_type(x) {
                    Some(x) => Some(x),
                    None => {
                        ctx.error(term.location.start, |builder| builder
                            .with_message("Type error")
                            .with_label(Label::new((ctx.source_name, term.location.clone()))
                                .with_message(format!("cannot infer variable type {}", x.literal()))
                                .with_color(Color::Red))
                            .finish());
                        None
                    }
                }
            }
            (Term::Type, None) => return Some(term),
            (Term::Pi(a, bnd), None) | (Term::SigmaType(a, bnd), None) => {
                if ensure_type(a.clone(), ctx) {
                    let fresh = ctx.fresh();
                    let _guard = ctx.push_type(fresh.clone(), a.clone());
                    let var = RcPtr::new(a.location.clone(), Term::Variable(fresh));
                    let app = RcPtr::new(bnd.location.clone(), Term::App(bnd.clone(), var));
                    if ensure_type(app, ctx) {
                        Some(RcPtr::new(term.location.clone(), Term::Type))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            (Term::Lam(name, body), Some((_, Term::Pi(a, bnd)))) => {
                let name = name.clone().unwrap_or_else(|| ctx.fresh());
                let _guard = ctx.push_type(name.clone(), a.clone());
                let var = RcPtr::new(a.location.clone(), Term::Variable(name));
                let app = RcPtr::new(bnd.location.clone(), Term::App(bnd.clone(), var));
                if Term::check_type(body.clone(), app, ctx) {
                    target.clone()
                } else {
                    None
                }
            }

            (Term::SigmaIntro(x, y), None) => {
                Self::infer_type(x.clone(), ctx)
                    .and_then(|tx| Self::infer_type(y.clone(), ctx).map(|ty| (tx, ty)))
                    .map(|(tx, ty)|
                        RcPtr::new(term.location.clone(), Term::SigmaType(tx,
                            RcPtr::new(term.location.clone(), Term::Lam(None, ty))
                        ))
                    )
            }

            (Term::SigmaIntro(x, y), Some((_, Term::SigmaType(a, bnd)))) => {
                if Self::check_type(x.clone(), a.clone(), ctx) {
                    let app = RcPtr::new(bnd.location.clone(), Term::App(bnd.clone(), x.clone()));
                    if Self::check_type(y.clone(), app, ctx) {
                        target
                    } else {
                        None
                    }
                } else {
                    None
                }
            }

            (Term::Lam(_, _), Some((loc, nf))) | (Term::SigmaIntro(_, _), Some((loc, nf))) => {
                ctx.error(term.location.start, |builder| builder
                    .with_message("Type error")
                    .with_label(Label::new((ctx.source_name, term.location.clone()))
                        .with_message(format!("failed to type check this expression, which is interpreted as {}", term))
                        .with_color(Color::Red))
                    .with_label(Label::new((ctx.source_name, loc))
                        .with_message(format!("the type is provided from here, whose WHNF is given as {}", nf))
                        .with_color(Color::Red))
                    .finish());
                None
            }
            (Term::App(x, y), None) => {
                let nf = Term::whnf(ctx, x.clone());
                match nf.data.as_ref() {
                    _ => Self::infer_type(nf.clone(), ctx)
                        .and_then(| type_x | ensure_pi(type_x, ctx))
                        .and_then(| (a, bnd) | {
                                if Self::check_type(y.clone(), a, ctx) {
                                      let app = RcPtr::new(bnd.location.clone(), Term::App(bnd, y.clone()));
                                          Some(Term::whnf(ctx, app))
                                      } else {
                                          None
                                      }
                        }),
                }
            }
            (Term::Ann(x, y), None) => {
                if ensure_type(y.clone(), ctx) && Self::check_type(x.clone(), y.clone(), ctx) {
                    Some(y.clone())
                } else {
                    None
                }
            }
            (Term::TrustMe, Some(_)) => target,
            (Term::BottomType, None) => Some(RcPtr::new(term.location.clone(), Term::Type)),
            (Term::BottomElim(x), Some(_)) => {
                let bottom_type = RcPtr::new(x.location.clone(), Term::BottomType);
                if Self::check_type(x.clone(), bottom_type, ctx) {
                    target
                } else {
                    None
                }
            }
            (Term::UnitType, None) => Some(RcPtr::new(term.location.clone(), Term::Type)),
            (Term::UnitIntro, None) => Some(RcPtr::new(term.location.clone(), Term::UnitType)),
            (Term::UnitElim(x, y), None) => {
                let unit_type = RcPtr::new(x.location.clone(), Term::UnitType);
                if Self::check_type(x.clone(), unit_type, ctx) {
                    Self::infer_type(y.clone(), ctx)
                } else {
                    None
                }
            }
            (Term::UnitElim(x, y), Some(_)) => {
                let unit_type = RcPtr::new(x.location.clone(), Term::UnitType);
                if Self::check_type(x.clone(), unit_type, ctx)
                    && Self::check_type(
                        y.clone(),
                        unsafe { target.clone().unwrap_unchecked() },
                        ctx,
                    )
                {
                    target
                } else {
                    None
                }
            }
            (Term::BoolType, None) => Some(RcPtr::new(term.location.clone(), Term::Type)),
            (Term::BoolIntro(_), None) => Some(RcPtr::new(term.location.clone(), Term::BoolType)),
            (Term::BoolElim(x, y, z), None) => {
                let bool_type = RcPtr::new(x.location.clone(), Term::BoolType);
                if Self::check_type(x.clone(), bool_type, ctx) {
                    Self::infer_type(y.clone(), ctx).and_then(|type_y| {
                        if Self::check_type(z.clone(), type_y.clone(), ctx) {
                            Some(type_y)
                        } else {
                            None
                        }
                    })
                } else {
                    None
                }
            }
            (Term::BoolElim(x, y, z), Some(_)) => {
                let bool_type = RcPtr::new(x.location.clone(), Term::BoolType);
                if Self::check_type(x.clone(), bool_type, ctx) {
                    let branch_true = {
                        let target = unsafe { target.clone().unwrap_unchecked() };
                        move || {
                            let true_intro = RcPtr::new(x.location.clone(), Term::BoolIntro(true));
                            let _guard = def(x.clone(), true_intro, ctx);
                            Term::check_type(y.clone(), target, ctx)
                        }
                    };
                    let branch_false = {
                        let target = unsafe { target.clone().unwrap_unchecked() };
                        move || {
                            let false_intro =
                                RcPtr::new(x.location.clone(), Term::BoolIntro(false));
                            let _guard = def(x.clone(), false_intro, ctx);
                            Term::check_type(z.clone(), target, ctx)
                        }
                    };
                    if branch_true() && branch_false() {
                        target
                    } else {
                        None
                    }
                } else {
                    None
                }
            }

            (Term::Let(x, y, z), required) => Self::infer_type(y.clone(), ctx)
                .and_then(|type_y| {
                    let _g1 = x.as_ref().map(|x| ctx.push_type(x.clone(), type_y));
                    let _g2 = x.as_ref().map(|x| ctx.push_def(x.clone(), y.clone()));
                    Self::check_term(z.clone(), target.clone(), ctx)
                })
                .map(|result| match (required, x) {
                    (Some(_), _) | (_, None) => result,
                    (None, Some(x)) => Self::whnf(
                        ctx,
                        Term::instantiate(result, [(x.clone(), y.clone())].into_iter()),
                    ),
                }),

            (Term::SigmaElim(a, b, c, d), Some((loc, _))) => {
                Self::infer_type(a.clone(), ctx)
                    .and_then(|type_a| {
                        let type_a = Self::whnf(ctx, type_a);
                        match type_a.data.as_ref() {
                            Term::SigmaType(tx, bnd) => {
                                let nx = b.as_ref().map(|x|x.clone()).unwrap_or_else(|| ctx.fresh());
                                let ny = c.as_ref().map(|y|y.clone()).unwrap_or_else(|| ctx.fresh());
                                let var_x = RcPtr::new(a.location.clone(), Term::Variable(nx.clone()));
                                let var_y = RcPtr::new(a.location.clone(), Term::Variable(ny.clone()));
                                let _guard0 = def(a.clone(), RcPtr::new(a.location.clone(), Term::SigmaIntro(var_x.clone(), var_y)), ctx);
                                let _guard1 = ctx.push_type(nx, tx.clone());
                                let app = RcPtr::new(bnd.location.clone(), Term::App(bnd.clone(), var_x));
                                let _guard2 = ctx.push_type(ny, Term::whnf(ctx, app));
                                if Self::check_type(d.clone(), unsafe { target.clone().unwrap_unchecked() }, ctx) {
                                    target
                                } else {
                                    None
                                }
                            }
                            _ => {
                                ctx.error(term.location.start, |builder|
                                builder
                                    .with_message("Type Error")
                                    .with_label(Label::new((ctx.source_name, term.location.clone()))
                                        .with_color(Color::Red)
                                        .with_message("trying to apply elimination rule of the sigma type"))
                                    .with_label(Label::new((ctx.source_name, a.location.clone()))
                                        .with_color(Color::Red)
                                        .with_message(format!("... however, the matched expression is not of sigma type, the WHNF is {}", a)))
                                    .finish());
                                None
                            }
                        }
                    })
            }
            (Term::IdType(_, _, _), None) => Some(RcPtr::new(term.location.clone(), Term::Type)),
            (Term::IdIntro(x), None) => {
                Self::infer_type(x.clone(), ctx)
                    .map(|type_x| {
                        RcPtr::new(term.location.clone(), Term::IdType(type_x, x.clone(), x.clone()))
                    })
            }
            (Term::IdIntro(a), Some((_, Term::IdType(t, x, y)))) => {
                if Self::check_type(a.clone(), t.clone(), ctx) {
                    if Term::equalize(x , y, ctx, false) {
                        target
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            (Term::IdElim(x, y, z), Some(_)) => {
                Self::infer_type(x.clone(), ctx)
                    .and_then(|x| {
                        let x = Self::whnf(ctx, x);
                        match x.data.as_ref() {
                            Term::IdType(t, a, b) => {
                                let _guard0 = y.as_ref().map(|y| ctx.push_type(y.clone(), t.clone()));
                                let _guard1 = y.as_ref().map(|y| ctx.push_def(y.clone(), x.clone()));
                                let _guard2 = def(a.clone(), b.clone(), ctx);
                                let _guard3 = def(x.clone(), RcPtr::new(x.location.clone(), Term::IdIntro(a.clone())), ctx);
                                if Self::check_type(z.clone(), unsafe { target.clone().unwrap_unchecked() }, ctx) {
                                    target
                                } else {
                                    None
                                }
                            }
                            _ => {
                                ctx.error(term.location.start, |builder|
                                    builder
                                        .with_message("Type Error")
                                        .with_label(Label::new((ctx.source_name, term.location.clone()))
                                            .with_color(Color::Red)
                                            .with_message("trying to apply elimination rule of the identity type"))
                                        .with_label(Label::new((ctx.source_name, x.location.clone()))
                                            .with_color(Color::Red)
                                            .with_message(format!("... however, the matched expression is not of identity type, the WHNF is {}", x)))
                                        .finish());
                                None
                            }
                        }
                    })
            }

            (_, Some(_)) => {
                Self::infer_type(term, ctx)
                    .and_then( |x| {
                        if Term::equalize(&x, unsafe { target.as_ref().unwrap_unchecked() }, ctx, true) {
                            Some(x)
                        } else {
                            None
                        }
                    })
            }

            _ => {
                ctx.error(
                    term.location.start,
                    |builder| builder
                        .with_message("Type error")
                        .with_label(Label::new((ctx.source_name, term.location.clone()))
                            .with_message(format!("cannot infer the type (WNHF: {})", term))
                            .with_color(Color::Red))
                        .finish()
                );
                None
            },
        };
        if let Some(target) = debug_target.as_ref() {
            eprintln!("type checking {} against {}", debug_term, target);
        } else {
            eprintln!("infer {}", debug_term);
        }
        eprintln!(
            "context: {:?}",
            unsafe { (*ctx.local_types.get()).iter() }.collect::<Vec<_>>()
        );
        match result.as_ref() {
            Some(x) => eprintln!("result: {}\n", x),
            None => eprintln!("result: failed\n"),
        }
        result
    }

    fn infer_type<'a>(
        term: Self::Wrapper<Self>,
        ctx: &Self::Context<'a>,
    ) -> Option<Self::Wrapper<Self>> {
        match term.data.as_ref() {
            Term::Ann(_, _) => Self::check_term(term, None, ctx),
            Term::Variable(x) if x.literal() == "u" => {
                let nf = Self::whnf(ctx, term);
                Self::check_term(nf, None, ctx)
            },
            _ => Self::check_term(Self::whnf(ctx, term), None, ctx),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_type_check_0() {
        let source = r#"
        module Test
        test : Bool -> (`Sigma Bool, Bool)
        test x = case x of {
            True -> let u = x in (@Pair u x);
            False -> (@Pair x x);
        }
        "#;
        let definitions = crate::term::test::get_definitions(source);
        let context = TypeCheckContext::new("test.txt", definitions.iter());
        let mut flag = true;
        for i in definitions {
            flag = flag && Term::check_type(i.term, i.signature, &context);
        }
        for i in context.take_reports() {
            i.print(("test.txt", ariadne::Source::from(source)))
                .unwrap()
        }
        assert!(flag);
    }
    #[test]
    fn test_type_check_1() {
        let source = r#"
        module Test
        explosion : (x : Type) -> Bottom -> x
        explosion x b = case b of {}
        "#;
        let definitions = crate::term::test::get_definitions(source);
        let context = TypeCheckContext::new("test.txt", definitions.iter());
        let mut flag = true;
        for i in definitions {
            flag = flag && Term::check_type(i.term, i.signature, &context);
        }
        for i in context.take_reports() {
            i.print(("test.txt", ariadne::Source::from(source)))
                .unwrap()
        }
        assert!(flag);
    }
    #[test]
    fn test_type_check_2() {
        let source = r#"
        module Test
        prjLeft : (x : Type) -> (y : Type) -> (`Sigma x, y) -> x
        prjLeft x y p = case p of {
            Pair a b -> a;
        }
        "#;
        let definitions = crate::term::test::get_definitions(source);
        let context = TypeCheckContext::new("test.txt", definitions.iter());
        let mut flag = true;
        for i in definitions {
            flag = flag && Term::check_type(i.term, i.signature, &context);
        }
        for i in context.take_reports() {
            i.print(("test.txt", ariadne::Source::from(source)))
                .unwrap()
        }
        assert!(flag);
    }
    #[test]
    fn test_type_check_3() {
        let source = r#"
        module Test
        id : (x : Type) -> x -> x
        id _ x = x

        prjLeft : (x : Type) -> (y : Type) -> (`Sigma x, y) -> (`Sigma x, x)
        prjLeft x y p = case p of {
            Pair a b -> (@Pair (id x a) (id x a));
        }
        "#;
        let definitions = crate::term::test::get_definitions(source);
        let context = TypeCheckContext::new("test.txt", definitions.iter());
        let mut flag = true;
        for i in definitions {
            flag = flag && Term::check_type(i.term, i.signature, &context);
        }
        for i in context.take_reports() {
            i.print(("test.txt", ariadne::Source::from(source)))
                .unwrap()
        }
        assert!(flag);
    }

    #[test]
    fn test_type_wrong_ann() {
        let source = r#"
        module Test
        id : (x : Type) -> x -> x
        id _ x = x

        prjLeft : (x : Type) -> (y : Type) -> (`Sigma x, y) -> (`Sigma x, x)
        prjLeft x y p = case p of {
            Pair a b -> let a : Bool = a in (@Pair (id x a) (id x a));
        }
        "#;
        let definitions = crate::term::test::get_definitions(source);
        let context = TypeCheckContext::new("test.txt", definitions.iter());
        let mut flag = true;
        for i in definitions {
            flag = flag && Term::check_type(i.term, i.signature, &context);
        }
        for i in context.take_reports() {
            i.print(("test.txt", ariadne::Source::from(source)))
                .unwrap()
        }
        assert!(!flag);
    }

    #[test]
    fn test_type_wrong_type_level() {
        let source = r#"
        module Test
        correct : Bool -> Type
        correct x = case x of {
            True -> Unit;
            False -> Bottom;
        }
        illegal : Bool -> Type
        illegal x = case x of {
            True -> @True;
            False -> Bottom;
        }
        "#;
        let definitions = crate::term::test::get_definitions(source);
        let context = TypeCheckContext::new("test.txt", definitions.iter());
        let mut flag = true;
        for i in definitions {
            flag = flag && Term::check_type(i.term, i.signature, &context);
        }
        for i in context.take_reports() {
            i.print(("test.txt", ariadne::Source::from(source)))
                .unwrap()
        }
        assert!(!flag);
    }

    #[test]
    fn test_type_refl_intro() {
        let source = r#"
        module Test
        refl : (x : Type) -> (i : x) -> (Id x i i)
        refl x i = (@Refl i)
        "#;
        let definitions = crate::term::test::get_definitions(source);
        let context = TypeCheckContext::new("test.txt", definitions.iter());
        let mut flag = true;
        for i in definitions {
            flag = flag && Term::check_type(i.term, i.signature, &context);
        }
        for i in context.take_reports() {
            i.print(("test.txt", ariadne::Source::from(source)))
                .unwrap()
        }
        assert!(flag);
    }
    #[test]
    fn test_type_wrong_refl() {
        let source = r#"
        module Test
        absurd : (i : Bool) -> (Id Bool @False i)
        absurd i = (@Refl i)
        "#;
        let definitions = crate::term::test::get_definitions(source);
        let context = TypeCheckContext::new("test.txt", definitions.iter());
        let mut flag = true;
        for i in definitions {
            flag = flag && Term::check_type(i.term, i.signature, &context);
        }
        for i in context.take_reports() {
            i.print(("test.txt", ariadne::Source::from(source)))
                .unwrap()
        }
        assert!(!flag);
    }
    #[test]
    fn test_type_wrong_refl_elim() {
        let source = r#"
        module Test
        absurd : (i : Bool) -> (Id Bool @False i)
        absurd i = case @True of {
            Refl _ -> !!;
        }
        "#;
        let definitions = crate::term::test::get_definitions(source);
        let context = TypeCheckContext::new("test.txt", definitions.iter());
        let mut flag = true;
        for i in definitions {
            flag = flag && Term::check_type(i.term, i.signature, &context);
        }
        for i in context.take_reports() {
            i.print(("test.txt", ariadne::Source::from(source)))
                .unwrap()
        }
        assert!(!flag);
    }
    #[test]
    fn test_type_proof_neg_neg() {
        let source = r#"
        module Test
        neg : Bool -> Bool
        neg x = case x of {
            True -> @True;
            False -> @False;
        }

        lemma : (x : Bool) -> (Id Bool (neg (neg x)) x)
        lemma x = case x of {
            True -> (@Refl @True);
            False -> (@Refl @False);
        }
        "#;
        let definitions = crate::term::test::get_definitions(source);
        let context = TypeCheckContext::new("test.txt", definitions.iter());
        let mut flag = true;
        for i in definitions {
            flag = flag && Term::check_type(i.term, i.signature, &context);
        }
        for i in context.take_reports() {
            i.print(("test.txt", ariadne::Source::from(source)))
                .unwrap()
        }
        assert!(flag);
    }
    #[test]
    fn test_type_transport() {
        let source = r#"
        module Test
        transport : (a : Type) -> (b : Type) -> (x : a) -> (y : a) -> (Id a x y) -> (f : a -> b) -> (Id b (f a) (f b))
        transport a b x y p f = case p of {
            Refl _ -> (@Refl (f x));
        }
        "#;
        let definitions = crate::term::test::get_definitions(source);
        let context = TypeCheckContext::new("test.txt", definitions.iter());
        let mut flag = true;
        for i in definitions {
            println!("signature: {}", i.signature);
            println!("def: {}\n", i.term);
            flag = flag && Term::check_type(i.term, i.signature, &context);
        }
        for i in context.take_reports() {
            i.print(("test.txt", ariadne::Source::from(source)))
                .unwrap()
        }
        assert!(flag);
    }
}
