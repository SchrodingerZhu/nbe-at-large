use crate::term::{Definition, Name, RcPtr, Term};
use crate::whnf::WeakHeadNF;
use ariadne::{Report, ReportBuilder};
use std::cell::{Cell, UnsafeCell};
use std::collections::HashMap;
use std::ops::Range;
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
        Self::check_term(term, None, ctx)
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
    local_hints: UnsafeCell<HashMap<Name, RcPtr<Term>>>,
    local_types: UnsafeCell<HashMap<Name, RcPtr<Term>>>,
    fresh_counter: Cell<usize>,
}

enum ChangeLog {
    LocalDef(Name, Option<RcPtr<Term>>),
    LocalHint(Name, Option<RcPtr<Term>>),
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
            ChangeLog::LocalHint(name, delta) => (name.clone(), delta, unsafe {
                &mut *self.ctx.local_hints.get()
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
    pub fn lookup_hint(&self, name: &Name) -> Option<RcPtr<Term>> {
        unsafe { (*self.local_hints.get()).get(name).cloned() }
    }
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

    pub fn push_hint<'b>(&'b self, name: Name, value: RcPtr<Term>) -> Guard<'a, 'b> {
        Guard {
            ctx: self,
            changelog: ChangeLog::LocalHint(name.clone(), unsafe {
                (*self.local_hints.get()).insert(name, value)
            }),
        }
    }

    pub fn push_type<'b>(&'b self, name: Name, value: RcPtr<Term>) -> Guard<'a, 'b> {
        Guard {
            ctx: self,
            changelog: ChangeLog::LocalType(name.clone(), unsafe {
                (*self.local_hints.get()).insert(name, value)
            }),
        }
    }

    pub fn push_def<'b>(&'b self, name: Name, value: RcPtr<Term>) -> Guard<'a, 'b> {
        Guard {
            ctx: self,
            changelog: ChangeLog::LocalDef(name.clone(), unsafe {
                (*self.local_hints.get()).insert(name, value)
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
            local_hints: Default::default(),
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
            local_hints: Default::default(),
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

fn ensure_type<'a>(term: RcPtr<Term>, ctx: &TypeCheckContext<'a>) -> bool {
    let target = RcPtr::new(term.location.clone(), Term::Type);
    Term::check_type(term, target, ctx)
}

fn ensure_pi<'a>(
    term: RcPtr<Term>,
    ctx: &TypeCheckContext<'a>,
) -> Option<(RcPtr<Term>, RcPtr<Term>)> {
    let location = term.location.clone();
    let term = Term::whnf(ctx, term);
    match term.data.as_ref() {
        Term::Pi(x, y) => Some((x.clone(), y.clone())),
        _ => {
            ctx.error(todo!(), |_| todo!());
            None
        }
    }
}

impl BidirectionalTypeCheck for Term {
    fn check_term<'a>(
        term: Self::Wrapper<Self>,
        target: Option<Self::Wrapper<Self>>,
        ctx: &Self::Context<'a>,
    ) -> Option<Self::Wrapper<Self>> {
        match (term.data.as_ref(), target.as_ref().map(|x| x.data.as_ref())) {
            (Term::Variable(x), None) => return ctx.lookup_type(x),
            (Term::Type, None) => return Some(term),
            (Term::Pi(a, bnd), None) => {
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
            (Term::Lam(name, body), Some(Term::Pi(a, bnd))) => {
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
            _ => todo!(),
        }
    }
}
