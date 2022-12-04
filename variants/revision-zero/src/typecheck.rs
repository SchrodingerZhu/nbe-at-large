use crate::term::{Definition, Name, RcPtr, Term};
use ariadne::{Report, ReportBuilder};
use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::ops::Range;
trait BidirectionalTypeCheck: Sized {
    type Wrapper<T>;
    // TODO
}

type NamedSpan<'a> = (&'a str, Range<usize>);

pub struct TypeCheckContext<'a> {
    source_name: &'a str,
    global_defs: HashMap<Name, Definition>,

    reports: UnsafeCell<Vec<Report<NamedSpan<'a>>>>,
    local_defs: UnsafeCell<HashMap<Name, RcPtr<Term>>>,
    local_hints: UnsafeCell<HashMap<Name, RcPtr<Term>>>,
    local_types: UnsafeCell<HashMap<Name, RcPtr<Term>>>,
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
        }
    }
}
