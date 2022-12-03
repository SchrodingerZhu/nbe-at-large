use crate::term::{Name, RcPtr, Term};
use ariadne::Report;
use std::cell::UnsafeCell;
use std::collections::HashMap;
trait BidirectionalTypeCheck: Sized {
    type Wrapper<T>;
    // TODO
}

pub struct TypeCheckContext {
    global_defs: HashMap<Name, RcPtr<Term>, RcPtr<Term>>,

    reports: UnsafeCell<Vec<Report>>,
    local_defs: UnsafeCell<HashMap<Name, RcPtr<Term>>>,
    local_signatures: UnsafeCell<HashMap<Name, RcPtr<Term>>>,
}

impl TypeCheckContext {}
