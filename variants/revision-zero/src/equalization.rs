use crate::term::{Name, RcPtr, Term};
use std::collections::HashMap;

trait Equlization: Sized {
    type Name;
    type Wrapper<T>;
    type Context;

    fn equalize(x: &Self::Wrapper<Self>, y: &Self::Wrapper<Self>, ctx: &Self::Context) -> bool;
}
