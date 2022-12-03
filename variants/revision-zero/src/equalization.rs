use crate::alpha_equality::AlphaEquality;
use crate::term::{Name, RcPtr, Term};
use crate::typecheck::TypeCheckContext;

trait Equalization: Sized {
    type Name;
    type Wrapper<T>;
    type Context<'a>;

    fn equalize<'a>(
        x: &Self::Wrapper<Self>,
        y: &Self::Wrapper<Self>,
        ctx: &Self::Context<'a>,
    ) -> bool;
}

impl Equalization for Term {
    type Name = Name;

    type Wrapper<T> = RcPtr<T>;

    type Context<'a> = TypeCheckContext<'a>;

    fn equalize<'a>(
        x: &Self::Wrapper<Self>,
        y: &Self::Wrapper<Self>,
        ctx: &Self::Context<'a>,
    ) -> bool {
        if x.data.as_ref().alpha_equal(y.data.as_ref()) {
            return true;
        }
        match (x.data.as_ref(), y.data.as_ref()) {
            _ => todo!(),
        }
    }
}
