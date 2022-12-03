use crate::term::{Name, Term};
use std::cell::UnsafeCell;
use std::collections::HashMap;

pub trait AlphaEquality {
    fn alpha_equal(&self, other: &Self) -> bool;
}

impl AlphaEquality for Term {
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
}
