use crate::alpha_equality::AlphaEquality;
use crate::term::{self, Guard, Name, RcPtr, Term};
use crate::typecheck::TypeCheckContext;
use crate::whnf::WeakHeadNF;
use ariadne::{Color, Label};
pub trait Equalization: Sized {
    type Name;
    type Wrapper<T>;
    type Context<'a>;

    fn equalize<'a>(
        x: &Self::Wrapper<Self>,
        y: &Self::Wrapper<Self>,
        ctx: &Self::Context<'a>,
        typecheck: bool,
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
        typecheck: bool,
    ) -> bool {
        if x.data.as_ref().alpha_equal(y.data.as_ref()) {
            return true;
        }
        let x = Term::whnf(ctx, x.clone());
        let y = Term::whnf(ctx, y.clone());
        #[cfg(feature = "debug")]
        {
            eprintln!("equating {} with {}", x, y);
        }
        match (x.data.as_ref(), y.data.as_ref()) {
            (Term::Type, Term::Type)
            | (Term::TrustMe, Term::TrustMe)
            | (Term::BottomType, Term::BottomType)
            | (Term::UnitType, Term::UnitType)
            | (Term::UnitIntro, Term::UnitIntro)
            | (Term::BoolType, Term::BoolType) => true,

            // if a fresh variable exists in the normal form, it means that
            // they are currently not resolved within the scope, thus we directly
            // compare whether they are refering to the name object.
            (Term::Variable(a), Term::Variable(b)) if a == b => true,
            | (Term::IdIntro(x), Term::IdIntro(y))
            => Self::equalize(x, y, ctx, typecheck),

            (Term::Lam(nx, x0), Term::Lam(ny, y0)) => {
                let _guard = if let (Some(nx), Some(ny)) = (nx, ny) {
                    Some(ctx.push_def(ny.clone(), RcPtr::new(x.location.start..x0.location.start, Term::Variable(nx.clone()))))
                } else {
                    None
                };
                Self::equalize(x0, y0, ctx, typecheck)
            }

            (Term::SigmaElim(x0, nx, mx, x1), Term::SigmaElim(y0, ny, my, y1)) => {
                Self::equalize(x0, y0, ctx, typecheck) && {
                    let _guard = if let (Some(nx), Some(ny)) = (nx, ny) {
                        Some(ctx.push_def(ny.clone(), RcPtr::new(x0.location.end..x1.location.start, Term::Variable(nx.clone()))))
                    } else {
                        None
                    };
                    let _guard = if let (Some(mx), Some(my)) = (mx, my) {
                        Some(ctx.push_def(my.clone(), RcPtr::new(x0.location.start..x1.location.start, Term::Variable(mx.clone()))))
                    } else {
                        None
                    };
                    Self::equalize(x1, y1, ctx, typecheck)
                }
            }
            (Term::IdElim(x0, nx,  x1), Term::IdElim(y0, ny, y1)) => {
                Self::equalize(x0, y0, ctx, typecheck) && {
                    let _guard = if let (Some(nx), Some(ny)) = (nx, ny) {
                        Some(ctx.push_def(ny.clone(), RcPtr::new(x0.location.end..x1.location.start, Term::Variable(nx.clone()))))
                    } else {
                        None
                    };
                    Self::equalize(x1, y1, ctx, typecheck)
                }
            }
            (Term::App(x0, x1), Term::App(y0, y1))
            | (Term::Pi(x0, x1), Term::Pi(y0, y1))
            | (Term::UnitElim(x0, x1), Term::UnitElim(y0, y1))
            | (Term::SigmaType(x0, x1), Term::SigmaType(y0, y1))
            | (Term::SigmaIntro(x0, x1), Term::SigmaIntro(y0, y1))
            //| (Term::Let(_, x0, x1), Term::Let(_, y0, y1)) -- this should not appear at WHNF
            => {
                Self::equalize(x0, y0, ctx, typecheck) && Self::equalize(x1, y1, ctx, typecheck)
            }
            (Term::BoolIntro(x), Term::BoolIntro(y)) => x == y,
            (Term::BoolElim(x0, x1, x2), Term::BoolElim(y0, y1, y2))
            | (Term::IdType(x0, x1, x2), Term::IdType(y0, y1, y2))
            => {
                Self::equalize(x0, y0, ctx, typecheck)
                    && Self::equalize(x1, y1, ctx, typecheck)
                    && Self::equalize(x2, y2, ctx, typecheck)
            }
            _ => {
                ctx.error(x.location.start, |builder| builder
                    .with_message("Failed to equalize weak-head normal form")
                    .with_label(Label::new((ctx.source_name(), x.location.clone()))
                        .with_color(Color::Red)
                        .with_message(format!("the term at this position has WHNF: {}", x)))
                    .with_label(Label::new((ctx.source_name(), y.location.clone()))
                        .with_color(Color::Red)
                        .with_message(format!("... however, it is expected to equate with the term provided here, whose WHNF is {}", y)))
                    .finish());
                false
            }
        }
    }
}
