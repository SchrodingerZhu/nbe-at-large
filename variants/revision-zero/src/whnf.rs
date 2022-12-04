use crate::instantiation::Instantiation;
use crate::term::{Name, RcPtr, Term};
use std::rc::Rc;
pub trait WeakHeadNF: Sized {
    type Wrapper<T>: Clone;
    type Name;
    type Context<'a>;
    fn whnf<'a>(context: &Self::Context<'a>, tree: Self::Wrapper<Self>) -> Self::Wrapper<Self>;
}

impl WeakHeadNF for Term {
    fn whnf<'a>(ctx: &Self::Context<'a>, tree: RcPtr<Self>) -> RcPtr<Self> {
        match tree.data.as_ref() {
            Term::Type => tree,
            Term::Variable(x) => match ctx.lookup_def(x) {
                Some(def) => Term::whnf(ctx, def.clone()),
                None => tree.clone(),
            },
            Term::Lam(_, _) => tree,
            Term::App(x, y) => {
                let nf = Term::whnf(ctx, x.clone());
                match nf.data.as_ref() {
                    Term::Lam(name, body) => {
                        let body = match name {
                            None => body.clone(),
                            Some(name) => Term::instantiate(
                                body.clone(),
                                [(name.clone(), y.clone())].into_iter(),
                            ),
                        };
                        Term::whnf(ctx, body)
                    }
                    _ if Rc::ptr_eq(&x.data, &nf.data) => tree,
                    _ => RcPtr::new(tree.location, Term::App(nf, y.clone())),
                }
            }
            Term::Pi(_, _) => tree,
            Term::Ann(x, _) => x.clone(),
            Term::Let(x, y, z) => match x {
                Some(name) => {
                    let body =
                        Term::instantiate(z.clone(), [(name.clone(), y.clone())].into_iter());
                    Term::whnf(ctx, body)
                }
                None => Term::whnf(ctx, z.clone()),
            },
            Term::TrustMe => tree,
            Term::BottomType => tree,
            Term::BottomElim(_) => tree,
            Term::UnitType => tree,
            Term::UnitIntro => tree,
            Term::UnitElim(x, y) => {
                let nf = Term::whnf(ctx, x.clone());
                match nf.data.as_ref() {
                    Term::UnitIntro => Term::whnf(ctx, y.clone()),
                    _ if Rc::ptr_eq(&nf.data, &x.data) => tree,
                    _ => RcPtr::new(tree.location, Term::UnitElim(nf, y.clone())),
                }
            }
            Term::BoolType => tree,
            Term::BoolIntro(_) => tree,
            Term::BoolElim(x, y, z) => {
                let nf = Term::whnf(ctx, x.clone());
                match nf.data.as_ref() {
                    Term::BoolIntro(true) => Term::whnf(ctx, y.clone()),
                    Term::BoolIntro(false) => Term::whnf(ctx, z.clone()),
                    _ if Rc::ptr_eq(&nf.data, &x.data) => tree,
                    _ => RcPtr::new(tree.location, Term::BoolElim(nf, y.clone(), z.clone())),
                }
            }
            Term::SigmaType(_, _) => tree,
            Term::SigmaIntro(_, _) => tree,
            Term::SigmaElim(x, a, b, y) => {
                let nf = Term::whnf(ctx, x.clone());
                match nf.data.as_ref() {
                    Term::SigmaIntro(av, bv) => {
                        let mut vars = Vec::new();
                        if let Some(name) = a {
                            vars.push((name.clone(), av.clone()));
                        }
                        if let Some(name) = b {
                            vars.push((name.clone(), bv.clone()));
                        }
                        let y = Term::instantiate(y.clone(), vars.into_iter());
                        Term::whnf(ctx, y)
                    }
                    _ if Rc::ptr_eq(&nf.data, &x.data) => tree,
                    _ => RcPtr::new(
                        tree.location,
                        Term::SigmaElim(nf, a.clone(), b.clone(), y.clone()),
                    ),
                }
            }
        }
    }

    type Wrapper<T> = RcPtr<T>;
    type Name = Name;
    type Context<'a> = crate::typecheck::TypeCheckContext<'a>;
}

#[cfg(test)]
mod test {
    use crate::typecheck::TypeCheckContext;

    use super::*;
    #[test]
    fn test_whnf() {
        let source = r#"
        module Test

        test : Bool -> (`Sigma Bool, Bool)
        test x = case (id Bool testValue) of {
            True -> let u = x in (@Pair u x);
            False -> (@Pair x x);
        }

        testValue : Bool
        testValue = @True

        id : (t : Type) -> t -> t
        id _ x = x
        "#;
        let definitions = crate::term::test::get_definitions(source);
        let tree = {
            definitions
                .iter()
                .filter(|x| x.name.literal() == "test")
                .next()
                .unwrap()
                .term
                .clone()
        };
        match tree.data.as_ref() {
            Term::Lam(name, body) => {
                let target = RcPtr::new(0..0, Term::BoolIntro(true));
                let result =
                    Term::instantiate(body.clone(), [(name.clone().unwrap(), target)].into_iter());
                assert_eq!(
                    "(True , True)",
                    format!(
                        "{}",
                        Term::whnf(&TypeCheckContext::new("test", definitions.iter()), result)
                    )
                )
            }
            _ => unreachable!(),
        }
    }
}
