use crate::term::{Name, RcPtr, Term};
use std::collections::HashMap;
use std::rc::Rc;

pub trait Instantiation: Sized {
    type Name;
    type Wrapper<T>;
    fn instantiate<I>(body: Self::Wrapper<Self>, iter: I) -> Self::Wrapper<Self>
    where
        I: Iterator<Item = (Name, Self::Wrapper<Self>)>;
}

impl Instantiation for Term {
    type Name = Name;

    type Wrapper<T> = RcPtr<T>;

    fn instantiate<I>(body: Self::Wrapper<Self>, iter: I) -> Self::Wrapper<Self>
    where
        I: Iterator<Item = (Name, Self::Wrapper<Self>)>,
    {
        let map = HashMap::from_iter(iter);
        fn instantiate_with_map(
            tree: RcPtr<Term>,
            map: &HashMap<Name, RcPtr<Term>>,
        ) -> RcPtr<Term> {
            match tree.data.as_ref() {
                Term::Type => tree,
                Term::Variable(a) => {
                    if let Some(tree) = map.get(a).cloned() {
                        tree
                    } else {
                        tree
                    }
                }
                Term::Lam(x, a) => {
                    let new_a = instantiate_with_map(a.clone(), map);
                    if Rc::ptr_eq(&a.data, &new_a.data) {
                        tree
                    } else {
                        RcPtr::new(tree.location, Term::Lam(x.clone(), new_a))
                    }
                }
                Term::App(a, b) => {
                    let new_a = instantiate_with_map(a.clone(), map);
                    let new_b = instantiate_with_map(b.clone(), map);
                    if Rc::ptr_eq(&a.data, &new_a.data) && Rc::ptr_eq(&b.data, &new_b.data) {
                        tree
                    } else {
                        RcPtr::new(tree.location, Term::App(new_a, new_b))
                    }
                }
                Term::Pi(a, b) => {
                    let new_a = instantiate_with_map(a.clone(), map);
                    let new_b = instantiate_with_map(b.clone(), map);
                    if Rc::ptr_eq(&a.data, &new_a.data) && Rc::ptr_eq(&b.data, &new_b.data) {
                        tree
                    } else {
                        RcPtr::new(tree.location, Term::Pi(new_a, new_b))
                    }
                }
                Term::Ann(a, b) => {
                    let new_a = instantiate_with_map(a.clone(), map);
                    let new_b = instantiate_with_map(b.clone(), map);
                    if Rc::ptr_eq(&a.data, &new_a.data) && Rc::ptr_eq(&b.data, &new_b.data) {
                        tree
                    } else {
                        RcPtr::new(tree.location, Term::Ann(new_a, new_b))
                    }
                }
                Term::Let(x, a, b) => {
                    let new_a = instantiate_with_map(a.clone(), map);
                    let new_b = instantiate_with_map(b.clone(), map);
                    if Rc::ptr_eq(&a.data, &new_a.data) && Rc::ptr_eq(&b.data, &new_b.data) {
                        tree
                    } else {
                        RcPtr::new(tree.location, Term::Let(x.clone(), new_a, new_b))
                    }
                }
                Term::TrustMe => tree,
                Term::BottomType => tree,
                Term::BottomElim(a) => {
                    let new_a = instantiate_with_map(a.clone(), map);
                    if Rc::ptr_eq(&a.data, &new_a.data) {
                        tree
                    } else {
                        RcPtr::new(tree.location, Term::BottomElim(new_a))
                    }
                }
                Term::UnitType => tree,
                Term::UnitIntro => tree,
                Term::UnitElim(a, b) => {
                    let new_a = instantiate_with_map(a.clone(), map);
                    let new_b = instantiate_with_map(b.clone(), map);
                    if Rc::ptr_eq(&a.data, &new_a.data) && Rc::ptr_eq(&b.data, &new_b.data) {
                        tree
                    } else {
                        RcPtr::new(tree.location, Term::UnitElim(new_a, new_b))
                    }
                }
                Term::BoolType => tree,
                Term::BoolIntro(_) => tree,
                Term::BoolElim(a, b, c) => {
                    let new_a = instantiate_with_map(a.clone(), map);
                    let new_b = instantiate_with_map(b.clone(), map);
                    let new_c = instantiate_with_map(c.clone(), map);
                    if Rc::ptr_eq(&a.data, &new_a.data)
                        && Rc::ptr_eq(&b.data, &new_b.data)
                        && Rc::ptr_eq(&c.data, &new_c.data)
                    {
                        tree
                    } else {
                        RcPtr::new(tree.location, Term::BoolElim(new_a, new_b, new_c))
                    }
                }
                Term::SigmaType(a, b) => {
                    let new_a = instantiate_with_map(a.clone(), map);
                    let new_b = instantiate_with_map(b.clone(), map);
                    if Rc::ptr_eq(&a.data, &new_a.data) && Rc::ptr_eq(&b.data, &new_b.data) {
                        tree
                    } else {
                        RcPtr::new(tree.location, Term::SigmaType(new_a, new_b))
                    }
                }
                Term::SigmaIntro(a, b) => {
                    let new_a = instantiate_with_map(a.clone(), map);
                    let new_b = instantiate_with_map(b.clone(), map);
                    if Rc::ptr_eq(&a.data, &new_a.data) && Rc::ptr_eq(&b.data, &new_b.data) {
                        tree
                    } else {
                        RcPtr::new(tree.location, Term::SigmaIntro(new_a, new_b))
                    }
                }
                Term::SigmaElim(a, x, y, b) => {
                    let new_a = instantiate_with_map(a.clone(), map);
                    let new_b = instantiate_with_map(b.clone(), map);
                    if Rc::ptr_eq(&a.data, &new_a.data) && Rc::ptr_eq(&b.data, &new_b.data) {
                        tree
                    } else {
                        RcPtr::new(
                            tree.location,
                            Term::SigmaElim(new_a, x.clone(), y.clone(), new_b),
                        )
                    }
                }
            }
        }
        instantiate_with_map(body, &map)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_instantiate() {
        let source = r#"
        module Test
        test : Bool -> (`Sigma Bool, Bool)
        test x = case x of {
            True -> let u = x in (@Pair u x);
            False -> (@Pair x x);
        } 
        "#;
        let definitions = crate::term::test::get_definitions(source);
        let tree = definitions.first().unwrap().term.clone();
        match tree.data.as_ref() {
            Term::Ann(x, _) => match x.data.as_ref() {
                Term::Lam(name, body) => {
                    let target = RcPtr::new(0..0, Term::BoolIntro(true));
                    let result = Term::instantiate(
                        body.clone(),
                        [(name.clone().unwrap(), target)].into_iter(),
                    );
                    assert_eq!(format!("{}", result), "(𝟚-elim True (let u = True in (((λ fresh_0 . (λ fresh_1 . (fresh_0 , fresh_1))) u) True)) (((λ fresh_2 . (λ fresh_3 . (fresh_2 , fresh_3))) True) True))")
                }
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }
}
