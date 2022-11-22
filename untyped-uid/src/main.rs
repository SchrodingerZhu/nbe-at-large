use std::fmt::{Debug, Formatter};
use std::hash::Hasher;
use std::rc::Rc;

use pest::{iterators::Pair, Parser};

#[derive(Clone, Debug)]
struct UniqueName(Rc<str>);

impl UniqueName {
    fn new<S: AsRef<str>>(name: S) -> Self {
        let name = name.as_ref().to_string();
        let data = name.into_boxed_str();
        Self(Rc::from(data))
    }

    fn uid(&self) -> *const str {
        Rc::as_ptr(&self.0)
    }
}

impl std::fmt::Display for UniqueName {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}@{:?}", self.0.as_ref(), self.uid())
    }
}

impl PartialEq<Self> for UniqueName {
    fn eq(&self, other: &Self) -> bool {
        self.uid() == other.uid()
    }
}

impl std::hash::Hash for UniqueName {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.uid().hash(state)
    }
}

impl Eq for UniqueName {}

#[derive(Debug, Clone)]
enum Term<T: Debug + Clone> {
    Var(T),
    Lam(T, Box<Self>),
    App(Box<Self>, Box<Self>),
    Let(T, Box<Self>, Box<Self>),
}

type PrimitiveTerm<'a> = Term<&'a str>;
type CapAvoidTerm = Term<UniqueName>;

#[derive(pest_derive::Parser)]
#[grammar = "syntax.pest"]
struct LambdaParser;

fn translate(x: Pair<Rule>) -> Box<PrimitiveTerm> {
    match x.as_rule() {
        Rule::expr => translate(x.into_inner().next().unwrap()),
        Rule::var => Box::new(Term::Var(x.as_str())),
        Rule::let_expr => {
            let mut iter = x.into_inner();
            let var = iter.next().unwrap().as_str();
            let binding = translate(iter.next().unwrap());
            let body = translate(iter.next().unwrap());
            Box::new(Term::Let(var, binding, body))
        }
        Rule::lambda_expr => {
            let mut iter = x.into_inner();
            let var = iter.next().unwrap().as_str();
            let body = translate(iter.next().unwrap());
            Box::new(Term::Lam(var, body))
        }
        Rule::app_expr => {
            let mut iter = x.into_inner();
            let a = translate(iter.next().unwrap());
            let b = translate(iter.next().unwrap());
            Box::new(Term::App(a, b))
        }
        _ => panic!("unexpected token"),
    }
}

fn parse_tree(input: &str) -> Box<PrimitiveTerm> {
    translate(
        LambdaParser::parse(Rule::file, input)
            .unwrap()
            .next()
            .unwrap()
            .into_inner()
            .filter_map(|x| match x.as_rule() {
                Rule::expr => Some(x),
                _ => None,
            })
            .next()
            .unwrap(),
    )
}

fn to_capture_avoidance_term(term: &PrimitiveTerm) -> Box<CapAvoidTerm> {
    struct Context<'a>(std::cell::UnsafeCell<std::collections::HashMap<&'a str, UniqueName>>);
    struct Guard<'a, 'b>(&'b Context<'a>, &'a str, Option<UniqueName>);
    impl<'a> Context<'a> {
        fn new() -> Self {
            Context(std::cell::UnsafeCell::new(std::collections::HashMap::new()))
        }

        fn get(&self, name: &str) -> Option<UniqueName> {
            unsafe { (*self.0.get()).get(name).cloned() }
        }

        fn push<'b>(&'b self, name: &'a str) -> (UniqueName, Guard<'a, 'b>) {
            let unique = UniqueName::new(name);
            let replacement = unsafe { (*self.0.get()).insert(name, unique.clone()) };
            (unique, Guard::<'a, 'b>(self, name, replacement))
        }
    }

    impl<'a, 'b> Drop for Guard<'a, 'b> {
        fn drop(&mut self) {
            let upstream = unsafe { &mut *self.0 .0.get() };
            if let Some(x) = self.2.take() {
                upstream.insert(self.1, x);
            } else {
                upstream.remove(self.1);
            }
        }
    }

    let mut ctx = Context::new();
    fn convert<'a>(ctx: &Context<'a>, term: &PrimitiveTerm<'a>) -> Box<CapAvoidTerm> {
        match term {
            PrimitiveTerm::Var(x) => Box::new(CapAvoidTerm::Var(ctx.get(*x).unwrap())),
            PrimitiveTerm::Lam(name, body) => {
                let (name, _guard) = ctx.push(name);
                let body = convert(ctx, body);
                Box::new(CapAvoidTerm::Lam(name, body))
            }
            PrimitiveTerm::App(lhs, rhs) => {
                let lhs = convert(ctx, lhs);
                let rhs = convert(ctx, rhs);
                Box::new(CapAvoidTerm::App(lhs, rhs))
            }
            PrimitiveTerm::Let(x, y, z) => {
                let (x, _guard) = ctx.push(x);
                let y = convert(ctx, y);
                let z = convert(ctx, z);
                Box::new(CapAvoidTerm::Let(x, y, z))
            }
        }
    }

    convert(&mut ctx, term)
}

impl<T: std::fmt::Display + Debug + Clone> std::fmt::Display for Term<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Var(x) => write!(f, "{}", x),
            Term::Lam(x, y) => write!(f, "λ {} . {}", x, y),
            Term::App(x, y) => write!(f, "({} {})", x, y),
            Term::Let(x, y, z) => write!(f, "(let {} = {} in {})", x, y, z),
        }
    }
}

#[derive(Clone, Debug)]
enum Value<'a> {
    Var(UniqueName),
    App(Rc<Value<'a>>, Rc<Value<'a>>),
    Lam(
        UniqueName,
        Vec<(UniqueName, Rc<Value<'a>>)>,
        &'a CapAvoidTerm,
    ),
}

struct Context<'a>(std::cell::UnsafeCell<std::collections::HashMap<UniqueName, Rc<Value<'a>>>>);
struct Guard<'a, 'b>(&'b Context<'a>, Vec<UniqueName>);

impl<'a> Context<'a> {
    fn new() -> Self {
        Context(std::cell::UnsafeCell::new(std::collections::HashMap::new()))
    }

    fn get(&self, name: &UniqueName) -> Option<Rc<Value<'a>>> {
        unsafe { (*self.0.get()).get(name).cloned() }
    }

    fn to_closure(&self) -> Vec<(UniqueName, Rc<Value<'a>>)> {
        unsafe {
            (*self.0.get())
                .iter()
                .map(|x| (x.0.clone(), x.1.clone()))
                .collect()
        }
    }

    fn from_closure<'b, I>(i: I) -> Context<'a>
    where
        I: Iterator<Item = &'b (UniqueName, Rc<Value<'a>>)>,
        'a: 'b,
    {
        Context(std::cell::UnsafeCell::new(
            i.map(|x| (x.0.clone(), x.1.clone())).collect(),
        ))
    }

    fn append<'b>(&'b self, name: UniqueName, value: Rc<Value<'a>>) -> Guard<'a, 'b> {
        let map = unsafe { &mut *self.0.get() };
        map.insert(name.clone(), value.clone());
        Guard(self, vec![name])
    }
}

impl<'a, 'b> Drop for Guard<'a, 'b> {
    fn drop(&mut self) {
        let map = unsafe { &mut *self.0 .0.get() };
        for name in self.1.iter() {
            map.remove(name);
        }
    }
}

fn evaluate<'a, 'b>(ctx: &'b Context<'a>, term: &'a CapAvoidTerm) -> Rc<Value<'a>>
where
    'a: 'b,
{
    match term {
        CapAvoidTerm::Var(name) => ctx.get(name).unwrap(),
        CapAvoidTerm::Lam(name, body) => {
            let closure = ctx.to_closure();
            Rc::new(Value::Lam(name.clone(), closure, body.as_ref()))
        }
        CapAvoidTerm::App(lhs, rhs) => {
            let lhs = evaluate(ctx, lhs);
            let rhs = evaluate(ctx, rhs);
            match lhs.as_ref() {
                Value::Lam(x, closure, body) => {
                    let ctx = Context::from_closure(closure.iter());
                    let _guard = ctx.append(x.clone(), rhs);
                    evaluate(&ctx, body)
                }
                _ => Rc::new(Value::App(lhs, rhs)),
            }
        }
        CapAvoidTerm::Let(x, y, z) => {
            let value = evaluate(ctx, y);
            let _guard = ctx.append(x.clone(), value);
            evaluate(ctx, z)
        }
    }
}

fn eval(term: &CapAvoidTerm) -> Rc<Value> {
    let ctx = Context::new();
    evaluate(&ctx, term)
}

fn qoute(val: &Value) -> Box<CapAvoidTerm> {
    match val {
        Value::Var(x) => Box::new(CapAvoidTerm::Var(x.clone())),
        Value::App(lhs, rhs) => {
            let lhs = qoute(lhs);
            let rhs = qoute(rhs);
            Box::new(CapAvoidTerm::App(lhs, rhs))
        }
        Value::Lam(x, y, z) => {
            let ctx = Context::from_closure(y.iter());
            let fresh = UniqueName::new(x.0.as_ref());
            let _guard = ctx.append(x.clone(), Rc::new(Value::Var(fresh.clone())));
            Box::new(CapAvoidTerm::Lam(fresh, qoute(&evaluate(&ctx, z))))
        }
    }
}

fn main() {
    let src = r#"
        (let I = λ x . x in (
            let K = λ x . λ y . x in (
                let S = λ x . λ y . λ z . ((x z) (y z)) in (
                    ((S I) I) S
                )
            )
        ))
    "#;
    let tree = parse_tree(src);
    let catree = to_capture_avoidance_term(&tree);
    let vtree = eval(&catree);
    let nf = qoute(&vtree);
    println!("{}", tree);
    println!("{}", catree);
    println!("{:?}", vtree);
    println!("{}", nf);
}
