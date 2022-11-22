use std::rc::Rc;

use pest::{iterators::Pair, Parser};

type Name = String;

#[derive(Debug, Clone)]
enum Term {
    Var(Name),
    Lam(Name, Rc<Self>),
    App(Rc<Self>, Rc<Self>),
    Let(Name, Rc<Self>, Rc<Self>),
}

enum Value {
    Var(Name),
    App(Rc<Self>, Rc<Self>),
    Lam(Name, Box<dyn Fn(Rc<Self>) -> Rc<Self>>),
}

impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Var(arg0) => f.debug_tuple("Var").field(arg0).finish(),
            Self::App(arg0, arg1) => f.debug_tuple("App").field(arg0).field(arg1).finish(),
            Self::Lam(arg0, _) => f.debug_tuple("Lam").field(arg0).finish(),
        }
    }
}

#[derive(Debug)]
enum Env {
    Cons(Name, Rc<Value>, Rc<Self>),
    Nil,
}

impl Env {
    fn lookup(&self, key: &str) -> Option<Rc<Value>> {
        let mut iter = self;
        loop {
            match iter {
                Env::Cons(name, value, tail) => {
                    if name == key {
                        return Some(value.clone());
                    }
                    iter = tail.as_ref();
                }
                Env::Nil => return None,
            }
        }
    }
}

fn eval(env: Rc<Env>, term: &Term) -> Rc<Value> {
    match term {
        Term::Var(x) => env.lookup(x).unwrap(),
        Term::Lam(x, t) => {
            let t = t.clone();
            let name = x.clone();
            let closure = Box::new(move |x: Rc<Value>| {
                let env = Rc::new(Env::Cons(name.clone(), x, env.clone()));
                eval(env, t.as_ref())
            });
            Rc::new(Value::Lam(x.clone(), closure))
        }
        Term::App(t, u) => {
            let lhs = eval(env.clone(), t.as_ref());
            let rhs = eval(env.clone(), u.as_ref());
            if let Value::Lam(_, t) = lhs.as_ref() {
                t(rhs)
            } else {
                Rc::new(Value::App(lhs, rhs))
            }
        }
        Term::Let(x, t, u) => {
            let bound = eval(env.clone(), t.as_ref());
            let env = Rc::new(Env::Cons(x.clone(), bound, env));
            eval(env, u.as_ref())
        }
    }
}

enum NameList {
    Cons(Name, Rc<Self>),
    Nil,
}

impl NameList {
    fn contains(&self, key: &str) -> bool {
        let mut iter = self;
        loop {
            match iter {
                NameList::Cons(h, t) => {
                    if h == key {
                        return true;
                    }
                    iter = t.as_ref();
                }
                NameList::Nil => return false,
            }
        }
    }
}

fn quote(ns: Rc<NameList>, val: &Value) -> Rc<Term> {
    match val {
        Value::Var(x) => Rc::new(Term::Var(x.clone())),
        Value::App(t, u) => {
            let lhs = quote(ns.clone(), t.as_ref());
            let rhs = quote(ns.clone(), u.as_ref());
            Rc::new(Term::App(lhs, rhs))
        }
        Value::Lam(x, closure) => {
            let x = if x == "_" {
                "_".to_string()
            } else {
                let mut x = x.clone();
                while ns.contains(x.as_str()) {
                    x.push('\'');
                }
                x
            };
            let var = Rc::new(Value::Var(x.clone()));
            let evaluated = closure(var);
            let body = quote(Rc::new(NameList::Cons(x.clone(), ns)), &evaluated);
            Rc::new(Term::Lam(x, body))
        }
    }
}

#[derive(pest_derive::Parser)]
#[grammar = "syntax.pest"]
struct LambdaParser;

fn translate(x: Pair<Rule>) -> Rc<Term> {
    match x.as_rule() {
        Rule::expr => translate(x.into_inner().next().unwrap()),
        Rule::var => Rc::new(Term::Var(x.as_str().to_string())),
        Rule::let_expr => {
            let mut iter = x.into_inner();
            let var = iter.next().unwrap().as_str().to_string();
            let binding = translate(iter.next().unwrap());
            let body = translate(iter.next().unwrap());
            Rc::new(Term::Let(var, binding, body))
        }
        Rule::lambda_expr => {
            let mut iter = x.into_inner();
            let var = iter.next().unwrap().as_str().to_string();
            let body = translate(iter.next().unwrap());
            Rc::new(Term::Lam(var, body))
        }
        Rule::app_expr => {
            let mut iter = x.into_inner();
            let a = translate(iter.next().unwrap());
            let b = translate(iter.next().unwrap());
            Rc::new(Term::App(a, b))
        }
        _ => panic!("unexpected token"),
    }
}

fn main() {
    let src = "λ x . (let x = λ y . y in λ x . x x)";
    let parser = LambdaParser::parse(Rule::file, src)
        .unwrap()
        .next()
        .unwrap();
    let t = parser
        .into_inner()
        .filter_map(|x| match x.as_rule() {
            Rule::expr => Some(x),
            _ => None,
        })
        .next()
        .unwrap();
    let expr = translate(t);
    println!("{:?}", expr);
    let expr = eval(Rc::new(Env::Nil), &expr);
    let expr = quote(Rc::new(NameList::Nil), expr.as_ref());
    println!("{:?}", expr);
}
