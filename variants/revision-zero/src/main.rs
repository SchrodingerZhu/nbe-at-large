#![feature(box_patterns)]
#![feature(associated_type_defaults)]
#![feature(if_let_guard)]
#![feature(let_chains)]
mod alpha_equality;
mod builtin;
mod equalization;
mod instantiation;
mod term;
mod typecheck;
mod whnf;

#[macro_export]
macro_rules! assert_unreachable {
    () => {
        assert_unreachable!("entered unreachable code")
    };
    ($($e:expr),*) => {
        if cfg!(debug_assertions) {
            panic!($($e),*)
        } else {
            unsafe { core::hint::unreachable_unchecked() }
        }
    };
}

fn main() {
    println!("Hello, world!");
}
