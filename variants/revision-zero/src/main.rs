#![feature(box_patterns)]
#![feature(associated_type_defaults)]
mod alpha_equality;
mod builtin;
mod instantiation;
mod term;
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
