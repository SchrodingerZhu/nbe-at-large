#![feature(box_patterns)]
mod builtin;
mod term;

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
