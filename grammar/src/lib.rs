#![feature(option_result_contains)]

macro_rules! assert_unreachable {
    () => {
        assert_unreachable!("entered unreachable code")
    };
    ($e:expr) => {
        if cfg!(debug_assertions) {
            panic!($e)
        } else {
            unsafe { core::hint::unreachable_unchecked() }
        }
    };
}

pub mod lexical;
pub mod syntactic;
