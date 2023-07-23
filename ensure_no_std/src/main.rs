#![feature(start)]

#![deny(warnings)]

#![no_std]

#[cfg(windows)]
#[link(name="msvcrt")]
extern { }

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    exit_no_std::exit(99)
}

use enum_derive_2018::IterVariants;
use macro_attr_2018::macro_attr;

macro_attr! {
    #[derive(IterVariants!(XVariants), Eq, PartialEq, Debug)]
    enum X { A, B, C, D }
}

#[start]
pub fn main(_argc: isize, _argv: *const *const u8) -> isize {
    let mut variants = X::iter_variants();
    assert_eq!(variants.next(), Some(X::A));
    assert_eq!(variants.next(), Some(X::B));
    assert_eq!(variants.next(), Some(X::C));
    assert_eq!(variants.next(), Some(X::D));
    assert_eq!(variants.next(), None);
    0
}
