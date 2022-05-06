// Copyright (c) 2015 macro-attr contributors.
// Copyright (c) 2020 Warlock <internalmike@gmail.com>.
//
// Licensed under the MIT license (see LICENSE or <http://opensource.org
// /licenses/MIT>) or the Apache License, Version 2.0 (see LICENSE of
// <http://www.apache.org/licenses/LICENSE-2.0>), at your option. All
// files in the project carrying such notice may not be copied, modified,
// or distributed except according to those terms.

#![deny(warnings)]
#![doc(test(attr(deny(warnings))))]
#![doc(test(attr(allow(dead_code))))]
#![doc(test(attr(allow(unused_variables))))]
#![doc(test(attr(allow(unused_macros))))]

//! This crate provides several macros for deriving some useful methods for unitary enums
//! (*i.e.* enums where variants do not have payloads) and unary enums.
//!
//! **Crate features**
//!
//! * `"std"`
//! Enabled by default. Disable to make the library `#![no_std]`.
//!
//! ## Using with and without `macro_attr!`
//!
//! All of the macros are designed to be used with the
//! [`macro-attr-2018`](https://crates.io/crates/macro-attr-2018) crate,
//! though they can be used independent of it. The following:
//! ```rust
//! # use macro_attr_2018::macro_attr;
//! # use enum_derive_2018::IterVariants;
//! macro_attr! {
//!     #[derive(Copy, Clone, Debug, IterVariants!(Vars))]
//!     enum ItAintRight { BabeNo, NoNo, BoyBoy }
//! }
//! # fn main() {}
//! ```
//! can also be written as
//! ```rust
//! # use macro_attr_2018::macro_attr;
//! # use enum_derive_2018::IterVariants;
//! #[derive(Copy, Clone, Debug)]
//! enum ItAintRight { BabeNo, NoNo, BoyBoy }
//!
//! IterVariants! { (Vars) enum ItAintRight { BabeNo, NoNo, BoyBoy } }
//! # fn main() {}
//! ```

#![cfg_attr(not(feature = "std"), no_std)]
#[cfg(feature = "std")]
extern crate core;

#[doc(hidden)]
pub use core::convert::From as std_convert_From;
#[doc(hidden)]
pub use core::fmt::Display as std_fmt_Display;
#[doc(hidden)]
pub use core::fmt::Formatter as std_fmt_Formatter;
#[doc(hidden)]
pub use core::fmt::Result as std_fmt_Result;
#[doc(hidden)]
pub use core::iter::ExactSizeIterator as std_iter_ExactSizeIterator;
#[doc(hidden)]
pub use core::iter::Iterator as std_iter_Iterator;
#[doc(hidden)]
pub use core::mem::replace as std_mem_replace;
#[doc(hidden)]
pub use core::option::Option as std_option_Option;
#[doc(hidden)]
pub use core::result::Result as std_result_Result;
#[doc(hidden)]
pub use core::str::FromStr as std_str_FromStr;

#[doc(hidden)]
#[macro_export]
macro_rules! enum_derive_util {
    (@as_expr $e:expr) => {$e};
    (@as_item $($i:item)+) => {$($i)+};
    (@first_expr $head:expr $(, $($($tail:expr),+ $(,)?)?)?) => {$head};

    (
        @collect_unitary_variants ($callback:path { $($args:tt)* }),
        ($(,)*) -> ($($var_names:ident,)*)
    ) => {
        $crate::enum_derive_util! {
            @as_item
            $callback!{ $($args)* ($($var_names),*) }
        }
    };

    (
        @collect_unitary_variants $fixed:tt,
        (#[$_attr:meta] $($tail:tt)*) -> ($($var_names:tt)*)
    ) => {
        $crate::enum_derive_util! {
            @collect_unitary_variants $fixed,
            ($($tail)*) -> ($($var_names)*)
        }
    };

    (
        @collect_unitary_variants $fixed:tt,
        ($var:ident $(= $_val:expr)*, $($tail:tt)*) -> ($($var_names:tt)*)
    ) => {
        $crate::enum_derive_util! {
            @collect_unitary_variants $fixed,
            ($($tail)*) -> ($($var_names)* $var,)
        }
    };

    (
        @collect_unitary_variants ($name:ident),
        ($var:ident $_struct:tt, $($tail:tt)*) -> ($($var_names:tt)*)
    ) => {
        const _error: () = "cannot parse unitary variants from enum with non-unitary variants";
    };

    (
        @collect_unary_variants ($callback:path { $($args:tt)* }),
        ($(,)*) -> ($($out:tt)*)
    ) => {
        $crate::enum_derive_util! {
            @as_item
            $callback!{ $($args)* ($($out)*) }
        }
    };

    (
        @collect_unary_variants $fixed:tt,
        (#[$_attr:meta] $($tail:tt)*) -> ($($out:tt)*)
    ) => {
        $crate::enum_derive_util! {
            @collect_unary_variants $fixed,
            ($($tail)*) -> ($($out)*)
        }
    };

    (
        @collect_unary_variants $fixed:tt,
        ($var_name:ident($vis:vis $var_ty:ty), $($tail:tt)*) -> ($($out:tt)*)
    ) => {
        $crate::enum_derive_util! {
            @collect_unary_variants $fixed,
            ($($tail)*) -> ($($out)* $var_name($var_ty),)
        }
    };

    (
        @collect_unary_variants ($name:ident),
        ($var:ident $_struct:tt, $($tail:tt)*) -> ($($_out:tt)*)
    ) => {
        const _error: () = "cannot parse unary variants from enum with non-unary tuple variants";
    };
}

/// Derives `iter_variants()` for an unitary enum, which returns an iterator over the variants of the enum in lexical order.
///  
/// The argument is the name of the iterator type that will be generated:
/// ```rust
/// # use macro_attr_2018::macro_attr;
/// # use enum_derive_2018::IterVariants;
/// macro_attr! {
///     #[derive(IterVariants!(GetVariants))]
///     pub enum Get { Up, Down, AllAround }
/// }
/// # fn main() {}
/// ```
///
/// Neither macro imposes any naming requirements, save the obvious:
/// the name must not conflict with any other types.
#[macro_export]
macro_rules! IterVariants {
    (($itername:ident) $vis:vis enum $name:ident { $($body:tt)* }) => {
        $crate::enum_derive_util! {
            @collect_unitary_variants
            ($crate::IterVariants_impl { @expand ($vis) $itername, $name }),
            ($($body)*,) -> ()
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! IterVariants_impl {
    (
        @expand ($vis:vis) $itername:ident, $name:ident ()
    ) => {
        $crate::enum_derive_util! { @as_item $vis struct $itername; }

        impl $crate::std_iter_Iterator for $itername {
            type Item = $name;
            fn next(&mut self) -> $crate::std_option_Option<Self::Item> {
                None
            }

            fn size_hint(&self) -> (usize, $crate::std_option_Option<usize>) {
                (0, Some(0))
            }
        }

        impl $crate::std_iter_ExactSizeIterator for $itername { }

        $crate::enum_derive_util! {
            @as_item
            impl $name {
                #[allow(dead_code)]
                $vis fn iter_variants() -> $itername {
                    $itername
                }
            }
        }
    };

    (
        @expand ($vis:vis) $itername:ident, $name:ident ($($var_names:ident),*)
    ) => {
        $crate::enum_derive_util! { @as_item $vis struct $itername($crate::std_option_Option<$name>); }

        $crate::IterVariants_impl! { @iter ($itername, $name), ($($var_names,)*) -> () () (0usize) }

        $crate::enum_derive_util! {
            @as_item
            impl $name {
                #[allow(dead_code)]
                $vis fn iter_variants() -> $itername {
                    $itername($crate::std_option_Option::Some($crate::enum_derive_util!(@first_expr $($name::$var_names),+)))
                }
            }
        }
    };

    (
        @iter ($itername:ident, $name:ident), () -> ($($next_body:tt)*) ($($size_body:tt)*) ($($count:tt)*)
    ) => {
        $crate::enum_derive_util! {
            @as_item
            impl $crate::std_iter_Iterator for $itername {
                type Item = $name;
                fn next(&mut self) -> $crate::std_option_Option<Self::Item> {
                    let next_item = match self.0 {
                        $($next_body)*
                        $crate::std_option_Option::None => $crate::std_option_Option::None
                    };
                    $crate::std_mem_replace(&mut self.0, next_item)
                }

                fn size_hint(&self) -> (usize, $crate::std_option_Option<usize>) {
                    let variants = $($count)*;
                    let progress = match self.0 {
                        $($size_body)*
                        $crate::std_option_Option::None => variants
                    };
                    (variants - progress, $crate::std_option_Option::Some(variants - progress))
                }
            }

            impl $crate::std_iter_ExactSizeIterator for $itername { }
        }
    };

    (
        @iter ($itername:ident, $name:ident), ($a:ident, $b:ident, $($rest:tt)*) -> ($($next_body:tt)*) ($($size_body:tt)*) ($($count:tt)*)
    ) => {
        $crate::IterVariants_impl! {
            @iter ($itername, $name), ($b, $($rest)*)
            -> (
                $($next_body)*
                $crate::std_option_Option::Some($name::$a) => $crate::std_option_Option::Some($name::$b),
            )
            (
                $($size_body)*
                $crate::std_option_Option::Some($name::$a) => $($count)*,
            )
            ($($count)* + 1usize)
        }
    };

    (
        @iter ($itername:ident, $name:ident), ($a:ident,) -> ($($next_body:tt)*) ($($size_body:tt)*) ($($count:tt)*)
    ) => {
        $crate::IterVariants_impl! {
            @iter ($itername, $name), ()
            -> (
                $($next_body)*
                $crate::std_option_Option::Some($name::$a) => $crate::std_option_Option::None,
            )
            (
                $($size_body)*
                $crate::std_option_Option::Some($name::$a) => $($count)*,
            )
            ($($count)* + 1usize)
        }
    };
}

/// Derives `iter_variant_names()` for an unitary enum,
/// which returns an iterator over the string names of the variants of the enum in lexical order.
///  
/// The argument is the name of the iterator type that will be generated:
/// ```rust
/// # use macro_attr_2018::macro_attr;
/// # use enum_derive_2018::IterVariantNames;
/// macro_attr! {
///     #[derive(IterVariantNames!(GetVariantNames))]
///     pub enum Get { Up, Down, AllAround }
/// }
/// # fn main() {}
/// ```
///
/// Neither macro imposes any naming requirements, save the obvious:
/// the name must not conflict with any other types.
#[macro_export]
macro_rules! IterVariantNames {
    (($itername:ident) $vis:vis enum $name:ident { $($body:tt)* }) => {
        $crate::enum_derive_util! {
            @collect_unitary_variants
            ($crate::IterVariantNames_impl { @expand ($vis) $itername, $name }),
            ($($body)*,) -> ()
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! IterVariantNames_impl {
    (
        @expand ($vis:vis) $itername:ident, $name:ident ()
    ) => {
        $crate::enum_derive_util! { @as_item $vis struct $itername; }

        impl $crate::std_iter_Iterator for $itername {
            type Item = &'static str;
            fn next(&mut self) -> $crate::std_option_Option<Self::Item> {
                $crate::std_option_Option::None
            }

            fn size_hint(&self) -> (usize, $crate::std_option_Option<usize>) {
                (0, $crate::std_option_Option::Some(0))
            }
        }

        impl $crate::std_iter_ExactSizeIterator for $itername { }

        $crate::enum_derive_util! {
            @as_item
            impl $name {
                #[allow(dead_code)]
                $vis fn iter_variant_names() -> $itername {
                    $itername
                }
            }
        }
    };

    (
        @expand ($vis:vis) $itername:ident, $name:ident ($($var_names:ident),*)
    ) => {
        $crate::enum_derive_util! { @as_item $vis struct $itername($crate::std_option_Option<$name>); }

        $crate::IterVariantNames_impl! { @iter ($itername, $name), ($($var_names,)*) -> () () (0usize) }

        $crate::enum_derive_util! {
            @as_item
            impl $name {
                #[allow(dead_code)]
                $vis fn iter_variant_names() -> $itername {
                    $itername($crate::std_option_Option::Some($crate::enum_derive_util!(@first_expr $($name::$var_names),+)))
                }
            }
        }
    };

    (
        @iter ($itername:ident, $name:ident), () -> ($($next_body:tt)*) ($($size_body:tt)*) ($($count:tt)*)
    ) => {
        $crate::enum_derive_util! {
            @as_item
            impl $crate::std_iter_Iterator for $itername {
                type Item = &'static str;
                fn next(&mut self) -> $crate::std_option_Option<Self::Item> {
                    let (next_state, result) = match self.0 {
                        $($next_body)*
                        $crate::std_option_Option::None => ($crate::std_option_Option::None, $crate::std_option_Option::None)
                    };
                    self.0 = next_state;
                    result
                }

                fn size_hint(&self) -> (usize, $crate::std_option_Option<usize>) {
                    let variants = $($count)*;
                    let progress = match self.0 {
                        $($size_body)*
                        None => variants
                    };
                    (variants - progress, $crate::std_option_Option::Some(variants - progress))
                }
            }

            impl $crate::std_iter_ExactSizeIterator for $itername { }
        }
    };

    (
        @iter ($itername:ident, $name:ident), ($a:ident, $b:ident, $($rest:tt)*) -> ($($next_body:tt)*) ($($size_body:tt)*) ($($count:tt)*)
    ) => {
        $crate::IterVariantNames_impl! {
            @iter ($itername, $name), ($b, $($rest)*)
            -> (
                $($next_body)*
                $crate::std_option_Option::Some($name::$a)
                    => ($crate::std_option_Option::Some($name::$b), $crate::std_option_Option::Some(stringify!($a))),
            )
            (
                $($size_body)*
                $crate::std_option_Option::Some($name::$a) => $($count)*,
            )
            ($($count)* + 1usize)
        }
    };

    (
        @iter ($itername:ident, $name:ident), ($a:ident,) -> ($($next_body:tt)*) ($($size_body:tt)*) ($($count:tt)*)
    ) => {
        $crate::IterVariantNames_impl! {
            @iter ($itername, $name), ()
            -> (
                $($next_body)*
                $crate::std_option_Option::Some($name::$a)
                    => ($crate::std_option_Option::None, $crate::std_option_Option::Some(stringify!($a))),
            )
            (
                $($size_body)*
                $crate::std_option_Option::Some($name::$a) => $($count)*,
            )
            ($($count)* + 1usize)
        }
    };
}

/// Derives `next_variant(&self)` for an unitary enum,
/// which returns the next variant, or `None` when called for the last.
#[macro_export]
macro_rules! NextVariant {
    (() $vis:vis enum $name:ident { $($body:tt)* }) => {
        $crate::enum_derive_util! {
            @collect_unitary_variants
            ($crate::NextVariant_impl { @expand ($vis) $name }),
            ($($body)*,) -> ()
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! NextVariant_impl {
    (
        @expand ($vis:vis) $name:ident ()
    ) => {
        $crate::enum_derive_util! {
            @as_item
            impl $name {
                #[allow(dead_code)]
                $vis fn next_variant(&self) -> $crate::std_option_Option<$name> {
                    loop {} // unreachable
                }
            }
        }
    };

    (
        @expand ($vis:vis) $name:ident ($($var_names:ident),*)
    ) => {
        $crate::enum_derive_util! {
            @as_item
            impl $name {
                #[allow(dead_code)]
                $vis fn next_variant(&self) -> $crate::std_option_Option<$name> {
                    $crate::NextVariant_impl!(@arms ($name, self), ($($var_names)*) -> ())
                }
            }
        }
    };

    (
        @arms ($name:ident, $self_:expr), ($a:ident) -> ($($body:tt)*)
    ) => {
        $crate::enum_derive_util! {
            @as_expr
            match *$self_ {
                $($body)*
                $name::$a => $crate::std_option_Option::None
            }
        }
    };

    (
        @arms ($name:ident, $self_:expr), ($a:ident $b:ident $($rest:tt)*) -> ($($body:tt)*)
    ) => {
        $crate::NextVariant_impl! {
            @arms ($name, $self_), ($b $($rest)*)
            -> (
                $($body)*
                $name::$a => $crate::std_option_Option::Some($name::$b),
            )
        }
    };
}

/// Derives `prev_variant(&self)` for an unitary enum, which returns the previous variant, or `None` when called for the first.
#[macro_export]
macro_rules! PrevVariant {
    (() $vis:vis enum $name:ident { $($body:tt)* }) => {
        $crate::enum_derive_util! {
            @collect_unitary_variants
            ($crate::PrevVariant_impl { @expand ($vis) $name }),
            ($($body)*,) -> ()
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! PrevVariant_impl {
    (
        @expand ($vis:vis) $name:ident ()
    ) => {
        $crate::enum_derive_util! {
            @as_item
            impl $name {
                #[allow(dead_code)]
                $vis fn prev_variant(&self) -> $crate::std_option_Option<$name> {
                    loop {} // unreachable
                }
            }
        }
    };

    (
        @expand ($vis:vis) $name:ident ($($var_names:ident),*)
    ) => {
        $crate::enum_derive_util! {
            @as_item
            impl $name {
                #[allow(dead_code)]
                $vis fn prev_variant(&self) -> $crate::std_option_Option<$name> {
                    $crate::PrevVariant_impl!(@arms ($name, self), ($crate::std_option_Option::None, $($var_names)*) -> ())
                }
            }
        }
    };

    (
        @arms ($name:ident, $self_:expr), ($prev:expr, $a:ident) -> ($($body:tt)*)
    ) => {
        $crate::enum_derive_util! {
            @as_expr
            match *$self_ {
                $($body)*
                $name::$a => $prev
            }
        }
    };

    (
        @arms ($name:ident, $self_:expr), ($prev:expr, $a:ident $($rest:tt)*) -> ($($body:tt)*)
    ) => {
        $crate::PrevVariant_impl! {
            @arms ($name, $self_), ($crate::std_option_Option::Some($name::$a), $($rest)*)
            -> (
                $($body)*
                $name::$a => $prev,
            )
        }
    };
}

/// Derives [`Display`](core::fmt::Display) for an unitary enum, which outputs the name of the variant.
///
/// Note that this is identical to the behaviour of a derived [`Debug`](core::fmt::Debug) implementation.
#[macro_export]
macro_rules! EnumDisplay {
    (() $vis:vis enum $name:ident { $($body:tt)* }) => {
        $crate::enum_derive_util! {
            @collect_unitary_variants
            ($crate::EnumDisplay_impl { @expand $name }),
            ($($body)*,) -> ()
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! EnumDisplay_impl {
    (
        @expand $name:ident ()
    ) => {
        $crate::enum_derive_util! {
            @as_item
            impl $crate::std_fmt_Display for $name {
                fn fmt(&self, _: &mut $crate::std_fmt_Formatter) -> $crate::std_fmt_Result {
                    loop {} // unreachable
                }
            }
        }
    };

    (
        @expand $name:ident ($($var_names:ident),*)
    ) => {
        $crate::enum_derive_util! {
            @as_item
            impl $crate::std_fmt_Display for $name {
                fn fmt(&self, f: &mut $crate::std_fmt_Formatter) -> $crate::std_fmt_Result {
                    $crate::EnumDisplay_impl!(@arms ($name, self, f), ($($var_names)*) -> ())
                }
            }
        }
    };

    (
        @arms ($name:ident, $self_:expr, $f:ident), ($a:ident) -> ($($body:tt)*)
    ) => {
        $crate::enum_derive_util! {
            @as_expr
            match *$self_ {
                $($body)*
                $name::$a => write!($f, stringify!($a)),
            }
        }
    };

    (
        @arms ($name:ident, $self_:expr, $f:ident), ($a:ident $b:ident $($rest:tt)*) -> ($($body:tt)*)
    ) => {
        $crate::EnumDisplay_impl! {
            @arms ($name, $self_, $f), ($b $($rest)*)
            -> (
                $($body)*
                $name::$a => write!($f, stringify!($a)),
            )
        }
    };
}

/// Derives [`FromStr`](core::str::FromStr) for an unitary enum. It requires an exact match of the variant name.
#[macro_export]
macro_rules! EnumFromStr {
    (() $vis:vis enum $name:ident { $($body:tt)* }) => {
        $crate::enum_derive_util! {
            @collect_unitary_variants
            ($crate::EnumFromStr_impl { @expand ($vis) $name }),
            ($($body)*,) -> ()
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! EnumFromStr_impl {
    (
        @expand ($vis:vis) $name:ident ()
    ) => {
        $crate::enum_derive_util! {
            @as_item
            impl $crate::std_str_FromStr for $name {
                type Err = $crate::ParseEnumError;

                fn from_str(_: &str) -> $crate::std_result_Result<Self, Self::Err> {
                    $crate::std_result_Result::Err($crate::ParseEnumError)
                }
            }
        }
    };

    (
        @expand ($vis:vis) $name:ident ($($var_names:ident),*)
    ) => {
        $crate::enum_derive_util! {
            @as_item
            impl $crate::std_str_FromStr for $name {
                type Err = $crate::ParseEnumError;

                fn from_str(s: &str) -> Result<Self, Self::Err> {
                    $crate::EnumFromStr_impl!(@arms ($name, s), ($($var_names)*) -> ())
                }
            }
        }
    };

    (
        @arms ($name:ident, $s:ident), ($a:ident) -> ($($body:tt)*)
    ) => {
        $crate::enum_derive_util! {
            @as_expr
            match $s {
                $($body)*
                stringify!($a) => $crate::std_result_Result::Ok($name::$a),
                _ => $crate::std_result_Result::Err($crate::ParseEnumError)
            }
        }
    };

    (
        @arms ($name:ident, $s:ident), ($a:ident $b:ident $($rest:tt)*) -> ($($body:tt)*)
    ) => {
        $crate::EnumFromStr_impl! {
            @arms ($name, $s), ($b $($rest)*)
            -> (
                $($body)*
                stringify!($a) => $crate::std_result_Result::Ok($name::$a),
            )
        }
    };
}

/// The `FromStr` [derived implementations](EnumFromStr) error type.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseEnumError;

impl core::fmt::Display for ParseEnumError {
    fn fmt(&self, fmt: &mut core::fmt::Formatter) -> Result<(), core::fmt::Error> {
        write!(fmt, "provided string did not match any enum variant")
    }
}

#[cfg(feature="std")]
impl std::error::Error for ParseEnumError { }

/// Derives [`From<T>`](core::convert::From) for each variant's payload,
/// assuming all variants are unary.
#[macro_export]
macro_rules! EnumFromInner {
    (() $vis:vis enum $name:ident { $($body:tt)* }) => {
        $crate::enum_derive_util! {
            @collect_unary_variants
            ($crate::EnumFromInner_impl { @expand $name }),
            ($($body)*,) -> ()
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! EnumFromInner_impl {
    (
        @expand $name:ident ($($var_names:ident($var_tys:ty),)*)
    ) => {
        $(
            impl $crate::std_convert_From<$var_tys> for $name {
                fn from(v: $var_tys) -> $name {
                    $name::$var_names(v)
                }
            }
        )*
    };
}

/// Derives a method for an unary enum returning a borrowed pointer to the inner value, cast to a trait object.
///
/// `EnumInnerAsTrait!` accepts a single deriving form that specifies the name of the method to be derived,
/// whether the borrow should be mutable, and the trait of interest.
/// For example:
/// ```rust
/// # use macro_attr_2018::macro_attr;
/// # use enum_derive_2018::EnumInnerAsTrait;
/// macro_attr! {
///     #[derive(EnumInnerAsTrait!(pub as_display -> &dyn std::fmt::Display))]
///     enum Value {
///         U32(u32),
///         U64(u64),
///     }
/// }
///
/// # fn main() {
/// let s = format!("{}", Value::U64(42).as_display());
/// assert_eq!(&s[..], "42");
/// # }
/// ```
#[macro_export]
macro_rules! EnumInnerAsTrait {
    ($arg:tt $vis:vis enum $name:ident { $($body:tt)* }) => {
        $crate::enum_derive_util! {
            @collect_unary_variants
            ($crate::EnumInnerAsTrait_impl { @expand $arg, $name, }),
            ($($body)*,) -> ()
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! EnumInnerAsTrait_impl {
    (
        @expand ($vis:vis $fn_name:ident -> &mut $tr:ty), $($tail:tt)*
    ) => {
        $crate::EnumInnerAsTrait_impl! { @expand_inner ($vis), $fn_name, (mut), $tr, $($tail)* }
    };

    (
        @expand ($vis:vis $fn_name:ident -> &$tr:ty), $($tail:tt)*
    ) => {
        $crate::EnumInnerAsTrait_impl! { @expand_inner ($vis), $fn_name, (), $tr, $($tail)* }
    };

    (
        @expand_inner
        ($vis:vis), $fn_name:ident, (mut), $tr:ty,
        $ty_name:ident,
        ($($var_names:ident($_var_tys:ty),)*)
    ) => {
        $crate::enum_derive_util! {
            @as_item
            impl $ty_name {
                $vis fn $fn_name(&mut self) -> &mut $tr {
                    match *self {
                        $(
                            $ty_name::$var_names(ref mut v) => v as &mut $tr,
                        )*
                    }
                }
            }
        }
    };

    (
        @expand_inner
        ($vis:vis), $fn_name:ident, (), $tr:ty,
        $ty_name:ident,
        ($($var_names:ident($_var_tys:ty),)*)
    ) => {
        $crate::enum_derive_util! {
            @as_item
            impl $ty_name {
                $vis fn $fn_name(&self) -> &$tr {
                    match *self {
                        $(
                            $ty_name::$var_names(ref v) => v as &$tr,
                        )*
                    }
                }
            }
        }
    };
}
