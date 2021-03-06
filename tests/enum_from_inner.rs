// Copyright (c) 2015 macro-attr contributors.
// Copyright (c) 2020 Warlock <internalmike@gmail.com>.
//
// Licensed under the MIT license (see LICENSE or <http://opensource.org
// /licenses/MIT>) or the Apache License, Version 2.0 (see LICENSE of
// <http://www.apache.org/licenses/LICENSE-2.0>), at your option. All
// files in the project carrying such notice may not be copied, modified,
// or distributed except according to those terms.

use enum_derive_2018::EnumFromInner;
use macro_attr_2018::macro_attr;

macro_attr! {
    #[derive(Debug, PartialEq, EnumFromInner!)]
    pub enum Value {
        Unit(()),
        Int(i64),
        Str(&'static str),
    }
}

macro_attr! {
    #[derive(Debug, PartialEq, EnumFromInner!)]
    pub enum Degenerate {}
}

#[test]
fn test_from_inner() {
    assert_eq!(Into::<Value>::into(()), Value::Unit(()));
    assert_eq!(Into::<Value>::into(42i64), Value::Int(42));
    assert_eq!(Into::<Value>::into("fry"), Value::Str("fry"));

    assert_eq!({ let v: Value = From::from(()); v }, Value::Unit(()));
    assert_eq!({ let v: Value = From::from(42i64); v }, Value::Int(42));
    assert_eq!({ let v: Value = From::from("fry"); v }, Value::Str("fry"));
}
