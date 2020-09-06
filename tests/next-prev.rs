// Copyright (c) 2015 macro-attr contributors.
// Copyright (c) 2020 Warlock <internalmike@gmail.com>.
//
// Licensed under the MIT license (see LICENSE or <http://opensource.org
// /licenses/MIT>) or the Apache License, Version 2.0 (see LICENSE of
// <http://www.apache.org/licenses/LICENSE-2.0>), at your option. All
// files in the project carrying such notice may not be copied, modified,
// or distributed except according to those terms.

use enum_derive_2018::{NextVariant, PrevVariant};
use macro_attr_2018::macro_attr;

macro_attr! {
    #[derive(Debug, PartialEq, NextVariant!, PrevVariant!)]
    pub enum Get {
        Up,
        /// And
        Down,
        /** And */
        AllAround
    }
}

// We can't test this since it *literally* can't be called.
macro_attr! {
    #[derive(NextVariant!, PrevVariant!)]
    enum Nada {}
}

#[test]
fn test_next_variant() {
    assert_eq!(Get::Up.next_variant(),        Some(Get::Down));
    assert_eq!(Get::Down.next_variant(),      Some(Get::AllAround));
    assert_eq!(Get::AllAround.next_variant(), None);

    assert_eq!(Get::Up.prev_variant(),        None);
    assert_eq!(Get::Down.prev_variant(),      Some(Get::Up));
    assert_eq!(Get::AllAround.prev_variant(), Some(Get::Down));
}
