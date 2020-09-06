// Copyright (c) 2015 macro-attr contributors.
// Copyright (c) 2020 Warlock <internalmike@gmail.com>.
//
// Licensed under the MIT license (see LICENSE or <http://opensource.org
// /licenses/MIT>) or the Apache License, Version 2.0 (see LICENSE of
// <http://www.apache.org/licenses/LICENSE-2.0>), at your option. All
// files in the project carrying such notice may not be copied, modified,
// or distributed except according to those terms.

use enum_derive_2018::EnumDisplay;
use macro_attr_2018::macro_attr;

macro_attr! {
    #[derive(EnumDisplay!)]
    pub enum Get {
        Up,
        /// And
        Down,
        /** And */
        AllAround
    }
}

macro_attr! {
    #[derive(EnumDisplay!)]
    pub enum Degenerate {}
}

#[test]
fn test_next_variant() {
    assert_eq!(format!("{}", Get::Up), "Up");
    assert_eq!(format!("{}", Get::Down), "Down");
    assert_eq!(format!("{}", Get::AllAround), "AllAround");
}
