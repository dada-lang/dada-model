//! Tests for subpermissions.
//!
//! Perm P is a *subpermission* of perm Q when `P T` is a subtype of `Q T` for all types `T`.

use crate::{dada_lang::term, type_system::check_program};
use formality_core::{test, test_util::ResultTestExt};

#[test]
#[allow(non_snake_case)]
fn PermDataMy_is_subtype_of_PermDataMy() {
    check_program(&term(
        "
        class Data { }

        class PermData[perm P] {
            data: P Data;
        }

        class Main {
            fn test(my self, data: PermData[my]) {
                let m: PermData[my] = data.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn PermDataMy_is_subtype_of_PermDataOur() {
    check_program(&term(
        "
        class Data { }

        class PermData[perm P] {
            data: P Data;
        }

        class Main {
            fn test(my self, data: PermData[my]) {
                let m: PermData[our] = data.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn PermDataMy_is_not_subtype_of_PermDataLeased() {
    check_program(&term(
        "
        class Data { }

        class PermData[perm P] {
            data: P Data;
        }

        class Main {
            fn test(my self, data: PermData[my]) {
                let d = new Data();
                let m: PermData[leased{d}] = data.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn PermDataMy_is_not_subtype_of_PermDataShared() {
    check_program(&term(
        "
        class Data { }

        class PermData[perm P] {
            data: P Data;
        }

        class Main {
            fn test(my self, data: PermData[my]) {
                let d = new Data();
                let m: PermData[shared{d}] = data.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}
