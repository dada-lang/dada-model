use crate::{dada_lang::term, type_system::check_program};

/// Check what happens when we encounter a bad class name in a function parameter.
#[test]
fn empty_method() {
    expect_test::expect![[r#"
        Ok(
            (),
        )
    "#]]
    .assert_debug_eq(&check_program(&term(
        "
        class TheClass {
            fn empty_method(my self) {}
        }
    ",
    )));
}

/// Check what happens when we encounter a bad class name in a function parameter.
#[test]
fn bad_int_return_value() {
    expect_test::expect![[r#"
        Err(
            Error {
                context: "check program `class TheClass { fn empty_method (Some(my self)) -> Int { } }`",
                source: Error {
                    context: "check class named `TheClass`",
                    source: Error {
                        context: "check method named `empty_method`",
                        source: Error {
                            context: "check function body",
                            source: "type check for fn body failed",
                        },
                    },
                },
            },
        )
    "#]]
    .assert_debug_eq(&check_program(&term(
        "
        class TheClass {
            fn empty_method(my self) -> Int {}
        }
    ",
    )));
}

/// Check what happens when we encounter a bad class name in a function parameter.
#[test]
fn good_int_return_value() {
    expect_test::expect![[r#"
        Ok(
            (),
        )
    "#]]
    .assert_debug_eq(&check_program(&term(
        "
        class TheClass {
            fn empty_method(my self) -> Int {
                22;
            }
        }
    ",
    )));
}
