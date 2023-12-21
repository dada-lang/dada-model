use crate::{dada_lang::term, type_system::check_program};
use formality_core::test;

/// Check we are able to type check an empty method.
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

/// Check that empty blocks return unit (and that is not assignable to Int)
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

/// Check returning an integer with return type of Int.
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

/// Check returning an instance of a class.
#[test]
#[allow(non_snake_case)]
fn return_instance_of_Foo() {
    expect_test::expect![[r#"
        Ok(
            (),
        )
    "#]]
    .assert_debug_eq(&check_program(&term(
        "
        class Foo { }

        class TheClass {
            fn empty_method(my self) -> Foo {
                new Foo();
            }
        }
    ",
    )));
}

/// Check returning an instance of a class.
#[test]
#[allow(non_snake_case)]
fn return_from_variable() {
    expect_test::expect![[r#"
        Ok(
            (),
        )
    "#]]
    .assert_debug_eq(&check_program(&term(
        "
        class Foo { }

        class TheClass {
            fn empty_method(my self) -> Foo {
                let foo = new Foo();
                give foo;
            }
        }
    ",
    )));
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn return_shared_not_give() {
    expect_test::expect![[r#"
        Err(
            Error {
                context: "check program `class Foo { } class TheClass { fn empty_method (Some(my self)) -> Foo { let foo = new Foo () ; foo ; } }`",
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
        class Foo { }

        class TheClass {
            fn empty_method(my self) -> Foo {
                let foo = new Foo();
                share foo;
            }
        }
    ",
    )));
}
