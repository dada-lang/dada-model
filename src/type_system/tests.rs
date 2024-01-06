use crate::dada_lang::term;
use formality_core::test;

use super::check_program;

mod fn_calls;
mod move_check;
mod move_tracking;
mod permission_check;
mod type_check;

/// Check what happens when we encounter a bad class name in a function parameter.
#[test]
fn bad_class_name_in_fn_parameter() {
    expect_test::expect![[r#"
        Err(
            Error {
                context: "check program `class OtherClass { fn no_such_class (c : given TypeName) -> () { } }`",
                source: Error {
                    context: "check class named `OtherClass`",
                    source: Error {
                        context: "check method named `no_such_class`",
                        source: Error {
                            context: "check type `given TypeName`",
                            source: Error {
                                context: "check_perm(given",
                                source: "permision requires at lease one place",
                            },
                        },
                    },
                },
            },
        )
    "#]]
    .assert_debug_eq(&check_program(&term(
        "
        class OtherClass {
            fn no_such_class(c: given TypeName) -> () {}
        }
    ",
    )));
}

/// Check what happens when we encounter a bad class name in a function parameter.
#[test]
fn ok_field_name_in_fn_parameter() {
    expect_test::expect![[r#"
        Err(
            Error {
                context: "check program `class Point { x : shared Int ; y : shared Int ; fn no_such_class (c : given Point, x : shared (c . x) Int, y : shared (c . y) Int) -> () { } }`",
                source: Error {
                    context: "check class named `Point`",
                    source: Error {
                        context: "check method named `no_such_class`",
                        source: Error {
                            context: "check type `given Point`",
                            source: Error {
                                context: "check_perm(given",
                                source: "permision requires at lease one place",
                            },
                        },
                    },
                },
            },
        )
    "#]]
    .assert_debug_eq(&check_program(&term(
        "
        class Point { 
            x: shared Int;
            y: shared Int;

            fn no_such_class(
                c: given Point, 
                x: shared(c.x) Int, 
                y: shared(c.y) Int,
            ) -> () {

            }
        }  
    ",
    )));
}

/// Check what happens when we encounter a bad class name in a function parameter.
#[test]
fn bad_field_name_in_fn_parameter() {
    expect_test::expect![[r#"
        Err(
            Error {
                context: "check program `class Point { x : shared Int ; y : shared Int ; fn no_such_class (c : given Point, x : shared (c . z) Int) -> () { } }`",
                source: Error {
                    context: "check class named `Point`",
                    source: Error {
                        context: "check method named `no_such_class`",
                        source: Error {
                            context: "check type `given Point`",
                            source: Error {
                                context: "check_perm(given",
                                source: "permision requires at lease one place",
                            },
                        },
                    },
                },
            },
        )
    "#]]
    .assert_debug_eq(&check_program(&term(
        "
        class Point {
            x: shared Int;
            y: shared Int;

            fn no_such_class(
                c: given Point, 
                x: shared(c.z) Int,
            ) -> () {}
        }
    ",
    )));
}
