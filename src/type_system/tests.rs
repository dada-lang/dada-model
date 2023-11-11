use crate::dada_lang::term;

use super::check_program;

/// Check what happens when we encounter a bad class name in a function parameter.
#[test]
fn bad_class_name_in_fn_parameter() {
    expect_test::expect![[r#"
        Err(
            Error {
                context: "check program `fn no_such_class (c : my ClassName) -> () { }`",
                source: Error {
                    context: "check function named `no_such_class`",
                    source: Error {
                        context: "check type `my ClassName`",
                        source: Error {
                            context: "check class name `ClassName`",
                            source: "no class named `ClassName`",
                        },
                    },
                },
            },
        )
    "#]]
    .assert_debug_eq(&check_program(&term(
        "
        fn no_such_class(c: my ClassName) -> () {}
    ",
    )));
}
