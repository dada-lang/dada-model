use crate::{dada_lang::term, type_system::check_program};

/// Check what happens when we encounter a bad class name in a function parameter.
#[test]
fn empty_method() {
    expect_test::expect![[r#"
        Err(
            Error {
                context: "check program `class OtherClass { fn no_such_class (c : given ClassName) -> () { } }`",
                source: Error {
                    context: "check class named `OtherClass`",
                    source: Error {
                        context: "check method named `no_such_class`",
                        source: Error {
                            context: "check type `given ClassName`",
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
        class TheClass {
            fn empty_method(self) -> () {}
        }
    ",
    )));
}
