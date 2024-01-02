use crate::{dada_lang::term, type_system::check_program};
use formality_core::{test, test_util::ResultTestExt};

/// Check we are able to type check an empty method.
#[test]
fn empty_method() {
    check_program(&term(
        "
        class TheClass {
            fn empty_method(my self) {}
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

/// Check that empty blocks return unit (and that is not assignable to Int)
#[test]
fn bad_int_return_value() {
    check_program(
        &term(
            "
            class TheClass {
                fn empty_method(my self) -> Int {}
            }
        ",
        )
    ).assert_err(
        expect_test::expect![[r#"
            check program `class TheClass { fn empty_method (Some(my self)) -> Int { } }`

            Caused by:
                0: check class named `TheClass`
                1: check method named `empty_method`
                2: check function body
                3: judgment `can_type_expr_as { expr: { }, as_ty: Int, env: Env { program: class TheClass { fn empty_method (Some(my self)) -> Int { } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { }, as_ty: Int, env: Env { program: class TheClass { fn empty_method (Some(my self)) -> Int { } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                           judgment `sub { a: (), b: Int, env: Env { program: class TheClass { fn empty_method (Some(my self)) -> Int { } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "same class" failed at step #0 (src/file.rs:LL:CC) because
                               condition evaluted to false: `name_a == name_b`
       "#]],
    )
}

/// Check returning an integer with return type of Int.
#[test]
fn good_int_return_value() {
    check_program(&term(
        "
        class TheClass {
            fn empty_method(my self) -> Int {
                22;
            }
        }
    ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

/// Check returning an instance of a class.
#[test]
#[allow(non_snake_case)]
fn return_instance_of_Foo() {
    check_program(&term(
        "
        class Foo { }

        class TheClass {
            fn empty_method(my self) -> Foo {
                new Foo();
            }
        }
    ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

/// Check returning an instance of a class.
#[test]
#[allow(non_snake_case)]
fn return_from_variable() {
    check_program(&term(
        "
        class Foo { }

        class TheClass {
            fn empty_method(my self) -> Foo {
                let foo = new Foo();
                give foo;
            }
        }
    ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn return_shared_not_give() {
    check_program(
        &term(
            "
            class Foo { }
    
            class TheClass {
                fn empty_method(my self) -> Foo {
                    let foo = new Foo();
                    share foo;
                }
            }
        ",
        ),
    ).assert_err(
        expect_test::expect![[r#"
            check program `class Foo { } class TheClass { fn empty_method (Some(my self)) -> Foo { let foo = new Foo () ; foo ; } }`

            Caused by:
                0: check class named `TheClass`
                1: check method named `empty_method`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo () ; foo ; }, as_ty: Foo, env: Env { program: class Foo { } class TheClass { fn empty_method (Some(my self)) -> Foo { let foo = new Foo () ; foo ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo () ; foo ; }, as_ty: Foo, env: Env { program: class Foo { } class TheClass { fn empty_method (Some(my self)) -> Foo { let foo = new Foo () ; foo ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                           judgment `sub { a: shared (foo) Foo, b: Foo, env: Env { program: class Foo { } class TheClass { fn empty_method (Some(my self)) -> Foo { let foo = new Foo () ; foo ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "collapse a or b" failed at step #3 (src/file.rs:LL:CC) because
                               judgment `sub { a: shared (foo) Foo, b: my Foo, env: Env { program: class Foo { } class TheClass { fn empty_method (Some(my self)) -> Foo { let foo = new Foo () ; foo ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "apply-perms" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment had no applicable rules: `sub { a: shared (foo), b: my, env: Env { program: class Foo { } class TheClass { fn empty_method (Some(my self)) -> Foo { let foo = new Foo () ; foo ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }`
                                 the rule "collapse a or b" failed at step #3 (src/file.rs:LL:CC) because
                                   cyclic proof attempt: `sub { a: shared (foo) Foo, b: Foo, env: Env { program: class Foo { } class TheClass { fn empty_method (Some(my self)) -> Foo { let foo = new Foo () ; foo ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }`
       "#]],
    )
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn return_int_field_from_class_with_int_field() {
    check_program(&term(
        "
        class Foo {
            i: Int;
        }

        class TheClass {
            fn empty_method(my self) -> Int {
                let foo = new Foo(22);
                give foo.i;
            }
        }
    ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn return_modified_int_field_from_class_with_int_field() {
    check_program(&term(
        "
        class Foo {
            i: Int;
        }

        class TheClass {
            fn empty_method(my self) -> Int {
                let foo = new Foo(22);
                foo.i = give foo.i + 1;
                give foo.i;
            }
        }
    ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}
