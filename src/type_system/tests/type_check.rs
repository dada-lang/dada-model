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
            check program `class TheClass { fn empty_method (my self) -> Int { } }`

            Caused by:
                0: check class named `TheClass`
                1: check method named `empty_method`
                2: check function body
                3: judgment `can_type_expr_as { expr: { }, as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { }, as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                           judgment `sub { a: (), b: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `sub_in { terms_a: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, a: (), terms_b: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, b: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `sub_terms { terms_a: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {(Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, ())}, shared_places: {}, leased_places: {} }, terms_b: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {(Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, Int)}, shared_places: {}, leased_places: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                     the rule "sub_teams" failed at step #5 (src/file.rs:LL:CC) because
                                       judgment `sub_forall_exists { a_s: {(Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, ())}, b_s: {(Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, Int)}, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment had no applicable rules: `sub_base { terms_a: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, a: (), terms_b: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, b: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }`"#]],
    )
}

/// Check that empty blocks return unit (and that is not assignable to Int)
#[test]
fn bad_int_ascription() {
    check_program(
        &term(
            "
            class TheClass {
                fn empty_method(my self) {
                    let x: Int = ();
                }
            }
        ",
        )
    ).assert_err(
        expect_test::expect![[r#"
            check program `class TheClass { fn empty_method (my self) -> () { let x : Int = () ; } }`

            Caused by:
                0: check class named `TheClass`
                1: check method named `empty_method`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let x : Int = () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let x : Int = () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let x : Int = () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let x : Int = () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let x : Int = () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let x : Int = () ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr_as { expr: (), as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                             the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `sub { a: (), b: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                 the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `sub_in { terms_a: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, a: (), terms_b: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, b: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                     the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                       judgment `sub_terms { terms_a: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {(Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, ())}, shared_places: {}, leased_places: {} }, terms_b: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {(Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, Int)}, shared_places: {}, leased_places: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                         the rule "sub_teams" failed at step #5 (src/file.rs:LL:CC) because
                                                           judgment `sub_forall_exists { a_s: {(Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, ())}, b_s: {(Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, Int)}, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment had no applicable rules: `sub_base { terms_a: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, a: (), terms_b: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, b: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }`"#]],
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
                foo.give;
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
                    foo.share;
                }
            }
        ",
        ),
    ).assert_err(
        expect_test::expect![[r#"
            check program `class Foo { } class TheClass { fn empty_method (my self) -> Foo { let foo = new Foo () ; foo . share ; } }`

            Caused by:
                0: check class named `TheClass`
                1: check method named `empty_method`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo () ; foo . share ; }, as_ty: Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo () ; foo . share ; }, as_ty: Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                           judgment `sub { a: shared {foo} Foo, b: Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, foo: Foo}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `sub_in { terms_a: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, a: shared {foo} Foo, terms_b: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, b: Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, foo: Foo}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `sub_terms { terms_a: Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {(Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {}, shared_places: {foo}, leased_places: {} }, Foo)}, shared_places: {foo}, leased_places: {} }, terms_b: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {(Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, Foo)}, shared_places: {}, leased_places: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, foo: Foo}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                     the rule "sub_teams" failed at step #0 (src/file.rs:LL:CC) because
                                       condition evaluted to false: `terms_a.shared <= terms_b.shared`"#]],
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
                foo.i.give;
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
                foo.i = foo.i.give + 1;
                foo.i.give;
            }
        }
    ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}
