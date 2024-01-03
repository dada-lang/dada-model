use crate::{dada_lang::term, type_system::check_program};
use formality_core::{test, test_util::ResultTestExt};

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn give_same_field_twice() {
    check_program(
        &term(
            "
        class Foo {
            i: Int;
        }

        class TheClass {
            fn empty_method(my self) -> Int {
                let foo = new Foo(22);
                give foo.i;
                give foo.i;
            }
        }
    ")).assert_err(
        expect_test::expect![[r#"
            check program `class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo . i ; } }`

            Caused by:
                0: check class named `TheClass`
                1: check method named `empty_method`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (22) ; give foo . i ; give foo . i ; }, as_ty: Int, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (22) ; give foo . i ; give foo . i ; }, as_ty: Int, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (22) ; give foo . i ; give foo . i ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (22) ; give foo . i ; give foo . i ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let foo = new Foo (22) ;, give foo . i ;, give foo . i ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [give foo . i ;, give foo . i ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [give foo . i ;], ty: Int, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo . i} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: give foo . i ;, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo . i} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                 the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: give foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo . i} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                     the rule "give place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: give, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo . i} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                           condition evaluted to false: `!flow.is_moved(&place)`"#]],
    )
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn give_field_of_given_variable() {
    check_program(
        &term(
            "
            class Foo {
                i: Int;
            }

            class TheClass {
                fn empty_method(my self) -> Int {
                    let foo = new Foo(22);
                    give foo;
                    give foo.i;
                }
            }
        "
      )).assert_err(
        expect_test::expect![[r#"
            check program `class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo ; give foo . i ; } }`

            Caused by:
                0: check class named `TheClass`
                1: check method named `empty_method`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (22) ; give foo ; give foo . i ; }, as_ty: Int, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (22) ; give foo ; give foo . i ; }, as_ty: Int, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (22) ; give foo ; give foo . i ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (22) ; give foo ; give foo . i ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let foo = new Foo (22) ;, give foo ;, give foo . i ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [give foo ;, give foo . i ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [give foo . i ;], ty: Foo, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: give foo . i ;, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                 the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: give foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                     the rule "give place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: give, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                           condition evaluted to false: `!flow.is_moved(&place)`"#]],
    )
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn give_variable_with_given_field() {
    check_program(
        &term(
        "
            class Foo {
                i: Int;
            }

            class TheClass {
                fn empty_method(my self) -> Int {
                    let foo = new Foo(22);
                    give foo.i;
                    give foo;
                }
            }
        "
        )).assert_err(
        expect_test::expect![[r#"
            check program `class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo ; } }`

            Caused by:
                0: check class named `TheClass`
                1: check method named `empty_method`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (22) ; give foo . i ; give foo ; }, as_ty: Int, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (22) ; give foo . i ; give foo ; }, as_ty: Int, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (22) ; give foo . i ; give foo ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (22) ; give foo . i ; give foo ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let foo = new Foo (22) ;, give foo . i ;, give foo ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [give foo . i ;, give foo ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [give foo ;], ty: Int, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo . i} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: give foo ;, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo . i} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                 the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: give foo, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo . i} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                     the rule "give place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: give, place: foo, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo . i} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                           condition evaluted to false: `!flow.is_moved(&place)`"#]],
    )
}

/// Check giving a shared value twice (giving a shared value doesn't consume it).
#[test]
#[allow(non_snake_case)]
fn give_shared_value() {
    check_program(&term(
        "
        class Foo {
            i: Int;
        }

        class TheClass {
            fn empty_method(my self) {
                let foo = new Foo(22);
                let bar = share foo;
                give bar;
                give bar;
                ();
            }
        }
    ",
    ))
    .assert_ok(expect_test::expect!["()"])
}

/// Check giving a leased value twice errors.
#[test]
#[allow(non_snake_case)]
fn give_leased_value() {
    check_program(
        &term(
            "
              class Foo {
                  i: Int;
              }

              class TheClass {
                  fn empty_method(my self) {
                      let foo = new Foo(22);
                      let bar = lease foo;
                      give bar;
                      give bar;
                      ();
                  }
              }
          ",
    )).assert_err(
      expect_test::expect![[r#"
          check program `class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; give bar ; give bar ; () ; } }`

          Caused by:
              0: check class named `TheClass`
              1: check method named `empty_method`
              2: check function body
              3: judgment `can_type_expr_as { expr: { let foo = new Foo (22) ; let bar = lease foo ; give bar ; give bar ; () ; }, as_ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; give bar ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                   the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                     judgment `type_expr_as { expr: { let foo = new Foo (22) ; let bar = lease foo ; give bar ; give bar ; () ; }, as_ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; give bar ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                       the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                         judgment `type_expr { expr: { let foo = new Foo (22) ; let bar = lease foo ; give bar ; give bar ; () ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; give bar ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                           the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                             judgment `type_block { block: { let foo = new Foo (22) ; let bar = lease foo ; give bar ; give bar ; () ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; give bar ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                               the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                 judgment `type_statements_with_final_ty { statements: [let foo = new Foo (22) ;, let bar = lease foo ;, give bar ;, give bar ;, () ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; give bar ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                   the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                     judgment `type_statements_with_final_ty { statements: [let bar = lease foo ;, give bar ;, give bar ;, () ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; give bar ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                       the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                         judgment `type_statements_with_final_ty { statements: [give bar ;, give bar ;, () ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; give bar ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : leased (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                           the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                             judgment `type_statements_with_final_ty { statements: [give bar ;, () ;], ty: leased (foo) Foo, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; give bar ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : leased (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {bar} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                               the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                                 judgment `type_statement { statement: give bar ;, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; give bar ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : leased (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {bar} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                   the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                                     judgment `type_expr { expr: give bar, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; give bar ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : leased (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {bar} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                       the rule "give place" failed at step #0 (src/file.rs:LL:CC) because
                                                         judgment `access_permitted { access: give, place: bar, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; give bar ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : leased (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {bar} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                           the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                             condition evaluted to false: `!flow.is_moved(&place)`"#]],
    )
}
