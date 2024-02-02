use crate::{dada_lang::term, type_system::check_program};
use formality_core::{test, test_util::ResultTestExt};

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn give_same_field_twice() {
    check_program(
        &term(
            "
        class Data { }

        class Foo {
            i: Data;
        }

        class Main {
            fn main(my self) -> Int {
                let foo = new Foo(new Data());
                foo.i.give;
                foo.i.give;
            }
        }
    ")).assert_err(
        expect_test::expect![[r#"
            check program `class Data { } class Foo { i : Data ; } class Main { fn main (my self) -> Int { let foo = new Foo (new Data ()) ; foo . i . give ; foo . i . give ; } }`

            Caused by:
                0: check class named `Main`
                1: check method named `main`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; foo . i . give ; foo . i . give ; }, as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; foo . i . give ; foo . i . give ; }, as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; foo . i . give ; foo . i . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (new Data ()) ; foo . i . give ; foo . i . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, foo . i . give ;, foo . i . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [foo . i . give ;, foo . i . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [foo . i . give ;], ty: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo . i} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: foo . i . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo . i} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                 the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: foo . i . give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo . i} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                     the rule "give place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: give, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo . i} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                           condition evaluted to false: `!flow.is_moved(&place)`
                                                             flow = Flow { moved_places: {foo . i} }
                                                             &place = foo . i"#]],
    )
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn give_field_of_given_variable() {
    check_program(
        &term(
            "
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn main(my self) -> Int {
                    let foo = new Foo(new Data());
                    foo.give;
                    foo.i.give;
                }
            }
        "
      )).assert_err(
        expect_test::expect![[r#"
            check program `class Data { } class Foo { i : Data ; } class Main { fn main (my self) -> Int { let foo = new Foo (new Data ()) ; foo . give ; foo . i . give ; } }`

            Caused by:
                0: check class named `Main`
                1: check method named `main`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; foo . give ; foo . i . give ; }, as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; foo . give ; foo . i . give ; }, as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; foo . give ; foo . i . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (new Data ()) ; foo . give ; foo . i . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, foo . give ;, foo . i . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [foo . give ;, foo . i . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [foo . i . give ;], ty: Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: foo . i . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                 the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: foo . i . give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                     the rule "give place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: give, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                           condition evaluted to false: `!flow.is_moved(&place)`
                                                             flow = Flow { moved_places: {foo} }
                                                             &place = foo . i"#]],
    )
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn give_variable_with_given_field() {
    check_program(
        &term(
        "
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn main(my self) -> Int {
                    let foo = new Foo(new Data());
                    foo.i.give;
                    foo.give;
                }
            }
        "
        )).assert_err(
        expect_test::expect![[r#"
            check program `class Data { } class Foo { i : Data ; } class Main { fn main (my self) -> Int { let foo = new Foo (new Data ()) ; foo . i . give ; foo . give ; } }`

            Caused by:
                0: check class named `Main`
                1: check method named `main`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; foo . i . give ; foo . give ; }, as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; foo . i . give ; foo . give ; }, as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; foo . i . give ; foo . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (new Data ()) ; foo . i . give ; foo . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, foo . i . give ;, foo . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [foo . i . give ;, foo . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [foo . give ;], ty: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo . i} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: foo . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo . i} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                 the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: foo . give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo . i} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                     the rule "give place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: give, place: foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo . i} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                           condition evaluted to false: `!flow.is_moved(&place)`
                                                             flow = Flow { moved_places: {foo . i} }
                                                             &place = foo"#]],
    )
}

/// Check giving a shared value twice (giving a shared value doesn't consume it).
#[test]
#[allow(non_snake_case)]
fn give_shared_value() {
    check_program(&term(
        "
        class Data { }

        class Foo {
            i: Data;
        }

        class Main {
            fn main(my self) {
                let foo = new Foo(new Data());
                let bar = foo.share;
                bar.give;
                bar.give;
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
              class Data { }

              class Foo {
                  i: Data;
              }

              class Main {
                  fn main(my self) {
                      let foo = new Foo(new Data());
                      let bar = foo.lease;
                      bar.give;
                      bar.give;
                      ();
                  }
              }
          ",
    )).assert_err(
      expect_test::expect![[r#"
          check program `class Data { } class Foo { i : Data ; } class Main { fn main (my self) -> () { let foo = new Foo (new Data ()) ; let bar = foo . lease ; bar . give ; bar . give ; () ; } }`

          Caused by:
              0: check class named `Main`
              1: check method named `main`
              2: check function body
              3: judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; let bar = foo . lease ; bar . give ; bar . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                   the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                     judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; let bar = foo . lease ; bar . give ; bar . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                       the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                         judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; let bar = foo . lease ; bar . give ; bar . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                           the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                             judgment `type_block { block: { let foo = new Foo (new Data ()) ; let bar = foo . lease ; bar . give ; bar . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                               the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                 judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, let bar = foo . lease ;, bar . give ;, bar . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                   the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                     judgment `type_statements_with_final_ty { statements: [let bar = foo . lease ;, bar . give ;, bar . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                       the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                         judgment `type_statements_with_final_ty { statements: [bar . give ;, bar . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: leased {foo} Foo, foo: Foo}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                           the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                             judgment `type_statements_with_final_ty { statements: [bar . give ;, () ;], ty: leased {foo} Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: leased {foo} Foo, foo: Foo}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {bar} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                               the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                                 judgment `type_statement { statement: bar . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: leased {foo} Foo, foo: Foo}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {bar} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                   the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                                     judgment `type_expr { expr: bar . give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: leased {foo} Foo, foo: Foo}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {bar} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                       the rule "give place" failed at step #0 (src/file.rs:LL:CC) because
                                                         judgment `access_permitted { access: give, place: bar, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: leased {foo} Foo, foo: Foo}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {bar} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                           the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                             condition evaluted to false: `!flow.is_moved(&place)`
                                                               flow = Flow { moved_places: {bar} }
                                                               &place = bar"#]],
    )
}
