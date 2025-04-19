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
                foo.i.move;
                foo.i.move;
            }
        }
    ")).assert_err(
        expect_test::expect![[r#"
            check program `class Data { } class Foo { i : Data ; } class Main { fn main (my self) -> Int { let foo = new Foo (new Data ()) ; foo . i . move ; foo . i . move ; } }`

            Caused by:
                0: check class named `Main`
                1: check method named `main`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; foo . i . move ; foo . i . move ; }, as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; foo . i . move ; foo . i . move ; }, as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; foo . i . move ; foo . i . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (new Data ()) ; foo . i . move ; foo . i . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, foo . i . move ;, foo . i . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let foo = new Foo (new Data ()) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo . i}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr { expr: new Foo (new Data ()), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "new" failed at step #6 (src/file.rs:LL:CC) because
                                               judgment `type_field_exprs_as { temp_var: @ fresh(0), exprs: [new Data ()], fields: [i : Data ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Foo}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "cons" failed at step #6 (src/file.rs:LL:CC) because
                                                   judgment `sub { a: Data, b: Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Foo}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                     the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                       judgment `sub_perms { a: my, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Foo}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                         the rule "apply to shared" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Foo}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                             the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Foo}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   pattern `true` did not match value `false`"#]],
    )
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn give_field_of_moved_variable() {
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
                    foo.move;
                    foo.i.move;
                }
            }
        "
      )).assert_err(
        expect_test::expect![[r#"
            check program `class Data { } class Foo { i : Data ; } class Main { fn main (my self) -> Int { let foo = new Foo (new Data ()) ; foo . move ; foo . i . move ; } }`

            Caused by:
                0: check class named `Main`
                1: check method named `main`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; foo . move ; foo . i . move ; }, as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; foo . move ; foo . i . move ; }, as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; foo . move ; foo . i . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (new Data ()) ; foo . move ; foo . i . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, foo . move ;, foo . i . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let foo = new Foo (new Data ()) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo, foo . i}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr { expr: new Foo (new Data ()), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "new" failed at step #6 (src/file.rs:LL:CC) because
                                               judgment `type_field_exprs_as { temp_var: @ fresh(0), exprs: [new Data ()], fields: [i : Data ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Foo}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "cons" failed at step #6 (src/file.rs:LL:CC) because
                                                   judgment `sub { a: Data, b: Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Foo}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                     the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                       judgment `sub_perms { a: my, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Foo}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                         the rule "apply to shared" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Foo}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                             the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Foo}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   pattern `true` did not match value `false`"#]],
    )
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn give_variable_with_moved_field() {
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
                    foo.i.move;
                    foo.move;
                }
            }
        "
        )).assert_err(
        expect_test::expect![[r#"
            check program `class Data { } class Foo { i : Data ; } class Main { fn main (my self) -> Int { let foo = new Foo (new Data ()) ; foo . i . move ; foo . move ; } }`

            Caused by:
                0: check class named `Main`
                1: check method named `main`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; foo . i . move ; foo . move ; }, as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; foo . i . move ; foo . move ; }, as_ty: Int, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; foo . i . move ; foo . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (new Data ()) ; foo . i . move ; foo . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, foo . i . move ;, foo . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let foo = new Foo (new Data ()) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo, foo . i}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr { expr: new Foo (new Data ()), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "new" failed at step #6 (src/file.rs:LL:CC) because
                                               judgment `type_field_exprs_as { temp_var: @ fresh(0), exprs: [new Data ()], fields: [i : Data ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Foo}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "cons" failed at step #6 (src/file.rs:LL:CC) because
                                                   judgment `sub { a: Data, b: Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Foo}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                     the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                       judgment `sub_perms { a: my, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Foo}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                         the rule "apply to shared" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Foo}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                             the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Foo}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   pattern `true` did not match value `false`"#]],
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
                let bar = foo.ref;
                bar.move;
                bar.move;
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
                      let bar = foo.mut;
                      bar.move;
                      bar.move;
                      ();
                  }
              }
          ",
    )).assert_err(
      expect_test::expect![[r#"
          check program `class Data { } class Foo { i : Data ; } class Main { fn main (my self) -> () { let foo = new Foo (new Data ()) ; let bar = foo . mut ; bar . move ; bar . move ; () ; } }`

          Caused by:
              0: check class named `Main`
              1: check method named `main`
              2: check function body
              3: judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; let bar = foo . mut ; bar . move ; bar . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                   the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                     judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; let bar = foo . mut ; bar . move ; bar . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                       the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                         judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; let bar = foo . mut ; bar . move ; bar . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                           the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                             judgment `type_block { block: { let foo = new Foo (new Data ()) ; let bar = foo . mut ; bar . move ; bar . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                               the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                 judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, let bar = foo . mut ;, bar . move ;, bar . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                   the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                     judgment `type_statement { statement: let foo = new Foo (new Data ()) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo}, traversed: {} } }` failed at the following rule(s):
                                       the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                         judgment `type_expr { expr: new Foo (new Data ()), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                           the rule "new" failed at step #6 (src/file.rs:LL:CC) because
                                             judgment `type_field_exprs_as { temp_var: @ fresh(0), exprs: [new Data ()], fields: [i : Data ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Foo}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                               the rule "cons" failed at step #6 (src/file.rs:LL:CC) because
                                                 judgment `sub { a: Data, b: Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Foo}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                   the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                     judgment `sub_perms { a: my, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Foo}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                       the rule "apply to shared" failed at step #0 (src/file.rs:LL:CC) because
                                                         judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Foo}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                           the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                             judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Foo}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                               the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                 pattern `true` did not match value `false`"#]],
    )
}
