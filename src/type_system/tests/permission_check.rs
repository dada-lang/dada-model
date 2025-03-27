use formality_core::test;
use formality_core::test_util::ResultTestExt;

use crate::{dada_lang::term, type_system::check_program};

mod borrowck_loan_kills;

/// Check sharing a field from a leased value errs.
#[test]
#[allow(non_snake_case)]
fn share_field_of_leased_value() {
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
                        let i = foo.i.share;
                        bar.give;
                        ();
                    }
                }
            ",
        ),
    ).assert_err(
        expect_test::expect![[r#"
            check program `class Data { } class Foo { i : Data ; } class Main { fn main (my self) -> () { let foo = new Foo (new Data ()) ; let bar = foo . lease ; let i = foo . i . share ; bar . give ; () ; } }`

            Caused by:
                0: check class named `Main`
                1: check method named `main`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; let bar = foo . lease ; let i = foo . i . share ; bar . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; let bar = foo . lease ; let i = foo . i . share ; bar . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; let bar = foo . lease ; let i = foo . i . share ; bar . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (new Data ()) ; let bar = foo . lease ; let i = foo . i . share ; bar . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, let bar = foo . lease ;, let i = foo . i . share ;, bar . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let bar = foo . lease ;, let i = foo . i . share ;, bar . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: let bar = foo . lease ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar, foo . i}, traversed: {} } }` failed at the following rule(s):
                                             the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: foo . lease, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo . i}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `access_permitted { access: lease, place: foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo . i}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `env_permits_access { access: lease, place: foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo . i}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `parameters_permit_access { parameters: [Foo], access: lease, place: foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `parameter_permits_access { parameter: Foo, access: lease, place: foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `liens { a: Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `some_lien { a: Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                           expression evaluated to an empty collection: `parameters`"#]],
    )
}

/// Check sharing a field from a shared value is ok.
#[test]
#[allow(non_snake_case)]
fn share_field_of_shared_value() {
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
                    let i = foo.i.share;
                    bar.give;
                    ();
                }
            }
        ",
    ))
    .assert_ok(expect_test::expect!["()"])
}

/// Check leasing a field from a shared value is not ok.
#[test]
#[allow(non_snake_case)]
fn lease_field_of_shared_value() {
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
                    let bar = foo.share;
                    let i = foo.i.lease;
                    bar.give;
                    ();
                }
            }
        ",
        ),
    ).assert_err(
        expect_test::expect![[r#"
            check program `class Data { } class Foo { i : Data ; } class Main { fn main (my self) -> () { let foo = new Foo (new Data ()) ; let bar = foo . share ; let i = foo . i . lease ; bar . give ; () ; } }`

            Caused by:
                0: check class named `Main`
                1: check method named `main`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; let bar = foo . share ; let i = foo . i . lease ; bar . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; let bar = foo . share ; let i = foo . i . lease ; bar . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; let bar = foo . share ; let i = foo . i . lease ; bar . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (new Data ()) ; let bar = foo . share ; let i = foo . i . lease ; bar . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, let bar = foo . share ;, let i = foo . i . lease ;, bar . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let bar = foo . share ;, let i = foo . i . lease ;, bar . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: let bar = foo . share ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar, foo . i}, traversed: {} } }` failed at the following rule(s):
                                             the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: foo . share, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo . i}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `access_permitted { access: share, place: foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo . i}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `env_permits_access { access: share, place: foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo . i}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `parameters_permit_access { parameters: [Foo], access: share, place: foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `parameter_permits_access { parameter: Foo, access: share, place: foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `liens { a: Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `some_lien { a: Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                           expression evaluated to an empty collection: `parameters`"#]],
    )
}

/// Check giving a field from a shared value is not ok.
#[test]
#[allow(non_snake_case)]
fn give_field_of_shared_value() {
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
                    let bar = foo.share;
                    let i = foo.i.give;
                    bar.give;
                    ();
                }
            }
        ",
        ),
    ).assert_err(
        expect_test::expect![[r#"
            check program `class Data { } class Foo { i : Data ; } class Main { fn main (my self) -> () { let foo = new Foo (new Data ()) ; let bar = foo . share ; let i = foo . i . give ; bar . give ; () ; } }`

            Caused by:
                0: check class named `Main`
                1: check method named `main`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; let bar = foo . share ; let i = foo . i . give ; bar . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; let bar = foo . share ; let i = foo . i . give ; bar . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; let bar = foo . share ; let i = foo . i . give ; bar . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (new Data ()) ; let bar = foo . share ; let i = foo . i . give ; bar . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, let bar = foo . share ;, let i = foo . i . give ;, bar . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let bar = foo . share ;, let i = foo . i . give ;, bar . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: let bar = foo . share ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar, foo . i}, traversed: {} } }` failed at the following rule(s):
                                             the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: foo . share, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo . i}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `access_permitted { access: share, place: foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo . i}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `env_permits_access { access: share, place: foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo . i}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `parameters_permit_access { parameters: [Foo], access: share, place: foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `parameter_permits_access { parameter: Foo, access: share, place: foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `liens { a: Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `some_lien { a: Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                           expression evaluated to an empty collection: `parameters`"#]],
    )
}

/// Check sharing a field from a leased value errs.
#[test]
#[allow(non_snake_case)]
fn share_field_of_leased_value_after_explicit_give() {
    check_program(&term(
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
                        let i = foo.i.share;
                        ();
                    }
                }
            ",
    ))
    .assert_ok(expect_test::expect!["()"])
}

/// Check that we can permit accessing `foo.i` even though
/// it was leased since `bar` is dead.
#[test]
#[allow(non_snake_case)]
fn share_field_of_leased_value_without_explicit_give() {
    check_program(&term(
        "
                class Data { }

                class Foo {
                    i: Data;
                }

                class Main {
                    fn main(my self) {
                        let foo = new Foo(new Data());
                        let bar = foo.lease;
                        let i = foo.i.share;
                        ();
                    }
                }
            ",
    ))
    .assert_ok(expect_test::expect!["()"])
}

#[test]
fn share_field_of_leased_value_but_lease_variable_is_dead() {
    // Here, the variable `q` is dead, but its restrictions must
    // still be enforced because `r` is live.
    check_program(&term(
        "
                class Data { }

                class Foo {
                    i: Data;
                }

                class Main {
                    fn main(my self) {
                        let p = new Foo(new Data());
                        let q = p.lease;
                        let r = q.share;
                        let i = p.i.share;
                        r.give;
                        ();
                    }
                }
            ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Foo { i : Data ; } class Main { fn main (my self) -> () { let p = new Foo (new Data ()) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `main`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let p = new Foo (new Data ()) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let p = new Foo (new Data ()) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let p = new Foo (new Data ()) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let p = new Foo (new Data ()) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let p = new Foo (new Data ()) ;, let q = p . lease ;, let r = q . share ;, let i = p . i . share ;, r . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let q = p . lease ;, let r = q . share ;, let i = p . i . share ;, r . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let q = p . lease ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p . i, q}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr { expr: p . lease, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p . i}, traversed: {} } }` failed at the following rule(s):
                                             the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `access_permitted { access: lease, place: p, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p . i}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `env_permits_access { access: lease, place: p, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p . i}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `parameters_permit_access { parameters: [Foo], access: lease, place: p, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `parameter_permits_access { parameter: Foo, access: lease, place: p, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `liens { a: Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `some_lien { a: Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                       expression evaluated to an empty collection: `parameters`"#]])
}

#[test]
fn share_field_of_leased_value_but_lease_variable_is_dead_explicit_ty() {
    // Here, the variable `q` is dead, but its restrictions must
    // still be enforced because `r` is live.
    check_program(&term(
        "
                class Data { }

                class Foo {
                    i: Data;
                }

                class Main {
                    fn main(my self) {
                        let p: my Foo = new Foo(new Data());
                        let q: leased[p] Foo = p.lease;
                        let r: shared[q] Foo = q.share;
                        let i: shared[p.i] Data = p.i.share;
                        r.give;
                        ();
                    }
                }
            ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Foo { i : Data ; } class Main { fn main (my self) -> () { let p : my Foo = new Foo (new Data ()) ; let q : leased [p] Foo = p . lease ; let r : shared [q] Foo = q . share ; let i : shared [p . i] Data = p . i . share ; r . give ; () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `main`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let p : my Foo = new Foo (new Data ()) ; let q : leased [p] Foo = p . lease ; let r : shared [q] Foo = q . share ; let i : shared [p . i] Data = p . i . share ; r . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let p : my Foo = new Foo (new Data ()) ; let q : leased [p] Foo = p . lease ; let r : shared [q] Foo = q . share ; let i : shared [p . i] Data = p . i . share ; r . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let p : my Foo = new Foo (new Data ()) ; let q : leased [p] Foo = p . lease ; let r : shared [q] Foo = q . share ; let i : shared [p . i] Data = p . i . share ; r . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let p : my Foo = new Foo (new Data ()) ; let q : leased [p] Foo = p . lease ; let r : shared [q] Foo = q . share ; let i : shared [p . i] Data = p . i . share ; r . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let p : my Foo = new Foo (new Data ()) ;, let q : leased [p] Foo = p . lease ;, let r : shared [q] Foo = q . share ;, let i : shared [p . i] Data = p . i . share ;, r . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let q : leased [p] Foo = p . lease ;, let r : shared [q] Foo = q . share ;, let i : shared [p . i] Data = p . i . share ;, r . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let q : leased [p] Foo = p . lease ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p . i, q}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr_as { expr: p . lease, as_ty: leased [p] Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p . i}, traversed: {} } }` failed at the following rule(s):
                                             the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: p . lease, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p . i}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `access_permitted { access: lease, place: p, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p . i}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `env_permits_access { access: lease, place: p, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p . i}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `parameters_permit_access { parameters: [my Foo], access: lease, place: p, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `parameter_permits_access { parameter: my Foo, access: lease, place: p, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `liens { a: my Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `some_lien { a: my Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "apply-perm-ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `some_lien { a: Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                               expression evaluated to an empty collection: `parameters`"#]])
}

/// Test where we expect data leased from self and then try to use self.
/// Error.
#[test]
#[allow(non_snake_case)]
fn pair_method__leased_self__use_self() {
    check_program(&term(
        "
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(my self, data: leased[self] Data) {
                  self.a.lease;
                  data.give;
                  ();
                }
            }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { a : Data ; b : Data ; fn method (my self data : leased [self] Data) -> () { self . a . lease ; data . give ; () ; } }`

        Caused by:
            0: check class named `Pair`
            1: check method named `method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { self . a . lease ; data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: leased [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { self . a . lease ; data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: leased [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { self . a . lease ; data . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: leased [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { self . a . lease ; data . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: leased [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [self . a . lease ;, data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: leased [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: self . a . lease ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: leased [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                     the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `type_expr { expr: self . a . lease, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: leased [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                         the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `access_permitted { access: lease, place: self . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: leased [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                             the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `env_permits_access { access: lease, place: self . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: leased [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `parameters_permit_access { parameters: [leased [self] Data], access: lease, place: self . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: leased [self] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `parameter_permits_access { parameter: leased [self] Data, access: lease, place: self . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: leased [self] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `lien_permit_access { lien: leased(self), access: lease, accessed_place: self . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: leased [self] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "leased" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `leased_place_permits_access { leased_place: self, access: lease, accessed_place: self . a }` failed at the following rule(s):
                                                                 the rule "lease-mutation" failed at step #0 (src/file.rs:LL:CC) because
                                                                   condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
                                                                     &accessed_place = self . a
                                                                     &leased_place = self"#]])
}

/// Test that we cannot mutate fields of a shared class.
#[test]
#[allow(non_snake_case)]
fn mutate_field_of_shared_pair() {
    check_program(&term(
        "
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(my self, data: my Data) {
                  let me = self.share;
                  me.a = data.give;
                  ();
                }
            }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { a : Data ; b : Data ; fn method (my self data : my Data) -> () { let me = self . share ; me . a = data . give ; () ; } }`

        Caused by:
            0: check class named `Pair`
            1: check method named `method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let me = self . share ; me . a = data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let me = self . share ; me . a = data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let me = self . share ; me . a = data . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let me = self . share ; me . a = data . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let me = self . share ;, me . a = data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: let me = self . share ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {me} } }` failed at the following rule(s):
                                     the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `type_expr { expr: self . share, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                         the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `access_permitted { access: share, place: self, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                             the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `env_permits_access { access: share, place: self, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `parameters_permit_access { parameters: [my Data], access: share, place: self, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `parameter_permits_access { parameter: my Data, access: share, place: self, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `liens { a: my Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `some_lien { a: my Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "apply-perm-ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `some_lien { a: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                       expression evaluated to an empty collection: `parameters`"#]])
}

/// Test that we cannot mutate fields of a shared class.
#[test]
#[allow(non_snake_case)]
fn mutate_field_of_our_pair() {
    check_program(&term(
        "
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(my self, pair: our Pair, data: my Data) {
                  pair.a = data.give;
                  ();
                }
            }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { a : Data ; b : Data ; fn method (my self pair : our Pair, data : my Data) -> () { pair . a = data . give ; () ; } }`

        Caused by:
            0: check class named `Pair`
            1: check method named `method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { pair . a = data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, pair: our Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { pair . a = data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, pair: our Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { pair . a = data . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, pair: our Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { pair . a = data . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, pair: our Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [pair . a = data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, pair: our Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: pair . a = data . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, pair: our Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "reassign" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_expr_as { expr: data . give, as_ty: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, pair: our Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {pair} } }` failed at the following rule(s):
                                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr { expr: data . give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, pair: our Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {pair} } }` failed at the following rule(s):
                                             the rule "give place" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `access_permitted { access: give, place: data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, pair: our Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {pair} } }` failed at the following rule(s):
                                                 the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `env_permits_access { access: give, place: data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, pair: our Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {pair} } }` failed at the following rule(s):
                                                     the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `parameters_permit_access { parameters: [our Pair], access: give, place: data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, pair: our Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `parameter_permits_access { parameter: our Pair, access: give, place: data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, pair: our Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `liens { a: our Pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, pair: our Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `some_lien { a: our Pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, pair: our Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "apply-perm-ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `some_lien { a: Pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, pair: our Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                           expression evaluated to an empty collection: `parameters`"#]])
}

/// Test that we can mutate fields of a leased class.
#[test]
#[allow(non_snake_case)]
fn mutate_field_of_leased_pair() {
    check_program(&term(
        "
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(my self, data: my Data) {
                  let me = self.lease;
                  me.a = data.give;
                  ();
                }
            }
        ",
    ))
    .assert_ok(expect_test::expect![["()"]])
}

// Test that we can give from `our` and go on using it
#[test]
#[allow(non_snake_case)]
fn give_our_then_use_later_and_return() {
    check_program(&term(
        "
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(my self, data: our Data) -> our Data {
                  let d: our Data = data.give;
                  let e: our Data = data.give;
                  let f: our Data = data.give;
                  d.give;
                }
            }
        ",
    ))
    .assert_ok(expect_test::expect![["()"]])
}

// Test that we can give from `shared` and go on using it
#[test]
#[allow(non_snake_case)]
fn give_shared_then_use_later_and_return() {
    check_program(&term(
        "
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(my self, owner: my Data, data: shared[owner] Data) -> shared[owner] Data {
                  let d: shared[owner] Data = data.give;
                  let e: shared[owner] Data = data.give;
                  let f: shared[owner] Data = data.give;
                  d.give;
                }
            }
        ",
    ))
    .assert_ok(expect_test::expect![["()"]])
}

// Test that we can give from `shared` and go on using it
#[test]
#[allow(non_snake_case)]
fn take_my_and_shared_move_my_then_return_shared() {
    check_program(&term(
        "
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(my self, owner: my Data, data: shared[owner] Data) -> shared[owner] Data {
                  let d: shared[owner] Data = data.give;
                  let owner1: my Data = owner.give;
                  d.give;
                }
            }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { a : Data ; b : Data ; fn method (my self owner : my Data, data : shared [owner] Data) -> shared [owner] Data { let d : shared [owner] Data = data . give ; let owner1 : my Data = owner . give ; d . give ; } }`

        Caused by:
            0: check class named `Pair`
            1: check method named `method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d : shared [owner] Data = data . give ; let owner1 : my Data = owner . give ; d . give ; }, as_ty: shared [owner] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: shared [owner] Data, owner: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d : shared [owner] Data = data . give ; let owner1 : my Data = owner . give ; d . give ; }, as_ty: shared [owner] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: shared [owner] Data, owner: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d : shared [owner] Data = data . give ; let owner1 : my Data = owner . give ; d . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: shared [owner] Data, owner: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d : shared [owner] Data = data . give ; let owner1 : my Data = owner . give ; d . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: shared [owner] Data, owner: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d : shared [owner] Data = data . give ;, let owner1 : my Data = owner . give ;, d . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: shared [owner] Data, owner: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: let d : shared [owner] Data = data . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: shared [owner] Data, owner: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {d, owner}, traversed: {} } }` failed at the following rule(s):
                                     the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `type_expr_as { expr: data . give, as_ty: shared [owner] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: shared [owner] Data, owner: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {owner}, traversed: {} } }` failed at the following rule(s):
                                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr { expr: data . give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: shared [owner] Data, owner: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {owner}, traversed: {} } }` failed at the following rule(s):
                                             the rule "give place" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `access_permitted { access: give, place: data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: shared [owner] Data, owner: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {owner}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `env_permits_access { access: give, place: data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: shared [owner] Data, owner: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {owner}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `parameters_permit_access { parameters: [my Data], access: give, place: data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: shared [owner] Data, owner: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `parameter_permits_access { parameter: my Data, access: give, place: data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: shared [owner] Data, owner: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `liens { a: my Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: shared [owner] Data, owner: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `some_lien { a: my Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: shared [owner] Data, owner: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "apply-perm-ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `some_lien { a: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: shared [owner] Data, owner: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                           expression evaluated to an empty collection: `parameters`"#]])
}

/// Interesting example from [conversation with Isaac][r]. In this example,
/// when `bar` calls `foo`, it takes a *locally leased* copy of `y` -- but since
/// `y` is stored into `x.value`, it escapes, and hence is no longer usable.
///
/// In Dada this is accepted because `leased(y) B R[Int]` can be converted to `B R[Int]`
/// so long as `y` is dead (as long as B is shared/leased).
///
/// [r]: https://gitlab.inf.ethz.ch/public-plf/borrowck-examples/-/blob/db0ece7ab20404935e4cf381471f425b41e6c009/tests/passing/reborrowing-escape-function.md
#[test]
fn escapes_ok() {
    check_program(&term(
        "
          class R[ty T] {
            value: T;
          }

          class Main {
            fn foo[perm A, perm B](my self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              move(A), lent(A),
              move(B), lent(B),
            {
              ();
            }

            fn bar[perm A, perm B](my self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              move(A), lent(A),
              move(B), lent(B),
            {
              self.give.foo[A, B](x.give, y.lease);
            }
          }
    ",
    ))
    .assert_ok(expect_test::expect![["()"]]);

    // fn foo<'a, 'b>(x : &'a mut &'b mut i32, y : &'b mut i32) {
    //   () // For example: *x = y;
    // }

    // fn bar<'a, 'b>(u : &'a mut &'b mut i32, v : &'b mut i32) {
    //   foo(u, &mut *v);
    // }

    // fn main() {}
}

/// See `escapes_ok`, but here we use `y` again (and hence get an error).
#[test]
fn escapes_err_use_again() {
    check_program(&term(
        "
          class R[ty T] {
            value: T;
          }

          class Main {
            fn foo[perm A, perm B](my self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              move(A), lent(A),
              move(B), lent(B),
            {
              ();
            }

            fn bar[perm A, perm B](my self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              move(A), lent(A),
              move(B), lent(B),
            {
              self.give.foo[A, B](x.give, y.lease);
              y.give;
            }
          }
    ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class R [ty] { value : ^ty0_0 ; } class Main { fn foo [perm, perm] (my self x : ^perm0_0 R[^perm0_1 R[Int]], y : ^perm0_1 R[Int]) -> () where move(^perm0_0), lent(^perm0_0), move(^perm0_1), lent(^perm0_1) { () ; } fn bar [perm, perm] (my self x : ^perm0_0 R[^perm0_1 R[Int]], y : ^perm0_1 R[Int]) -> () where move(^perm0_0), lent(^perm0_0), move(^perm0_1), lent(^perm0_1) { self . give . foo [^perm0_0, ^perm0_1] (x . give, y . lease) ; y . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `foo`
            2: check function body
            3: judgment `can_type_expr_as { expr: { () ; }, as_ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { () ; }, as_ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { () ; }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { () ; }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [() ;], ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: () ;, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "expr" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `parameter_permits_access { parameter: (), access: drop, place: @ fresh(0), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): (), x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 1 } }` failed at the following rule(s):
                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `liens { a: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): (), x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 1 } }` failed at the following rule(s):
                                             the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `some_lien { a: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): (), x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 1 } }` failed at the following rule(s):
                                                 the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                   expression evaluated to an empty collection: `parameters`"#]]);
}

/// See `escapes_ok`, but here we don't know that `B` is leased (and hence get an error).
/// In particular you can't convert e.g. `leased[y] my R[Int]`.
///
/// Equivalent in Rust would be
///
/// ```rust
/// fn foo(x: &mut T, y: T) { }
///
/// fn bar(x: &mut T, y: T) {
///     foo(x, &mut y);
/// }
/// ```
#[test]
fn escapes_err_not_leased() {
    check_program(&term(
        "
          class R[ty T] {
            value: T;
          }

          class Main {
            fn foo[perm A, perm B](my self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              move(A), lent(A),
            {
              ();
            }

            fn bar[perm A, perm B](my self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              move(A), lent(A),
            {
              self.give.foo[A, B](x.give, y.lease);
            }
          }
    ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class R [ty] { value : ^ty0_0 ; } class Main { fn foo [perm, perm] (my self x : ^perm0_0 R[^perm0_1 R[Int]], y : ^perm0_1 R[Int]) -> () where move(^perm0_0), lent(^perm0_0) { () ; } fn bar [perm, perm] (my self x : ^perm0_0 R[^perm0_1 R[Int]], y : ^perm0_1 R[Int]) -> () where move(^perm0_0), lent(^perm0_0) { self . give . foo [^perm0_0, ^perm0_1] (x . give, y . lease) ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `foo`
            2: check function body
            3: judgment `can_type_expr_as { expr: { () ; }, as_ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { () ; }, as_ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { () ; }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { () ; }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [() ;], ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: () ;, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "expr" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `parameter_permits_access { parameter: (), access: drop, place: @ fresh(0), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): (), x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 1 } }` failed at the following rule(s):
                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `liens { a: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): (), x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 1 } }` failed at the following rule(s):
                                             the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `some_lien { a: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): (), x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 1 } }` failed at the following rule(s):
                                                 the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                   expression evaluated to an empty collection: `parameters`"#]]);
}

/// Check that a `shared[d1, d2]` in parameters prohibits writes to `d1`.
#[test]
fn shared_d1_in_parameters() {
    check_program(&term(
        "
          class Pair[ty T] {
            value1: T;
            value2: T;
          }

          class Data { }

          class Main {
            fn main(my self) {
              let d1 = new Data();
              let d2 = new Data();
              let p = new Pair[shared[d1, d2] Data](d1.share, d2.share);
              d1 = new Data();
              let _keep_alive = p.give;
            }
          }
    ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Pair [ty] { value1 : ^ty0_0 ; value2 : ^ty0_0 ; } class Data { } class Main { fn main (my self) -> () { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [shared [d1, d2] Data] (d1 . share, d2 . share) ; d1 = new Data () ; let _keep_alive = p . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `main`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [shared [d1, d2] Data] (d1 . share, d2 . share) ; d1 = new Data () ; let _keep_alive = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [shared [d1, d2] Data] (d1 . share, d2 . share) ; d1 = new Data () ; let _keep_alive = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [shared [d1, d2] Data] (d1 . share, d2 . share) ; d1 = new Data () ; let _keep_alive = p . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [shared [d1, d2] Data] (d1 . share, d2 . share) ; d1 = new Data () ; let _keep_alive = p . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d1 = new Data () ;, let d2 = new Data () ;, let p = new Pair [shared [d1, d2] Data] (d1 . share, d2 . share) ;, d1 = new Data () ;, let _keep_alive = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let d2 = new Data () ;, let p = new Pair [shared [d1, d2] Data] (d1 . share, d2 . share) ;, d1 = new Data () ;, let _keep_alive = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let p = new Pair [shared [d1, d2] Data] (d1 . share, d2 . share) ;, d1 = new Data () ;, let _keep_alive = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: let p = new Pair [shared [d1, d2] Data] (d1 . share, d2 . share) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                             the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: new Pair [shared [d1, d2] Data] (d1 . share, d2 . share), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "new" failed at step #6 (src/file.rs:LL:CC) because
                                                   judgment `type_field_exprs_as { temp_var: @ fresh(0), exprs: [d1 . share, d2 . share], fields: [value1 : shared [d1, d2] Data ;, value2 : shared [d1, d2] Data ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair[shared [d1, d2] Data], d1: Data, d2: Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #3 (src/file.rs:LL:CC) because
                                                       judgment `type_expr { expr: d1 . share, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair[shared [d1, d2] Data], d1: Data, d2: Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {d2}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `access_permitted { access: share, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair[shared [d1, d2] Data], d1: Data, d2: Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {d2}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `env_permits_access { access: share, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair[shared [d1, d2] Data], d1: Data, d2: Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {d2}, traversed: {} } }` failed at the following rule(s):
                                                                 the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `parameters_permit_access { parameters: [Data], access: share, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair[shared [d1, d2] Data], d1: Data, d2: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                     the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `parameter_permits_access { parameter: Data, access: share, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair[shared [d1, d2] Data], d1: Data, d2: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `liens { a: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair[shared [d1, d2] Data], d1: Data, d2: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                             the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `some_lien { a: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair[shared [d1, d2] Data], d1: Data, d2: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                 the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   expression evaluated to an empty collection: `parameters`"#]]);
}

/// Check that a `shared[d1, d2]` in parameters prohibits writes to `d2`.
#[test]
fn shared_d2_in_parameters() {
    check_program(&term(
        "
          class Pair[ty T] {
            value1: T;
            value2: T;
          }

          class Data { }

          class Main {
            fn main(my self) {
              let d1 = new Data();
              let d2 = new Data();
              let p = new Pair[shared[d1, d2] Data](d1.share, d2.share);
              d2 = new Data();
              let _keep_alive = p.give;
            }
          }
    ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Pair [ty] { value1 : ^ty0_0 ; value2 : ^ty0_0 ; } class Data { } class Main { fn main (my self) -> () { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [shared [d1, d2] Data] (d1 . share, d2 . share) ; d2 = new Data () ; let _keep_alive = p . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `main`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [shared [d1, d2] Data] (d1 . share, d2 . share) ; d2 = new Data () ; let _keep_alive = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [shared [d1, d2] Data] (d1 . share, d2 . share) ; d2 = new Data () ; let _keep_alive = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [shared [d1, d2] Data] (d1 . share, d2 . share) ; d2 = new Data () ; let _keep_alive = p . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [shared [d1, d2] Data] (d1 . share, d2 . share) ; d2 = new Data () ; let _keep_alive = p . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d1 = new Data () ;, let d2 = new Data () ;, let p = new Pair [shared [d1, d2] Data] (d1 . share, d2 . share) ;, d2 = new Data () ;, let _keep_alive = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let d2 = new Data () ;, let p = new Pair [shared [d1, d2] Data] (d1 . share, d2 . share) ;, d2 = new Data () ;, let _keep_alive = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let p = new Pair [shared [d1, d2] Data] (d1 . share, d2 . share) ;, d2 = new Data () ;, let _keep_alive = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: let p = new Pair [shared [d1, d2] Data] (d1 . share, d2 . share) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                             the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: new Pair [shared [d1, d2] Data] (d1 . share, d2 . share), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "new" failed at step #6 (src/file.rs:LL:CC) because
                                                   judgment `type_field_exprs_as { temp_var: @ fresh(0), exprs: [d1 . share, d2 . share], fields: [value1 : shared [d1, d2] Data ;, value2 : shared [d1, d2] Data ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair[shared [d1, d2] Data], d1: Data, d2: Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #3 (src/file.rs:LL:CC) because
                                                       judgment `type_expr { expr: d1 . share, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair[shared [d1, d2] Data], d1: Data, d2: Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {d2}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `access_permitted { access: share, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair[shared [d1, d2] Data], d1: Data, d2: Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {d2}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `env_permits_access { access: share, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair[shared [d1, d2] Data], d1: Data, d2: Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {d2}, traversed: {} } }` failed at the following rule(s):
                                                                 the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `parameters_permit_access { parameters: [Data], access: share, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair[shared [d1, d2] Data], d1: Data, d2: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                     the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `parameter_permits_access { parameter: Data, access: share, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair[shared [d1, d2] Data], d1: Data, d2: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `liens { a: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair[shared [d1, d2] Data], d1: Data, d2: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                             the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `some_lien { a: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair[shared [d1, d2] Data], d1: Data, d2: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                 the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   expression evaluated to an empty collection: `parameters`"#]]);
}

/// Check that a `leased[d1, d2]` in parameters prohibits reads from `d1`.
#[test]
fn leased_d1_in_parameters() {
    check_program(&term(
        "
          class Pair[ty T] {
            value1: T;
            value2: T;
          }

          class Data { }

          class Main {
            fn main(my self) {
              let d1 = new Data();
              let d2 = new Data();
              let p = new Pair[leased[d1, d2] Data](d1.lease, d2.lease);
              d1.share;
              let _keep_alive = p.give;
            }
          }
    ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Pair [ty] { value1 : ^ty0_0 ; value2 : ^ty0_0 ; } class Data { } class Main { fn main (my self) -> () { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [leased [d1, d2] Data] (d1 . lease, d2 . lease) ; d1 . share ; let _keep_alive = p . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `main`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [leased [d1, d2] Data] (d1 . lease, d2 . lease) ; d1 . share ; let _keep_alive = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [leased [d1, d2] Data] (d1 . lease, d2 . lease) ; d1 . share ; let _keep_alive = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [leased [d1, d2] Data] (d1 . lease, d2 . lease) ; d1 . share ; let _keep_alive = p . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [leased [d1, d2] Data] (d1 . lease, d2 . lease) ; d1 . share ; let _keep_alive = p . give ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d1 = new Data () ;, let d2 = new Data () ;, let p = new Pair [leased [d1, d2] Data] (d1 . lease, d2 . lease) ;, d1 . share ;, let _keep_alive = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let d2 = new Data () ;, let p = new Pair [leased [d1, d2] Data] (d1 . lease, d2 . lease) ;, d1 . share ;, let _keep_alive = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let p = new Pair [leased [d1, d2] Data] (d1 . lease, d2 . lease) ;, d1 . share ;, let _keep_alive = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: let p = new Pair [leased [d1, d2] Data] (d1 . lease, d2 . lease) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {d1, p}, traversed: {} } }` failed at the following rule(s):
                                             the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: new Pair [leased [d1, d2] Data] (d1 . lease, d2 . lease), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {d1}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "new" failed at step #6 (src/file.rs:LL:CC) because
                                                   judgment `type_field_exprs_as { temp_var: @ fresh(0), exprs: [d1 . lease, d2 . lease], fields: [value1 : leased [d1, d2] Data ;, value2 : leased [d1, d2] Data ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair[leased [d1, d2] Data], d1: Data, d2: Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {d1}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #3 (src/file.rs:LL:CC) because
                                                       judgment `type_expr { expr: d1 . lease, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair[leased [d1, d2] Data], d1: Data, d2: Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {d1, d2}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `access_permitted { access: lease, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair[leased [d1, d2] Data], d1: Data, d2: Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {d1, d2}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `env_permits_access { access: lease, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair[leased [d1, d2] Data], d1: Data, d2: Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {d1, d2}, traversed: {} } }` failed at the following rule(s):
                                                                 the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `parameters_permit_access { parameters: [Data, Data], access: lease, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair[leased [d1, d2] Data], d1: Data, d2: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                     the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `parameter_permits_access { parameter: Data, access: lease, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair[leased [d1, d2] Data], d1: Data, d2: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `liens { a: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair[leased [d1, d2] Data], d1: Data, d2: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                             the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `some_lien { a: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair[leased [d1, d2] Data], d1: Data, d2: Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                 the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   expression evaluated to an empty collection: `parameters`"#]]);
}
