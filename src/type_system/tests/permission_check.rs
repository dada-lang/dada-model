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
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let i = foo . i . share ;, bar . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: leased [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: let i = foo . i . share ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: leased [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: foo . i . share, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: leased [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: share, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: leased [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `env_permits_access { access: share, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: leased [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `parameters_permit_access { parameters: [leased [foo] Foo], access: share, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: leased [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `parameter_permits_access { parameter: leased [foo] Foo, access: share, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: leased [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `lien_permit_access { lien: leased(foo), access: share, accessed_place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: leased [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "leased" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `leased_place_permits_access { leased_place: foo, access: share, accessed_place: foo . i }` failed at the following rule(s):
                                                                             the rule "lease-mutation" failed at step #0 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
                                                                                 &accessed_place = foo . i
                                                                                 &leased_place = foo"#]],
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
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let i = foo . i . lease ;, bar . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: shared [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: let i = foo . i . lease ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: shared [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: foo . i . lease, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: shared [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: lease, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: shared [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `env_permits_access { access: lease, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: shared [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `parameters_permit_access { parameters: [shared [foo] Foo], access: lease, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: shared [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `parameter_permits_access { parameter: shared [foo] Foo, access: lease, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: shared [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `lien_permit_access { lien: shared(foo), access: lease, accessed_place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: shared [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "shared" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `shared_place_permits_access { shared_place: foo, access: lease, accessed_place: foo . i }` failed at the following rule(s):
                                                                             the rule "share-mutation" failed at step #0 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
                                                                                 &accessed_place = foo . i
                                                                                 &shared_place = foo"#]],
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
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let i = foo . i . give ;, bar . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: shared [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: let i = foo . i . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: shared [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: foo . i . give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: shared [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "give place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: give, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: shared [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `env_permits_access { access: give, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: shared [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `parameters_permit_access { parameters: [shared [foo] Foo], access: give, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: shared [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `parameter_permits_access { parameter: shared [foo] Foo, access: give, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: shared [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `lien_permit_access { lien: shared(foo), access: give, accessed_place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: shared [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "shared" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `shared_place_permits_access { shared_place: foo, access: give, accessed_place: foo . i }` failed at the following rule(s):
                                                                             the rule "share-give" failed at step #0 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `place_disjoint_from_or_prefix_of(&accessed_place, &shared_place)`
                                                                                 &accessed_place = foo . i
                                                                                 &shared_place = foo"#]],
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
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let r = q . share ;, let i = p . i . share ;, r . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo, q: leased [p] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let i = p . i . share ;, r . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo, q: leased [p] Foo, r: shared [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: let i = p . i . share ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo, q: leased [p] Foo, r: shared [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: p . i . share, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo, q: leased [p] Foo, r: shared [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: share, place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo, q: leased [p] Foo, r: shared [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `env_permits_access { access: share, place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo, q: leased [p] Foo, r: shared [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `parameters_permit_access { parameters: [shared [q] Foo], access: share, place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo, q: leased [p] Foo, r: shared [q] Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `parameter_permits_access { parameter: shared [q] Foo, access: share, place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo, q: leased [p] Foo, r: shared [q] Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `"flat_map"` failed at the following rule(s):
                                                                         failed at (src/file.rs:LL:CC) because
                                                                           judgment `lien_permit_access { lien: leased(p), access: share, accessed_place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo, q: leased [p] Foo, r: shared [q] Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "leased" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `leased_place_permits_access { leased_place: p, access: share, accessed_place: p . i }` failed at the following rule(s):
                                                                                 the rule "lease-mutation" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
                                                                                     &accessed_place = p . i
                                                                                     &leased_place = p"#]])
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
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let r : shared [q] Foo = q . share ;, let i : shared [p . i] Data = p . i . share ;, r . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo, q: leased [p] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let i : shared [p . i] Data = p . i . share ;, r . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo, q: leased [p] Foo, r: shared [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: let i : shared [p . i] Data = p . i . share ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo, q: leased [p] Foo, r: shared [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr_as { expr: p . i . share, as_ty: shared [p . i] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo, q: leased [p] Foo, r: shared [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `type_expr { expr: p . i . share, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo, q: leased [p] Foo, r: shared [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `access_permitted { access: share, place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo, q: leased [p] Foo, r: shared [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `env_permits_access { access: share, place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo, q: leased [p] Foo, r: shared [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                                 the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `parameters_permit_access { parameters: [shared [q] Foo], access: share, place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo, q: leased [p] Foo, r: shared [q] Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `parameter_permits_access { parameter: shared [q] Foo, access: share, place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo, q: leased [p] Foo, r: shared [q] Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                           judgment `"flat_map"` failed at the following rule(s):
                                                                             failed at (src/file.rs:LL:CC) because
                                                                               judgment `lien_permit_access { lien: leased(p), access: share, accessed_place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo, q: leased [p] Foo, r: shared [q] Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "leased" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `leased_place_permits_access { leased_place: p, access: share, accessed_place: p . i }` failed at the following rule(s):
                                                                                     the rule "lease-mutation" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
                                                                                         &accessed_place = p . i
                                                                                         &leased_place = p"#]])
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
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [me . a = data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, me: shared [self] Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: me . a = data . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, me: shared [self] Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "reassign" failed at step #3 (src/file.rs:LL:CC) because
                                           judgment `prove_is_move { a: shared [self] Pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, @ fresh(0): Data, data: my Data, me: shared [self] Pair}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                             the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: move(shared [self] Pair), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, @ fresh(0): Data, data: my Data, me: shared [self] Pair}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                   pattern `true` did not match value `false`"#]])
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
                                     the rule "reassign" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `prove_is_move { a: our Pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, @ fresh(0): Data, data: my Data, pair: our Pair}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                         the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `prove_predicate { predicate: move(our Pair), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, @ fresh(0): Data, data: my Data, pair: our Pair}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                               pattern `true` did not match value `false`"#]])
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
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: shared [owner1] Data, b: shared [owner] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                           judgment `sub_perms { a: shared [owner1], b: shared [owner], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `prove_is_move { a: shared [owner1], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `prove_predicate { predicate: move(shared [owner1]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                       pattern `true` did not match value `false`
                             the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `prove_is_move { a: shared [owner1], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `prove_predicate { predicate: move(shared [owner1]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                       pattern `true` did not match value `false`
                             the rule "our-sub-copy" failed at step #1 (src/file.rs:LL:CC) because
                               judgment `prove_is_owned { a: shared [owner1], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `prove_predicate { predicate: owned(shared [owner1]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                       pattern `true` did not match value `false`
                             the rule "simplify-lhs" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `simplify_perm { perm: LeafPerms { leaves: [shared [owner1]] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "dead_copy" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `"flat_map"` failed at the following rule(s):
                                     failed at (src/file.rs:LL:CC) because
                                       judgment `prove_is_copy { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `prove_predicate { predicate: copy(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                               pattern `true` did not match value `false`
                                 the rule "dead_shared-up" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `"flat_map"` failed at the following rule(s):
                                     failed at (src/file.rs:LL:CC) because
                                       judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                               pattern `true` did not match value `false`
                             the rule "simplify-rhs" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `simplify_perm { perm: LeafPerms { leaves: [shared [owner]] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "dead_copy" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `"flat_map"` failed at the following rule(s):
                                     failed at (src/file.rs:LL:CC) because
                                       judgment `prove_is_copy { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `prove_predicate { predicate: copy(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                               pattern `true` did not match value `false`
                                 the rule "dead_shared-up" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `"flat_map"` failed at the following rule(s):
                                     failed at (src/file.rs:LL:CC) because
                                       judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                               pattern `true` did not match value `false`
                             the rule "sub_perms_relative" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `sub_perm_heads { a: LeafPerms { leaves: [shared [owner1]] }, b: LeafPerms { leaves: [shared [owner]] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "shared-shared" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `sub_place_perms { places_a: {owner1}, tail_a: my, places_b: {owner}, tail_b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "places-places" failed at step #0 (src/file.rs:LL:CC) because
                                       condition evaluted to false: `all_prefix_of_any(&places_a, &places_b)`
                                         &places_a = {owner1}
                                         &places_b = {owner}
                                 the rule "simplify-lhs" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `simplify_perm { perm: LeafPerms { leaves: [shared [owner1]] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "dead_copy" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `"flat_map"` failed at the following rule(s):
                                         failed at (src/file.rs:LL:CC) because
                                           judgment `prove_is_copy { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: copy(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                   pattern `true` did not match value `false`
                                     the rule "dead_shared-up" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `"flat_map"` failed at the following rule(s):
                                         failed at (src/file.rs:LL:CC) because
                                           judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                   pattern `true` did not match value `false`
                                 the rule "simplify-rhs" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `simplify_perm { perm: LeafPerms { leaves: [shared [owner]] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "dead_copy" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `"flat_map"` failed at the following rule(s):
                                         failed at (src/file.rs:LL:CC) because
                                           judgment `prove_is_copy { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: copy(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                   pattern `true` did not match value `false`
                                     the rule "dead_shared-up" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `"flat_map"` failed at the following rule(s):
                                         failed at (src/file.rs:LL:CC) because
                                           judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: shared [owner1] Data, data: shared [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                   pattern `true` did not match value `false`"#]])
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
            1: check method named `bar`
            2: check function body
            3: judgment `can_type_expr_as { expr: { self . give . foo [!perm_0, !perm_1] (x . give, y . lease) ; y . give ; }, as_ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { self . give . foo [!perm_0, !perm_1] (x . give, y . lease) ; y . give ; }, as_ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { self . give . foo [!perm_0, !perm_1] (x . give, y . lease) ; y . give ; }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { self . give . foo [!perm_0, !perm_1] (x . give, y . lease) ; y . give ; }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [self . give . foo [!perm_0, !perm_1] (x . give, y . lease) ;, y . give ;], ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: self . give . foo [!perm_0, !perm_1] (x . give, y . lease) ;, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {y}, traversed: {} } }` failed at the following rule(s):
                                     the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `type_expr { expr: self . give . foo [!perm_0, !perm_1] (x . give, y . lease), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {y}, traversed: {} } }` failed at the following rule(s):
                                         the rule "call" failed at step #8 (src/file.rs:LL:CC) because
                                           judgment `type_method_arguments_as { exprs: [x . give, y . lease], input_names: [x, y], input_tys: [!perm_0 R[!perm_1 R[Int]], !perm_1 R[Int]], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 1 }, live_after: LivePlaces { accessed: {y}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #7 (src/file.rs:LL:CC) because
                                               judgment `type_method_arguments_as { exprs: [y . lease], input_names: [y], input_tys: [!perm_1 R[Int]], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 2 }, live_after: LivePlaces { accessed: {y}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "cons" failed at step #5 (src/file.rs:LL:CC) because
                                                   judgment `sub { a: leased [y] R[Int], b: !perm_1 R[Int], live_after: LivePlaces { accessed: {y}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                     the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                       judgment `sub_perms { a: leased [y], b: !perm_1, live_after: LivePlaces { accessed: {y}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                         the rule "my-sub-copy" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_owned { a: leased [y], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                             the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: owned(leased [y]), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   pattern `true` did not match value `false`
                                                         the rule "my-sub-owned" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_owned { a: leased [y], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                             the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: owned(leased [y]), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   pattern `true` did not match value `false`
                                                         the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_copy { a: leased [y], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                             the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: copy(leased [y]), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), move(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   pattern `true` did not match value `false`"#]]);
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
            1: check method named `bar`
            2: check function body
            3: judgment `can_type_expr_as { expr: { self . give . foo [!perm_0, !perm_1] (x . give, y . lease) ; }, as_ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { self . give . foo [!perm_0, !perm_1] (x . give, y . lease) ; }, as_ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { self . give . foo [!perm_0, !perm_1] (x . give, y . lease) ; }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { self . give . foo [!perm_0, !perm_1] (x . give, y . lease) ; }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [self . give . foo [!perm_0, !perm_1] (x . give, y . lease) ;], ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: self . give . foo [!perm_0, !perm_1] (x . give, y . lease) ;, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `type_expr { expr: self . give . foo [!perm_0, !perm_1] (x . give, y . lease), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "call" failed at step #8 (src/file.rs:LL:CC) because
                                           judgment `type_method_arguments_as { exprs: [x . give, y . lease], input_names: [x, y], input_tys: [!perm_0 R[!perm_1 R[Int]], !perm_1 R[Int]], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #7 (src/file.rs:LL:CC) because
                                               judgment `type_method_arguments_as { exprs: [y . lease], input_names: [y], input_tys: [!perm_1 R[Int]], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 2 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "cons" failed at step #5 (src/file.rs:LL:CC) because
                                                   judgment `sub { a: leased [y] R[Int], b: !perm_1 R[Int], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                     the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                       judgment `sub_perms { a: leased [y], b: !perm_1, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                         the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_move { a: leased [y], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                             the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: move(leased [y]), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   pattern `true` did not match value `false`
                                                         the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_move { a: leased [y], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                             the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: move(leased [y]), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   pattern `true` did not match value `false`
                                                         the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_copy { a: leased [y], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                             the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: copy(leased [y]), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   pattern `true` did not match value `false`
                                                         the rule "simplify-lhs" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `simplify_perm { perm: LeafPerms { leaves: [leased [y]] }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "dead_copy" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `"flat_map"` failed at the following rule(s):
                                                                 failed at (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_copy { a: !perm_1, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                     the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: copy(!perm_1), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`
                                                             the rule "dead_leased-up" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `"flat_map"` failed at the following rule(s):
                                                                 failed at (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_lent { a: !perm_1, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                     the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: lent(!perm_1), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`
                                                         the rule "sub_perms_relative" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `sub_perm_heads { a: LeafPerms { leaves: [leased [y]] }, b: LeafPerms { leaves: [!perm_1] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                             the rule "simplify-lhs" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `simplify_perm { perm: LeafPerms { leaves: [leased [y]] }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                 the rule "dead_copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `"flat_map"` failed at the following rule(s):
                                                                     failed at (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_copy { a: !perm_1, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                         the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: copy(!perm_1), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`
                                                                 the rule "dead_leased-up" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `"flat_map"` failed at the following rule(s):
                                                                     failed at (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_lent { a: !perm_1, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                         the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: lent(!perm_1), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): leased [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`"#]]);
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
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [d1 = new Data () ;, let _keep_alive = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data, p: Pair[shared [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: d1 = new Data () ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data, p: Pair[shared [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "reassign" failed at step #4 (src/file.rs:LL:CC) because
                                                   judgment `env_permits_access { access: lease, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Data, d1: Data, d2: Data, p: Pair[shared [d1, d2] Data]}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `parameters_permit_access { parameters: [Pair[shared [d1, d2] Data]], access: lease, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Data, d1: Data, d2: Data, p: Pair[shared [d1, d2] Data]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                         the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `parameter_permits_access { parameter: Pair[shared [d1, d2] Data], access: lease, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Data, d1: Data, d2: Data, p: Pair[shared [d1, d2] Data]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                             the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `lien_permit_access { lien: shared(d1), access: lease, accessed_place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Data, d1: Data, d2: Data, p: Pair[shared [d1, d2] Data]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                 the rule "shared" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `shared_place_permits_access { shared_place: d1, access: lease, accessed_place: d1 }` failed at the following rule(s):
                                                                     the rule "share-mutation" failed at step #0 (src/file.rs:LL:CC) because
                                                                       condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
                                                                         &accessed_place = d1
                                                                         &shared_place = d1"#]]);
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
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [d2 = new Data () ;, let _keep_alive = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data, p: Pair[shared [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: d2 = new Data () ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data, p: Pair[shared [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "reassign" failed at step #4 (src/file.rs:LL:CC) because
                                                   judgment `env_permits_access { access: lease, place: d2, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Data, d1: Data, d2: Data, p: Pair[shared [d1, d2] Data]}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `parameters_permit_access { parameters: [Pair[shared [d1, d2] Data]], access: lease, place: d2, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Data, d1: Data, d2: Data, p: Pair[shared [d1, d2] Data]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                         the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `parameter_permits_access { parameter: Pair[shared [d1, d2] Data], access: lease, place: d2, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Data, d1: Data, d2: Data, p: Pair[shared [d1, d2] Data]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                             the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `"flat_map"` failed at the following rule(s):
                                                                 failed at (src/file.rs:LL:CC) because
                                                                   judgment `lien_permit_access { lien: shared(d2), access: lease, accessed_place: d2, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Data, d1: Data, d2: Data, p: Pair[shared [d1, d2] Data]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                     the rule "shared" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `shared_place_permits_access { shared_place: d2, access: lease, accessed_place: d2 }` failed at the following rule(s):
                                                                         the rule "share-mutation" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
                                                                             &accessed_place = d2
                                                                             &shared_place = d2"#]]);
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
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [d1 . share ;, let _keep_alive = p . give ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data, p: Pair[leased [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: d1 . share ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data, p: Pair[leased [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: d1 . share, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data, p: Pair[leased [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: share, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data, p: Pair[leased [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `env_permits_access { access: share, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data, p: Pair[leased [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `parameters_permit_access { parameters: [Pair[leased [d1, d2] Data]], access: share, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data, p: Pair[leased [d1, d2] Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `parameter_permits_access { parameter: Pair[leased [d1, d2] Data], access: share, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data, p: Pair[leased [d1, d2] Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `lien_permit_access { lien: leased(d1), access: share, accessed_place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data, p: Pair[leased [d1, d2] Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "leased" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `leased_place_permits_access { leased_place: d1, access: share, accessed_place: d1 }` failed at the following rule(s):
                                                                             the rule "lease-mutation" failed at step #0 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
                                                                                 &accessed_place = d1
                                                                                 &leased_place = d1"#]]);
}
