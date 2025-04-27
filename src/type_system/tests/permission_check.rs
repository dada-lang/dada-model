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
                        let bar = foo.mut;
                        let i = foo.i.ref;
                        bar.move;
                        ();
                    }
                }
            ",
        ),
    ).assert_err(
        expect_test::expect![[r#"
            check program `class Data { } class Foo { i : Data ; } class Main { fn main (my self) -> () { let foo = new Foo (new Data ()) ; let bar = foo . mut ; let i = foo . i . ref ; bar . move ; () ; } }`

            Caused by:
                0: check class named `Main`
                1: check method named `main`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; let bar = foo . mut ; let i = foo . i . ref ; bar . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; let bar = foo . mut ; let i = foo . i . ref ; bar . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; let bar = foo . mut ; let i = foo . i . ref ; bar . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (new Data ()) ; let bar = foo . mut ; let i = foo . i . ref ; bar . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, let bar = foo . mut ;, let i = foo . i . ref ;, bar . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let bar = foo . mut ;, let i = foo . i . ref ;, bar . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let i = foo . i . ref ;, bar . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: mut [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: let i = foo . i . ref ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: mut [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: foo . i . ref, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: mut [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "ref|mut place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: ref, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: mut [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `env_permits_access { access: ref, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: mut [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `parameters_permit_access { parameters: [mut [foo] Foo], access: ref, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: mut [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `parameter_permits_access { parameter: mut [foo] Foo, access: ref, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: mut [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `lien_permit_access { lien: mt(foo), access: ref, accessed_place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: mut [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "mut'd" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `mut_place_permits_access { leased_place: foo, access: ref, accessed_place: foo . i }` failed at the following rule(s):
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
                    let bar = foo.ref;
                    let i = foo.i.ref;
                    bar.move;
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
                    let bar = foo.ref;
                    let i = foo.i.mut;
                    bar.move;
                    ();
                }
            }
        ",
        ),
    ).assert_err(
        expect_test::expect![[r#"
            check program `class Data { } class Foo { i : Data ; } class Main { fn main (my self) -> () { let foo = new Foo (new Data ()) ; let bar = foo . ref ; let i = foo . i . mut ; bar . move ; () ; } }`

            Caused by:
                0: check class named `Main`
                1: check method named `main`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; let bar = foo . ref ; let i = foo . i . mut ; bar . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; let bar = foo . ref ; let i = foo . i . mut ; bar . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; let bar = foo . ref ; let i = foo . i . mut ; bar . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (new Data ()) ; let bar = foo . ref ; let i = foo . i . mut ; bar . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, let bar = foo . ref ;, let i = foo . i . mut ;, bar . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let bar = foo . ref ;, let i = foo . i . mut ;, bar . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let i = foo . i . mut ;, bar . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: let i = foo . i . mut ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: foo . i . mut, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "ref|mut place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: mut, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `env_permits_access { access: mut, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `parameters_permit_access { parameters: [ref [foo] Foo], access: mut, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `parameter_permits_access { parameter: ref [foo] Foo, access: mut, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `lien_permit_access { lien: rf(foo), access: mut, accessed_place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "ref'd" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `ref_place_permits_access { shared_place: foo, access: mut, accessed_place: foo . i }` failed at the following rule(s):
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
                    let bar = foo.ref;
                    let i = foo.i.move;
                    bar.move;
                    ();
                }
            }
        ",
        ),
    ).assert_err(
        expect_test::expect![[r#"
            check program `class Data { } class Foo { i : Data ; } class Main { fn main (my self) -> () { let foo = new Foo (new Data ()) ; let bar = foo . ref ; let i = foo . i . move ; bar . move ; () ; } }`

            Caused by:
                0: check class named `Main`
                1: check method named `main`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; let bar = foo . ref ; let i = foo . i . move ; bar . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; let bar = foo . ref ; let i = foo . i . move ; bar . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; let bar = foo . ref ; let i = foo . i . move ; bar . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (new Data ()) ; let bar = foo . ref ; let i = foo . i . move ; bar . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, let bar = foo . ref ;, let i = foo . i . move ;, bar . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let bar = foo . ref ;, let i = foo . i . move ;, bar . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let i = foo . i . move ;, bar . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: let i = foo . i . move ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: foo . i . move, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "move place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: move, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `env_permits_access { access: move, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `parameters_permit_access { parameters: [ref [foo] Foo], access: move, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `parameter_permits_access { parameter: ref [foo] Foo, access: move, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `lien_permit_access { lien: rf(foo), access: move, accessed_place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: ref [foo] Foo, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "ref'd" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `ref_place_permits_access { shared_place: foo, access: move, accessed_place: foo . i }` failed at the following rule(s):
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
                        let bar = foo.mut;
                        bar.move;
                        let i = foo.i.ref;
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
                        let bar = foo.mut;
                        let i = foo.i.ref;
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
                        let q = p.mut;
                        let r = q.ref;
                        let i = p.i.ref;
                        r.move;
                        ();
                    }
                }
            ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Foo { i : Data ; } class Main { fn main (my self) -> () { let p = new Foo (new Data ()) ; let q = p . mut ; let r = q . ref ; let i = p . i . ref ; r . move ; () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `main`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let p = new Foo (new Data ()) ; let q = p . mut ; let r = q . ref ; let i = p . i . ref ; r . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let p = new Foo (new Data ()) ; let q = p . mut ; let r = q . ref ; let i = p . i . ref ; r . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let p = new Foo (new Data ()) ; let q = p . mut ; let r = q . ref ; let i = p . i . ref ; r . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let p = new Foo (new Data ()) ; let q = p . mut ; let r = q . ref ; let i = p . i . ref ; r . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let p = new Foo (new Data ()) ;, let q = p . mut ;, let r = q . ref ;, let i = p . i . ref ;, r . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let q = p . mut ;, let r = q . ref ;, let i = p . i . ref ;, r . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let r = q . ref ;, let i = p . i . ref ;, r . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo, q: mut [p] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let i = p . i . ref ;, r . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: let i = p . i . ref ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: p . i . ref, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "ref|mut place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: ref, place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `env_permits_access { access: ref, place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `parameters_permit_access { parameters: [ref [q] Foo], access: ref, place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `parameter_permits_access { parameter: ref [q] Foo, access: ref, place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `"flat_map"` failed at the following rule(s):
                                                                         failed at (src/file.rs:LL:CC) because
                                                                           judgment `lien_permit_access { lien: mt(p), access: ref, accessed_place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "mut'd" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `mut_place_permits_access { leased_place: p, access: ref, accessed_place: p . i }` failed at the following rule(s):
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
                        let q: mut[p] Foo = p.mut;
                        let r: ref[q] Foo = q.ref;
                        let i: ref[p.i] Data = p.i.ref;
                        r.move;
                        ();
                    }
                }
            ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Foo { i : Data ; } class Main { fn main (my self) -> () { let p : my Foo = new Foo (new Data ()) ; let q : mut [p] Foo = p . mut ; let r : ref [q] Foo = q . ref ; let i : ref [p . i] Data = p . i . ref ; r . move ; () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `main`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let p : my Foo = new Foo (new Data ()) ; let q : mut [p] Foo = p . mut ; let r : ref [q] Foo = q . ref ; let i : ref [p . i] Data = p . i . ref ; r . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let p : my Foo = new Foo (new Data ()) ; let q : mut [p] Foo = p . mut ; let r : ref [q] Foo = q . ref ; let i : ref [p . i] Data = p . i . ref ; r . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let p : my Foo = new Foo (new Data ()) ; let q : mut [p] Foo = p . mut ; let r : ref [q] Foo = q . ref ; let i : ref [p . i] Data = p . i . ref ; r . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let p : my Foo = new Foo (new Data ()) ; let q : mut [p] Foo = p . mut ; let r : ref [q] Foo = q . ref ; let i : ref [p . i] Data = p . i . ref ; r . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let p : my Foo = new Foo (new Data ()) ;, let q : mut [p] Foo = p . mut ;, let r : ref [q] Foo = q . ref ;, let i : ref [p . i] Data = p . i . ref ;, r . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let q : mut [p] Foo = p . mut ;, let r : ref [q] Foo = q . ref ;, let i : ref [p . i] Data = p . i . ref ;, r . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let r : ref [q] Foo = q . ref ;, let i : ref [p . i] Data = p . i . ref ;, r . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo, q: mut [p] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let i : ref [p . i] Data = p . i . ref ;, r . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: let i : ref [p . i] Data = p . i . ref ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr_as { expr: p . i . ref, as_ty: ref [p . i] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `type_expr { expr: p . i . ref, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "ref|mut place" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `access_permitted { access: ref, place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `env_permits_access { access: ref, place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {r}, traversed: {} } }` failed at the following rule(s):
                                                                 the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `parameters_permit_access { parameters: [ref [q] Foo], access: ref, place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `parameter_permits_access { parameter: ref [q] Foo, access: ref, place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                           judgment `"flat_map"` failed at the following rule(s):
                                                                             failed at (src/file.rs:LL:CC) because
                                                                               judgment `lien_permit_access { lien: mt(p), access: ref, accessed_place: p . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, p: my Foo, q: mut [p] Foo, r: ref [q] Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "mut'd" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `mut_place_permits_access { leased_place: p, access: ref, accessed_place: p . i }` failed at the following rule(s):
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

                fn method(my self, data: mut[self] Data) {
                  self.a.mut;
                  data.move;
                  ();
                }
            }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { a : Data ; b : Data ; fn method (my self data : mut [self] Data) -> () { self . a . mut ; data . move ; () ; } }`

        Caused by:
            0: check class named `Pair`
            1: check method named `method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { self . a . mut ; data . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { self . a . mut ; data . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { self . a . mut ; data . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { self . a . mut ; data . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [self . a . mut ;, data . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: self . a . mut ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                     the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `type_expr { expr: self . a . mut, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                         the rule "ref|mut place" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `access_permitted { access: mut, place: self . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                             the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `env_permits_access { access: mut, place: self . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `parameters_permit_access { parameters: [mut [self] Data], access: mut, place: self . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `parameter_permits_access { parameter: mut [self] Data, access: mut, place: self . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `lien_permit_access { lien: mt(self), access: mut, accessed_place: self . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: mut [self] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "mut'd" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `mut_place_permits_access { leased_place: self, access: mut, accessed_place: self . a }` failed at the following rule(s):
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
                  let me = self.ref;
                  me.a = data.move;
                  ();
                }
            }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { a : Data ; b : Data ; fn method (my self data : my Data) -> () { let me = self . ref ; me . a = data . move ; () ; } }`

        Caused by:
            0: check class named `Pair`
            1: check method named `method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let me = self . ref ; me . a = data . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let me = self . ref ; me . a = data . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let me = self . ref ; me . a = data . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let me = self . ref ; me . a = data . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let me = self . ref ;, me . a = data . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [me . a = data . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, me: ref [self] Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: me . a = data . move ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, me: ref [self] Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "reassign" failed at step #3 (src/file.rs:LL:CC) because
                                           judgment `prove_is_unique { a: ref [self] Pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, @ fresh(0): Data, data: my Data, me: ref [self] Pair}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                             the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: unique(ref [self] Pair), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, @ fresh(0): Data, data: my Data, me: ref [self] Pair}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
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
                  pair.a = data.move;
                  ();
                }
            }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { a : Data ; b : Data ; fn method (my self pair : our Pair, data : my Data) -> () { pair . a = data . move ; () ; } }`

        Caused by:
            0: check class named `Pair`
            1: check method named `method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { pair . a = data . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, pair: our Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { pair . a = data . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, pair: our Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { pair . a = data . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, pair: our Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { pair . a = data . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, pair: our Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [pair . a = data . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, pair: our Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: pair . a = data . move ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: my Data, pair: our Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "reassign" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `prove_is_unique { a: our Pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, @ fresh(0): Data, data: my Data, pair: our Pair}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                         the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `prove_predicate { predicate: unique(our Pair), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, @ fresh(0): Data, data: my Data, pair: our Pair}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
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
                  let me = self.mut;
                  me.a = data.move;
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
                  let d: our Data = data.move;
                  let e: our Data = data.move;
                  let f: our Data = data.move;
                  d.move;
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

                fn method(my self, owner: my Data, data: ref[owner] Data) -> ref[owner] Data {
                  let d: ref[owner] Data = data.move;
                  let e: ref[owner] Data = data.move;
                  let f: ref[owner] Data = data.move;
                  d.move;
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

                fn method(my self, owner: my Data, data: ref[owner] Data) -> ref[owner] Data {
                  let d: ref[owner] Data = data.move;
                  let owner1: my Data = owner.move;
                  d.move;
                }
            }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { a : Data ; b : Data ; fn method (my self owner : my Data, data : ref [owner] Data) -> ref [owner] Data { let d : ref [owner] Data = data . move ; let owner1 : my Data = owner . move ; d . move ; } }`

        Caused by:
            0: check class named `Pair`
            1: check method named `method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d : ref [owner] Data = data . move ; let owner1 : my Data = owner . move ; d . move ; }, as_ty: ref [owner] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: ref [owner] Data, owner: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d : ref [owner] Data = data . move ; let owner1 : my Data = owner . move ; d . move ; }, as_ty: ref [owner] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: ref [owner] Data, owner: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: ref [owner1] Data, b: ref [owner] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                           judgment `sub_perms_both_ways { a: ref [owner1], b: ref [owner], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub-perms" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `sub_perms { a: ref [owner1], b: ref [owner], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "dead left" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `dead_perm { acc: rf, place: owner1, tail: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "dead ref" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                               pattern `true` did not match value `false`
                                 the rule "expand left" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_perms { a: ref [owner1] my, b: ref [owner], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "dead left" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `dead_perm { acc: rf, place: owner1, tail: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "dead ref" failed at step #3 (src/file.rs:LL:CC) because
                                           judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                   pattern `true` did not match value `false`
                                     the rule "expand right" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `sub_perms { a: ref [owner1] my, b: ref [owner] my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "dead left" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `dead_perm { acc: rf, place: owner1, tail: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "dead ref" failed at step #3 (src/file.rs:LL:CC) because
                                               judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                       pattern `true` did not match value `false`
                                 the rule "expand right" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_perms { a: ref [owner1], b: ref [owner] my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "dead left" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `dead_perm { acc: rf, place: owner1, tail: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "dead ref" failed at step #3 (src/file.rs:LL:CC) because
                                           judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                   pattern `true` did not match value `false`
                                     the rule "expand left" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `sub_perms { a: ref [owner1] my, b: ref [owner] my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "dead left" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `dead_perm { acc: rf, place: owner1, tail: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "dead ref" failed at step #3 (src/file.rs:LL:CC) because
                                               judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, d: ref [owner1] Data, data: ref [owner1] Data, owner: my Data, owner1: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
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
              unique(A), lent(A),
              unique(B), lent(B),
            {
              ();
            }

            fn bar[perm A, perm B](my self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              unique(A), lent(A),
              unique(B), lent(B),
            {
              self.move.foo[A, B](x.move, y.mut);
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
              unique(A), lent(A),
              unique(B), lent(B),
            {
              ();
            }

            fn bar[perm A, perm B](my self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              unique(A), lent(A),
              unique(B), lent(B),
            {
              self.move.foo[A, B](x.move, y.mut);
              y.move;
            }
          }
    ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class R [ty] { value : ^ty0_0 ; } class Main { fn foo [perm, perm] (my self x : ^perm0_0 R[^perm0_1 R[Int]], y : ^perm0_1 R[Int]) -> () where unique(^perm0_0), lent(^perm0_0), unique(^perm0_1), lent(^perm0_1) { () ; } fn bar [perm, perm] (my self x : ^perm0_0 R[^perm0_1 R[Int]], y : ^perm0_1 R[Int]) -> () where unique(^perm0_0), lent(^perm0_0), unique(^perm0_1), lent(^perm0_1) { self . move . foo [^perm0_0, ^perm0_1] (x . move, y . mut) ; y . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `bar`
            2: check function body
            3: judgment `can_type_expr_as { expr: { self . move . foo [!perm_0, !perm_1] (x . move, y . mut) ; y . move ; }, as_ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { self . move . foo [!perm_0, !perm_1] (x . move, y . mut) ; y . move ; }, as_ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { self . move . foo [!perm_0, !perm_1] (x . move, y . mut) ; y . move ; }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { self . move . foo [!perm_0, !perm_1] (x . move, y . mut) ; y . move ; }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [self . move . foo [!perm_0, !perm_1] (x . move, y . mut) ;, y . move ;], ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: self . move . foo [!perm_0, !perm_1] (x . move, y . mut) ;, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {y}, traversed: {} } }` failed at the following rule(s):
                                     the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `type_expr { expr: self . move . foo [!perm_0, !perm_1] (x . move, y . mut), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {y}, traversed: {} } }` failed at the following rule(s):
                                         the rule "call" failed at step #8 (src/file.rs:LL:CC) because
                                           judgment `type_method_arguments_as { exprs: [x . move, y . mut], input_temps: [@ fresh(0)], input_names: [x, y], input_tys: [!perm_0 R[!perm_1 R[Int]], !perm_1 R[Int]], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 1 }, live_after: LivePlaces { accessed: {y}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #7 (src/file.rs:LL:CC) because
                                               judgment `type_method_arguments_as { exprs: [y . mut], input_temps: [@ fresh(1), @ fresh(0)], input_names: [y], input_tys: [!perm_1 R[Int]], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 2 }, live_after: LivePlaces { accessed: {y}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "cons" failed at step #5 (src/file.rs:LL:CC) because
                                                   judgment `sub { a: mut [y] R[Int], b: !perm_1 R[Int], live_after: LivePlaces { accessed: {@ fresh(0), @ fresh(1), y}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                     the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                       judgment `sub_perms_both_ways { a: mut [y], b: !perm_1, live_after: LivePlaces { accessed: {@ fresh(0), @ fresh(1), y}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                         the rule "sub-perms" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `sub_perms { a: mut [y], b: !perm_1, live_after: LivePlaces { accessed: {@ fresh(0), @ fresh(1), y}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                             the rule "expand left" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `sub_perms { a: mut [y] !perm_1, b: !perm_1, live_after: LivePlaces { accessed: {@ fresh(0), @ fresh(1), y}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                 the rule "apply to shared, left" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_shared { a: !perm_1, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                     the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: shared(!perm_1), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), unique(!perm_1), lent(!perm_0), lent(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`"#]]);
}

/// See `escapes_ok`, but here we don't know that `B` is leased (and hence get an error).
/// In particular you can't convert e.g. `mut[y] my R[Int]`.
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
              unique(A), lent(A),
            {
              ();
            }

            fn bar[perm A, perm B](my self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              unique(A), lent(A),
            {
              self.move.foo[A, B](x.move, y.mut);
            }
          }
    ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class R [ty] { value : ^ty0_0 ; } class Main { fn foo [perm, perm] (my self x : ^perm0_0 R[^perm0_1 R[Int]], y : ^perm0_1 R[Int]) -> () where unique(^perm0_0), lent(^perm0_0) { () ; } fn bar [perm, perm] (my self x : ^perm0_0 R[^perm0_1 R[Int]], y : ^perm0_1 R[Int]) -> () where unique(^perm0_0), lent(^perm0_0) { self . move . foo [^perm0_0, ^perm0_1] (x . move, y . mut) ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `bar`
            2: check function body
            3: judgment `can_type_expr_as { expr: { self . move . foo [!perm_0, !perm_1] (x . move, y . mut) ; }, as_ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { self . move . foo [!perm_0, !perm_1] (x . move, y . mut) ; }, as_ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { self . move . foo [!perm_0, !perm_1] (x . move, y . mut) ; }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { self . move . foo [!perm_0, !perm_1] (x . move, y . mut) ; }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [self . move . foo [!perm_0, !perm_1] (x . move, y . mut) ;], ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: self . move . foo [!perm_0, !perm_1] (x . move, y . mut) ;, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `type_expr { expr: self . move . foo [!perm_0, !perm_1] (x . move, y . mut), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "call" failed at step #8 (src/file.rs:LL:CC) because
                                           judgment `type_method_arguments_as { exprs: [x . move, y . mut], input_temps: [@ fresh(0)], input_names: [x, y], input_tys: [!perm_0 R[!perm_1 R[Int]], !perm_1 R[Int]], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #7 (src/file.rs:LL:CC) because
                                               judgment `type_method_arguments_as { exprs: [y . mut], input_temps: [@ fresh(1), @ fresh(0)], input_names: [y], input_tys: [!perm_1 R[Int]], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 2 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "cons" failed at step #5 (src/file.rs:LL:CC) because
                                                   judgment `sub { a: mut [y] R[Int], b: !perm_1 R[Int], live_after: LivePlaces { accessed: {@ fresh(0), @ fresh(1)}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                     the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                       judgment `sub_perms_both_ways { a: mut [y], b: !perm_1, live_after: LivePlaces { accessed: {@ fresh(0), @ fresh(1)}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                         the rule "sub-perms" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `sub_perms { a: mut [y], b: !perm_1, live_after: LivePlaces { accessed: {@ fresh(0), @ fresh(1)}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                             the rule "dead left" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `dead_perm { acc: mt, place: y, tail: my, live_after: LivePlaces { accessed: {@ fresh(0), @ fresh(1)}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                 the rule "dead mut" failed at step #3 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                     the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`
                                                             the rule "expand left" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `sub_perms { a: mut [y] !perm_1, b: !perm_1, live_after: LivePlaces { accessed: {@ fresh(0), @ fresh(1)}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                 the rule "apply to shared, left" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_shared { a: !perm_1, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                     the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: shared(!perm_1), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`
                                                                 the rule "dead left" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `dead_perm { acc: mt, place: y, tail: !perm_1, live_after: LivePlaces { accessed: {@ fresh(0), @ fresh(1)}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                     the rule "dead mut" failed at step #3 (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_lent { a: !perm_1, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                         the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: lent(!perm_1), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, @ fresh(0): my Main, @ fresh(1): !perm_0 R[!perm_1 R[Int]], @ fresh(2): mut [y] R[Int], x: !perm_0 R[!perm_1 R[Int]], y: !perm_1 R[Int]}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 3 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`"#]]);
}

/// Check that a `ref[d1, d2]` in parameters prohibits writes to `d1`.
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
              let p = new Pair[ref[d1, d2] Data](d1.ref, d2.ref);
              d1 = new Data();
              let _keep_alive = p.move;
            }
          }
    ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Pair [ty] { value1 : ^ty0_0 ; value2 : ^ty0_0 ; } class Data { } class Main { fn main (my self) -> () { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ; d1 = new Data () ; let _keep_alive = p . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `main`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ; d1 = new Data () ; let _keep_alive = p . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ; d1 = new Data () ; let _keep_alive = p . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ; d1 = new Data () ; let _keep_alive = p . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ; d1 = new Data () ; let _keep_alive = p . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d1 = new Data () ;, let d2 = new Data () ;, let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ;, d1 = new Data () ;, let _keep_alive = p . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let d2 = new Data () ;, let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ;, d1 = new Data () ;, let _keep_alive = p . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ;, d1 = new Data () ;, let _keep_alive = p . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [d1 = new Data () ;, let _keep_alive = p . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data, p: Pair[ref [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: d1 = new Data () ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data, p: Pair[ref [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "reassign" failed at step #4 (src/file.rs:LL:CC) because
                                                   judgment `env_permits_access { access: mut, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Data, d1: Data, d2: Data, p: Pair[ref [d1, d2] Data]}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `parameters_permit_access { parameters: [Pair[ref [d1, d2] Data]], access: mut, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Data, d1: Data, d2: Data, p: Pair[ref [d1, d2] Data]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                         the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `parameter_permits_access { parameter: Pair[ref [d1, d2] Data], access: mut, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Data, d1: Data, d2: Data, p: Pair[ref [d1, d2] Data]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                             the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `lien_permit_access { lien: rf(d1), access: mut, accessed_place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Data, d1: Data, d2: Data, p: Pair[ref [d1, d2] Data]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                 the rule "ref'd" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `ref_place_permits_access { shared_place: d1, access: mut, accessed_place: d1 }` failed at the following rule(s):
                                                                     the rule "share-mutation" failed at step #0 (src/file.rs:LL:CC) because
                                                                       condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
                                                                         &accessed_place = d1
                                                                         &shared_place = d1"#]]);
}

/// Check that a `ref[d1, d2]` in parameters prohibits writes to `d2`.
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
              let p = new Pair[ref[d1, d2] Data](d1.ref, d2.ref);
              d2 = new Data();
              let _keep_alive = p.move;
            }
          }
    ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Pair [ty] { value1 : ^ty0_0 ; value2 : ^ty0_0 ; } class Data { } class Main { fn main (my self) -> () { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ; d2 = new Data () ; let _keep_alive = p . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `main`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ; d2 = new Data () ; let _keep_alive = p . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ; d2 = new Data () ; let _keep_alive = p . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ; d2 = new Data () ; let _keep_alive = p . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ; d2 = new Data () ; let _keep_alive = p . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d1 = new Data () ;, let d2 = new Data () ;, let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ;, d2 = new Data () ;, let _keep_alive = p . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let d2 = new Data () ;, let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ;, d2 = new Data () ;, let _keep_alive = p . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let p = new Pair [ref [d1, d2] Data] (d1 . ref, d2 . ref) ;, d2 = new Data () ;, let _keep_alive = p . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [d2 = new Data () ;, let _keep_alive = p . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data, p: Pair[ref [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: d2 = new Data () ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data, p: Pair[ref [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "reassign" failed at step #4 (src/file.rs:LL:CC) because
                                                   judgment `env_permits_access { access: mut, place: d2, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Data, d1: Data, d2: Data, p: Pair[ref [d1, d2] Data]}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `parameters_permit_access { parameters: [Pair[ref [d1, d2] Data]], access: mut, place: d2, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Data, d1: Data, d2: Data, p: Pair[ref [d1, d2] Data]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                         the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `parameter_permits_access { parameter: Pair[ref [d1, d2] Data], access: mut, place: d2, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Data, d1: Data, d2: Data, p: Pair[ref [d1, d2] Data]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                             the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `"flat_map"` failed at the following rule(s):
                                                                 failed at (src/file.rs:LL:CC) because
                                                                   judgment `lien_permit_access { lien: rf(d2), access: mut, accessed_place: d2, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Data, d1: Data, d2: Data, p: Pair[ref [d1, d2] Data]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                     the rule "ref'd" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `ref_place_permits_access { shared_place: d2, access: mut, accessed_place: d2 }` failed at the following rule(s):
                                                                         the rule "share-mutation" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
                                                                             &accessed_place = d2
                                                                             &shared_place = d2"#]]);
}

/// Check that a `mut[d1, d2]` in parameters prohibits reads from `d1`.
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
              let p = new Pair[mut[d1, d2] Data](d1.mut, d2.mut);
              d1.ref;
              let _keep_alive = p.move;
            }
          }
    ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Pair [ty] { value1 : ^ty0_0 ; value2 : ^ty0_0 ; } class Data { } class Main { fn main (my self) -> () { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [mut [d1, d2] Data] (d1 . mut, d2 . mut) ; d1 . ref ; let _keep_alive = p . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `main`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [mut [d1, d2] Data] (d1 . mut, d2 . mut) ; d1 . ref ; let _keep_alive = p . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [mut [d1, d2] Data] (d1 . mut, d2 . mut) ; d1 . ref ; let _keep_alive = p . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [mut [d1, d2] Data] (d1 . mut, d2 . mut) ; d1 . ref ; let _keep_alive = p . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d1 = new Data () ; let d2 = new Data () ; let p = new Pair [mut [d1, d2] Data] (d1 . mut, d2 . mut) ; d1 . ref ; let _keep_alive = p . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d1 = new Data () ;, let d2 = new Data () ;, let p = new Pair [mut [d1, d2] Data] (d1 . mut, d2 . mut) ;, d1 . ref ;, let _keep_alive = p . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let d2 = new Data () ;, let p = new Pair [mut [d1, d2] Data] (d1 . mut, d2 . mut) ;, d1 . ref ;, let _keep_alive = p . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let p = new Pair [mut [d1, d2] Data] (d1 . mut, d2 . mut) ;, d1 . ref ;, let _keep_alive = p . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [d1 . ref ;, let _keep_alive = p . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data, p: Pair[mut [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: d1 . ref ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data, p: Pair[mut [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: d1 . ref, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data, p: Pair[mut [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "ref|mut place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: ref, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data, p: Pair[mut [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `env_permits_access { access: ref, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data, p: Pair[mut [d1, d2] Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `parameters_permit_access { parameters: [Pair[mut [d1, d2] Data]], access: ref, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data, p: Pair[mut [d1, d2] Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `parameter_permits_access { parameter: Pair[mut [d1, d2] Data], access: ref, place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data, p: Pair[mut [d1, d2] Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `lien_permit_access { lien: mt(d1), access: ref, accessed_place: d1, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: Data, d2: Data, p: Pair[mut [d1, d2] Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "mut'd" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `mut_place_permits_access { leased_place: d1, access: ref, accessed_place: d1 }` failed at the following rule(s):
                                                                             the rule "lease-mutation" failed at step #0 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
                                                                                 &accessed_place = d1
                                                                                 &leased_place = d1"#]]);
}
