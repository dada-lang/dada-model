use crate::{dada_lang::term, type_system::check_program};
use formality_core::{test, test_util::ResultTestExt};

/// Check that we can give something which is shared and then go on
/// using the shared thing.
#[test]
fn give_while_shared_then_use() {
    check_program(&term(
        "
        class Data {}

        class Foo {
            i: Data;
        }

        class Main {
            fn main(my self) -> () {
                let foo = new Foo(new Data());
                let s = foo.i.share;
                let bar = foo.give; // rewrites type of `s` to `shared(bar) Foo`
                bar.i.share;
                s.give;
                ();
            }
        }
    ",
    ))
    .assert_ok(expect_test::expect!["()"])
}

/// Check that we can give something which is shared and then go on
/// using the shared thing.
#[test]
fn give_while_shared_then_drop() {
    check_program(&term(
        "
        class Data { }

        class Foo {
            i: Data;
        }

        class Main {
            fn main(my self) -> () {
                let foo = new Foo(new Data());
                let s = foo.i.share;
                let bar = foo.give; // rewrites type of `s` to `shared(bar) Foo`
                bar.i.give;
                ();
            }
        }
    ",
    ))
    .assert_ok(expect_test::expect![["()"]])
}

/// Check that if we give while shared we can't then move out of the new name.
#[test]
fn give_while_shared_then_move_while_shared() {
    check_program(
        &term(
            "
        class Data { }

        class Foo {
            i: Data;
        }

        class Main {
            fn main(my self) -> () {
                let foo = new Foo(new Data());
                let s = foo.i.share;

                // rewrites type of `s` to `shared(bar.i) Int`
                let bar = foo.give;

                // now we get an error here..
                bar.i.give;

                // ...because `s` is used again
                s.give;
                ();
            }
        }
    ")).assert_err(
        expect_test::expect![[r#"
            check program `class Data { } class Foo { i : Data ; } class Main { fn main (my self) -> () { let foo = new Foo (new Data ()) ; let s = foo . i . share ; let bar = foo . give ; bar . i . give ; s . give ; () ; } }`

            Caused by:
                0: check class named `Main`
                1: check method named `main`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; let s = foo . i . share ; let bar = foo . give ; bar . i . give ; s . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; let s = foo . i . share ; let bar = foo . give ; bar . i . give ; s . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; let s = foo . i . share ; let bar = foo . give ; bar . i . give ; s . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (new Data ()) ; let s = foo . i . share ; let bar = foo . give ; bar . i . give ; s . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, let s = foo . i . share ;, let bar = foo . give ;, bar . i . give ;, s . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let s = foo . i . share ;, let bar = foo . give ;, bar . i . give ;, s . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let bar = foo . give ;, bar . i . give ;, s . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo, s: shared (foo . i) Data}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                               judgment `type_statements_with_final_ty { statements: [bar . i . give ;, s . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: Foo, foo: Foo, s: shared (bar . i) Data}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `type_statement { statement: bar . i . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: Foo, foo: Foo, s: shared (bar . i) Data}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo} }, live_after: LiveVars { vars: {s} } }` failed at the following rule(s):
                                                     the rule "expr" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `env_permits_access { access: drop, place: @ in_flight, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: Foo, foo: Foo, s: shared (@ in_flight) Data}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {bar . i, foo} }, live_after: LiveVars { vars: {s} } }` failed at the following rule(s):
                                                         the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `parameters_permit_access { parameters: [shared (@ in_flight) Data], access: drop, place: @ in_flight, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: Foo, foo: Foo, s: shared (@ in_flight) Data}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {bar . i, foo} } }` failed at the following rule(s):
                                                             the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `parameter_permits_access { parameter: shared (@ in_flight) Data, access: drop, place: @ in_flight, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: Foo, foo: Foo, s: shared (@ in_flight) Data}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {bar . i, foo} } }` failed at the following rule(s):
                                                                 the rule "ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `ty_permits_access { ty: shared (@ in_flight) Data, access: drop, place: @ in_flight, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: Foo, foo: Foo, s: shared (@ in_flight) Data}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {bar . i, foo} } }` failed at the following rule(s):
                                                                     the rule "ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `perm_permits_access { perm: shared (@ in_flight), access: drop, place: @ in_flight, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: Foo, foo: Foo, s: shared (@ in_flight) Data}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {bar . i, foo} } }` failed at the following rule(s):
                                                                         the rule "disjoint" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `place_disjoint_from_all_of(&accessed_place, &perm_places)`
                                                                             &accessed_place = @ in_flight
                                                                             &perm_places = {@ in_flight}"#]],
    )
}
