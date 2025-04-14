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
                let s = foo.i.ref;
                let bar = foo.move; // rewrites type of `s` to `shared(bar) Foo`
                bar.i.ref;
                s.move;
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
                let s = foo.i.ref;
                let bar = foo.move; // rewrites type of `s` to `shared(bar) Foo`
                bar.i.move;
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
                let s = foo.i.ref;

                // rewrites type of `s` to `shared(bar.i) Int`
                let bar = foo.move;

                // now we get an error here..
                bar.i.move;

                // ...because `s` is used again
                s.move;
                ();
            }
        }
    ")).assert_err(
        expect_test::expect![[r#"
            check program `class Data { } class Foo { i : Data ; } class Main { fn main (my self) -> () { let foo = new Foo (new Data ()) ; let s = foo . i . ref ; let bar = foo . move ; bar . i . move ; s . move ; () ; } }`

            Caused by:
                0: check class named `Main`
                1: check method named `main`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; let s = foo . i . ref ; let bar = foo . move ; bar . i . move ; s . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; let s = foo . i . ref ; let bar = foo . move ; bar . i . move ; s . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; let s = foo . i . ref ; let bar = foo . move ; bar . i . move ; s . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (new Data ()) ; let s = foo . i . ref ; let bar = foo . move ; bar . i . move ; s . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, let s = foo . i . ref ;, let bar = foo . move ;, bar . i . move ;, s . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let s = foo . i . ref ;, let bar = foo . move ;, bar . i . move ;, s . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let bar = foo . move ;, bar . i . move ;, s . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo, s: ref [foo . i] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                               judgment `type_statements_with_final_ty { statements: [bar . i . move ;, s . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: Foo, foo: Foo, s: ref [bar . i] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `type_statement { statement: bar . i . move ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: Foo, foo: Foo, s: ref [bar . i] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {s}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "expr" failed at step #2 (src/file.rs:LL:CC) because
                                                       judgment `env_permits_access { access: drop, place: @ fresh(0), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Data, bar: Foo, foo: Foo, s: ref [@ fresh(0)] Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {s}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `parameters_permit_access { parameters: [ref [@ fresh(0)] Data], access: drop, place: @ fresh(0), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Data, bar: Foo, foo: Foo, s: ref [@ fresh(0)] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                             the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `parameter_permits_access { parameter: ref [@ fresh(0)] Data, access: drop, place: @ fresh(0), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Data, bar: Foo, foo: Foo, s: ref [@ fresh(0)] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `lien_permit_access { lien: rf(@ fresh(0)), access: drop, accessed_place: @ fresh(0), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Data, bar: Foo, foo: Foo, s: ref [@ fresh(0)] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                     the rule "shared" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `shared_place_permits_access { shared_place: @ fresh(0), access: drop, accessed_place: @ fresh(0) }` failed at the following rule(s):
                                                                         the rule "share-mutation" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
                                                                             &accessed_place = @ fresh(0)
                                                                             &shared_place = @ fresh(0)"#]],
    )
}

/// Check that if we give while shared we can't then move out of the new name.
#[test]
fn give_while_shared_then_assign_while_shared() {
    check_program(&term(
        "
        class Data { }

        class Foo {
            i: Data;
        }

        class Main {
            fn main(my self) -> () {
                let foo = new Foo(new Data());
                let s = foo.i.ref;

                // rewrites type of `s` to `shared(bar.i) Int`
                let bar = foo.move;

                // we can still assign `bar.i` to `d`...
                let d = new Data();
                d = bar.i.move;

                // ...even though `s` is used again;
                // the type of `s` becomes `shared(d)`
                s.move;
                ();
            }
        }
    ",
    ))
    .assert_ok(expect_test::expect![[r#"()"#]])
}

/// Check that if we give while shared we can't then move out of the new name.
#[test]
fn give_while_shared_then_assign_while_shared_then_mutate_new_place() {
    check_program(&term(
        "
        class Data { }

        class Foo {
            i: Data;
        }

        class Main {
            fn main(my self) -> () {
                let foo = new Foo(new Data());
                let s = foo.i.ref;

                // rewrites type of `s` to `shared(bar.i) Int`
                let bar = foo.move;

                // we can still assign `bar.i` to `d`...
                let d = new Data();
                d = bar.i.move;

                // ...even though `s` is used again;
                // the type of `s` becomes `shared(d)`
                s.move;

                // but now we can't reassign `d`
                d = new Data();

                // when `s` is used again
                s.move;
                ();
            }
        }
    ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Foo { i : Data ; } class Main { fn main (my self) -> () { let foo = new Foo (new Data ()) ; let s = foo . i . ref ; let bar = foo . move ; let d = new Data () ; d = bar . i . move ; s . move ; d = new Data () ; s . move ; () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `main`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; let s = foo . i . ref ; let bar = foo . move ; let d = new Data () ; d = bar . i . move ; s . move ; d = new Data () ; s . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; let s = foo . i . ref ; let bar = foo . move ; let d = new Data () ; d = bar . i . move ; s . move ; d = new Data () ; s . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; let s = foo . i . ref ; let bar = foo . move ; let d = new Data () ; d = bar . i . move ; s . move ; d = new Data () ; s . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let foo = new Foo (new Data ()) ; let s = foo . i . ref ; let bar = foo . move ; let d = new Data () ; d = bar . i . move ; s . move ; d = new Data () ; s . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, let s = foo . i . ref ;, let bar = foo . move ;, let d = new Data () ;, d = bar . i . move ;, s . move ;, d = new Data () ;, s . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let s = foo . i . ref ;, let bar = foo . move ;, let d = new Data () ;, d = bar . i . move ;, s . move ;, d = new Data () ;, s . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let bar = foo . move ;, let d = new Data () ;, d = bar . i . move ;, s . move ;, d = new Data () ;, s . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo, s: ref [foo . i] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let d = new Data () ;, d = bar . i . move ;, s . move ;, d = new Data () ;, s . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: Foo, foo: Foo, s: ref [bar . i] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                               judgment `type_statements_with_final_ty { statements: [d = bar . i . move ;, s . move ;, d = new Data () ;, s . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: Foo, d: Data, foo: Foo, s: ref [bar . i] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `type_statements_with_final_ty { statements: [s . move ;, d = new Data () ;, s . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: Foo, d: Data, foo: Foo, s: ref [d] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                                       judgment `type_statements_with_final_ty { statements: [d = new Data () ;, s . move ;, () ;], ty: ref [d] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: Foo, d: Data, foo: Foo, s: ref [d] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `type_statement { statement: d = new Data () ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, bar: Foo, d: Data, foo: Foo, s: ref [d] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {s}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "reassign" failed at step #4 (src/file.rs:LL:CC) because
                                                               judgment `env_permits_access { access: mut, place: d, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Data, bar: Foo, d: Data, foo: Foo, s: ref [d] Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {s}, traversed: {} } }` failed at the following rule(s):
                                                                 the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `parameters_permit_access { parameters: [ref [d] Data], access: mut, place: d, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Data, bar: Foo, d: Data, foo: Foo, s: ref [d] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                     the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `parameter_permits_access { parameter: ref [d] Data, access: mut, place: d, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Data, bar: Foo, d: Data, foo: Foo, s: ref [d] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                           judgment `lien_permit_access { lien: rf(d), access: mut, accessed_place: d, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Data, bar: Foo, d: Data, foo: Foo, s: ref [d] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                             the rule "shared" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `shared_place_permits_access { shared_place: d, access: mut, accessed_place: d }` failed at the following rule(s):
                                                                                 the rule "share-mutation" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
                                                                                     &accessed_place = d
                                                                                     &shared_place = d"#]])
}
