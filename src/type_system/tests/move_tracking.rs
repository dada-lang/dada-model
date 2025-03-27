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
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; let s = foo . i . share ; let bar = foo . give ; bar . i . give ; s . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; let s = foo . i . share ; let bar = foo . give ; bar . i . give ; s . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; let s = foo . i . share ; let bar = foo . give ; bar . i . give ; s . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (new Data ()) ; let s = foo . i . share ; let bar = foo . give ; bar . i . give ; s . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, let s = foo . i . share ;, let bar = foo . give ;, bar . i . give ;, s . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let s = foo . i . share ;, let bar = foo . give ;, bar . i . give ;, s . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: let s = foo . i . share ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo, s}, traversed: {} } }` failed at the following rule(s):
                                             the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: foo . i . share, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `access_permitted { access: share, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `env_permits_access { access: share, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `parameters_permit_access { parameters: [Foo], access: share, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `parameter_permits_access { parameter: Foo, access: share, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `liens { a: Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `some_lien { a: Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                           expression evaluated to an empty collection: `parameters`"#]],
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
                let s = foo.i.share;

                // rewrites type of `s` to `shared(bar.i) Int`
                let bar = foo.give;

                // we can still assign `bar.i` to `d`...
                let d = new Data();
                d = bar.i.give;

                // ...even though `s` is used again;
                // the type of `s` becomes `shared(d)`
                s.give;
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
                let s = foo.i.share;

                // rewrites type of `s` to `shared(bar.i) Int`
                let bar = foo.give;

                // we can still assign `bar.i` to `d`...
                let d = new Data();
                d = bar.i.give;

                // ...even though `s` is used again;
                // the type of `s` becomes `shared(d)`
                s.give;

                // but now we can't reassign `d`
                d = new Data();

                // when `s` is used again
                s.give;
                ();
            }
        }
    ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Foo { i : Data ; } class Main { fn main (my self) -> () { let foo = new Foo (new Data ()) ; let s = foo . i . share ; let bar = foo . give ; let d = new Data () ; d = bar . i . give ; s . give ; d = new Data () ; s . give ; () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `main`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let foo = new Foo (new Data ()) ; let s = foo . i . share ; let bar = foo . give ; let d = new Data () ; d = bar . i . give ; s . give ; d = new Data () ; s . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let foo = new Foo (new Data ()) ; let s = foo . i . share ; let bar = foo . give ; let d = new Data () ; d = bar . i . give ; s . give ; d = new Data () ; s . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let foo = new Foo (new Data ()) ; let s = foo . i . share ; let bar = foo . give ; let d = new Data () ; d = bar . i . give ; s . give ; d = new Data () ; s . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let foo = new Foo (new Data ()) ; let s = foo . i . share ; let bar = foo . give ; let d = new Data () ; d = bar . i . give ; s . give ; d = new Data () ; s . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let foo = new Foo (new Data ()) ;, let s = foo . i . share ;, let bar = foo . give ;, let d = new Data () ;, d = bar . i . give ;, s . give ;, d = new Data () ;, s . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let s = foo . i . share ;, let bar = foo . give ;, let d = new Data () ;, d = bar . i . give ;, s . give ;, d = new Data () ;, s . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let s = foo . i . share ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo, s}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr { expr: foo . i . share, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo}, traversed: {} } }` failed at the following rule(s):
                                             the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `access_permitted { access: share, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `env_permits_access { access: share, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {foo}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `parameters_permit_access { parameters: [Foo], access: share, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `parameter_permits_access { parameter: Foo, access: share, place: foo . i, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `liens { a: Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `some_lien { a: Foo, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, foo: Foo}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                       expression evaluated to an empty collection: `parameters`"#]])
}
