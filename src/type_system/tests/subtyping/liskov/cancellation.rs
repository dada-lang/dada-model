//! # Liveness and cancellation
//!
//! When variables are dead, subtyping allows for *cancellation*, so e.g. if `d1` is dead,
//! then `ref[d1] mut[d2] Foo` is a subtype of `mut[d2] Foo`. Cancellation only
//! applies when we have a shared/leased permission applies to a leased permission.
//!
//! Consideration to test:
//!
//! * C1. Cancellation can remove "relative" permissions like `shared` and `leased`, but not owned permissions
//!   like `my` or `our` nor generic permissions (since in that case we do not know which variables they
//!   may refer to)
//! * C2. Cancellation can only occur if all variables in the permission are dead: so `ref[d1, d2]` can only
//!   be canceled if `d1` and `d2` are both dead.
//! * C3. Cancellation cannot convert a shared permission into a leased permission.
//! * C4. Subtyping must account for future cancellation. So e.g., `mut[d1, d2] Foo` cannot be a subtype of
//!   `mut[d1] mut[d2] Foo` since, if `d1` later goes dead, the supertype could be upcast
//!   to `mut[d2] Foo` but the subtype could not. That would be unsound.

use crate::{dada_lang::term, type_system::check_program};
use formality_core::{test, test_util::ResultTestExt};

// C1. Cancellation can remove "relative" permissions like `shared` and `leased`.

#[test]
fn c1_remove_relative_shared() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) {
                let m: my Data = new Data();
                let p: ref[m] Data = m.ref;
                let q: ref[p] ref[m] Data = p.ref;
                let r: ref[m] Data = q.move;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
fn c1_remove_relative_leased() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) {
                let m: my Data = new Data();
                let p: mut[m] Data = m.mut;
                let q: mut[p] Data = p.mut;
                let r: mut[m] Data = q.move;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

// C1. Cancellation and `my` permission are not very relevant.
//
// The `my my` type here is equivalent to `my` so this just becomes
// ownership transfer.

#[test]
fn c1_remove_my() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) {
                let m: my Data = new Data();
                let p: my my Data = m.move;
                let q: my Data = p.move;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

// C1. Cancellation cannot remove owned permissions `our`.

#[test]
fn c1_remove_our() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) {
                let m: my Data = new Data();
                let p: our my Data = m.move;
                let q: my Data = p.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self) -> () { let m : my Data = new Data () ; let p : our my Data = m . move ; let q : my Data = p . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : my Data = new Data () ; let p : our my Data = m . move ; let q : my Data = p . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : my Data = new Data () ; let p : our my Data = m . move ; let q : my Data = p . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let m : my Data = new Data () ; let p : our my Data = m . move ; let q : my Data = p . move ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let m : my Data = new Data () ; let p : our my Data = m . move ; let q : my Data = p . move ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let m : my Data = new Data () ;, let p : our my Data = m . move ;, let q : my Data = p . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let p : our my Data = m . move ;, let q : my Data = p . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let q : my Data = p . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: our my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: let q : my Data = p . move ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: our my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr_as { expr: p . move, as_ty: my Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: our my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `sub { a: our my Data, b: my Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: our my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                       judgment `sub_perms { a: our my, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: our my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_unique { a: our my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: our my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: unique(our my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: our my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   pattern `true` did not match value `false`
                                                         the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_unique { a: our my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: our my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: unique(our my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: our my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   pattern `true` did not match value `false`
                                                         the rule "our-sub-copy" failed at step #2 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_share { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: our my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: our my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   pattern `true` did not match value `false`"#]]);
}

// C1. Cancellation cannot remove generic permissions `our`.

#[test]
fn c1_remove_generic_permissions() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self, p: P my Data) {
                let q: my Data = p.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self p : ^perm0_0 my Data) -> () { let q : my Data = p . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let q : my Data = p . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let q : my Data = p . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let q : my Data = p . move ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let q : my Data = p . move ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let q : my Data = p . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: let q : my Data = p . move ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `type_expr_as { expr: p . move, as_ty: my Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `sub { a: !perm_0 my Data, b: my Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                               judgment `sub_perms { a: !perm_0 my, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `prove_is_unique { a: !perm_0 my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `prove_predicate { predicate: unique(!perm_0 my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                           pattern `true` did not match value `false`
                                                 the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `prove_is_unique { a: !perm_0 my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `prove_predicate { predicate: unique(!perm_0 my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                           pattern `true` did not match value `false`
                                                 the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `prove_is_share { a: !perm_0 my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `prove_predicate { predicate: shared(!perm_0 my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                           pattern `true` did not match value `false`"#]]);
}

// C2. Cancellation can only occur if all variables in the permission are dead.

#[test]
fn c2_shared_shared_one_of_one_variables_dead() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) {
                let m: my Data = new Data();
                let p: ref[m] Data = m.ref;
                let q: ref[p] ref[m] Data = p.ref;
                let r: ref[m] Data = q.move;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
fn c2_shared_shared_two_of_two_variables_dead() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) {
                let m: my Data = new Data();
                let p: ref[m] Data = m.ref;
                let q: ref[m] Data = m.ref;
                let r: ref[p, q] ref[m] Data = p.ref;
                let s: ref[m] Data = r.move;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
fn c2_shared_shared_one_of_two_variables_dead() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) {
                let m: my Data = new Data();
                let p: ref[m] Data = m.ref;
                let q: ref[m] Data = m.ref;
                let r: ref[p, q] ref[m] Data = p.ref;
                let s: ref[m] Data = r.move;
                q.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self) -> () { let m : my Data = new Data () ; let p : ref [m] Data = m . ref ; let q : ref [m] Data = m . ref ; let r : ref [p, q] ref [m] Data = p . ref ; let s : ref [m] Data = r . move ; q . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : my Data = new Data () ; let p : ref [m] Data = m . ref ; let q : ref [m] Data = m . ref ; let r : ref [p, q] ref [m] Data = p . ref ; let s : ref [m] Data = r . move ; q . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : my Data = new Data () ; let p : ref [m] Data = m . ref ; let q : ref [m] Data = m . ref ; let r : ref [p, q] ref [m] Data = p . ref ; let s : ref [m] Data = r . move ; q . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment had no applicable rules: `sub { a: ref [m] Data, b: (), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: ref [m] Data, q: ref [m] Data, r: ref [@ fresh(0), p] ref [m] Data, s: ref [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }`"#]]);
}

#[test]
fn c2_leased_leased_one_of_one_variables_dead() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) {
                let m: my Data = new Data();
                let p: mut[m] Data = m.mut;
                let q: mut[p] Data = p.mut;
                let r: mut[m] Data = q.move;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
fn c2_leased_leased_two_of_two_variables_dead() {
    check_program(&term(
        "
        class Data {}
        class Pair {
            a: my Data;
            b: my Data;
        }
        class Main {
            fn test[perm P](my self) {
                let m: my Pair = new Pair(new Data(), new Data());
                let p: mut[m.a] Data = m.a.mut;
                let q: mut[m.b] Data = m.b.mut;
                let r: mut[p, q] Data = p.mut;
                let s: mut[m] Data = r.move;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
fn c2_leased_leased_one_of_two_variables_dead() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) {
                let m: my Data = new Data();
                let p: mut[m] Data = m.mut;
                let q: mut[m] Data = m.mut;
                let r: mut[p, q] mut[m] Data = p.mut;
                let s: mut[m] Data = r.move;
                q.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self) -> () { let m : my Data = new Data () ; let p : mut [m] Data = m . mut ; let q : mut [m] Data = m . mut ; let r : mut [p, q] mut [m] Data = p . mut ; let s : mut [m] Data = r . move ; q . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : my Data = new Data () ; let p : mut [m] Data = m . mut ; let q : mut [m] Data = m . mut ; let r : mut [p, q] mut [m] Data = p . mut ; let s : mut [m] Data = r . move ; q . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : my Data = new Data () ; let p : mut [m] Data = m . mut ; let q : mut [m] Data = m . mut ; let r : mut [p, q] mut [m] Data = p . mut ; let s : mut [m] Data = r . move ; q . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let m : my Data = new Data () ; let p : mut [m] Data = m . mut ; let q : mut [m] Data = m . mut ; let r : mut [p, q] mut [m] Data = p . mut ; let s : mut [m] Data = r . move ; q . move ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let m : my Data = new Data () ; let p : mut [m] Data = m . mut ; let q : mut [m] Data = m . mut ; let r : mut [p, q] mut [m] Data = p . mut ; let s : mut [m] Data = r . move ; q . move ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let m : my Data = new Data () ;, let p : mut [m] Data = m . mut ;, let q : mut [m] Data = m . mut ;, let r : mut [p, q] mut [m] Data = p . mut ;, let s : mut [m] Data = r . move ;, q . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let p : mut [m] Data = m . mut ;, let q : mut [m] Data = m . mut ;, let r : mut [p, q] mut [m] Data = p . mut ;, let s : mut [m] Data = r . move ;, q . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let q : mut [m] Data = m . mut ;, let r : mut [p, q] mut [m] Data = p . mut ;, let s : mut [m] Data = r . move ;, q . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: let q : mut [m] Data = m . mut ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {p, q}, traversed: {} } }` failed at the following rule(s):
                                             the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr_as { expr: m . mut, as_ty: mut [m] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: m . mut, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: mut, place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `env_permits_access { access: mut, place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `parameters_permit_access { parameters: [mut [m] Data], access: mut, place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `parameter_permits_access { parameter: mut [m] Data, access: mut, place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `lien_permit_access { lien: mt(m), access: mut, accessed_place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "leased" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `leased_place_permits_access { leased_place: m, access: mut, accessed_place: m }` failed at the following rule(s):
                                                                             the rule "lease-mutation" failed at step #0 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
                                                                                 &accessed_place = m
                                                                                 &leased_place = m"#]]);
}

// C3. Cancellation cannot convert a shared permission into a leased permission.

#[test]
fn c3_shared_leased_one_of_one_variables_dead() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) {
                let m: my Data = new Data();
                let p: mut[m] Data = m.mut;
                let q: ref[p] mut[m] Data = p.ref;
                let r: mut[m] Data = q.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self) -> () { let m : my Data = new Data () ; let p : mut [m] Data = m . mut ; let q : ref [p] mut [m] Data = p . ref ; let r : mut [m] Data = q . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : my Data = new Data () ; let p : mut [m] Data = m . mut ; let q : ref [p] mut [m] Data = p . ref ; let r : mut [m] Data = q . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : my Data = new Data () ; let p : mut [m] Data = m . mut ; let q : ref [p] mut [m] Data = p . ref ; let r : mut [m] Data = q . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let m : my Data = new Data () ; let p : mut [m] Data = m . mut ; let q : ref [p] mut [m] Data = p . ref ; let r : mut [m] Data = q . move ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let m : my Data = new Data () ; let p : mut [m] Data = m . mut ; let q : ref [p] mut [m] Data = p . ref ; let r : mut [m] Data = q . move ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let m : my Data = new Data () ;, let p : mut [m] Data = m . mut ;, let q : ref [p] mut [m] Data = p . ref ;, let r : mut [m] Data = q . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let p : mut [m] Data = m . mut ;, let q : ref [p] mut [m] Data = p . ref ;, let r : mut [m] Data = q . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let q : ref [p] mut [m] Data = p . ref ;, let r : mut [m] Data = q . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: let q : ref [p] mut [m] Data = p . ref ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {q}, traversed: {} } }` failed at the following rule(s):
                                             the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr_as { expr: p . ref, as_ty: ref [p] mut [m] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `sub { a: ref [p] Data, b: ref [p] mut [m] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                       judgment `sub_perms { a: ref [p], b: ref [p] mut [m], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_unique { a: ref [p], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: unique(ref [p]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   pattern `true` did not match value `false`
                                                         the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_unique { a: ref [p], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: unique(ref [p]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   pattern `true` did not match value `false`
                                                         the rule "our-sub-copy" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_owned { a: ref [p], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: owned(ref [p]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   pattern `true` did not match value `false`
                                                         the rule "sub_perms_relative" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `sub_perm_heads { a: LeafPerms { leaves: [ref [p]] }, b: LeafPerms { leaves: [ref [p], mut [m]] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "shared-shared" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `sub_place_perms { places_a: {p}, tail_a: my, places_b: {p}, tail_b: mut [m], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "places-places" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `sub_perm_tails { a: LeafPerms { leaves: [] }, b: LeafPerms { leaves: [mut [m]] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "tail-head" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `sub_perm_heads { a: LeafPerms { leaves: [] }, b: LeafPerms { leaves: [mut [m]] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "simplify-rhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `simplify_perm { perm: LeafPerms { leaves: [mut [m]] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                             the rule "copy type" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `"flat_map"` failed at the following rule(s):
                                                                                 failed at (src/file.rs:LL:CC) because
                                                                                   judgment `prove_is_share { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           pattern `true` did not match value `false`
                                                                             the rule "dead_leased-up" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `"flat_map"` failed at the following rule(s):
                                                                                 failed at (src/file.rs:LL:CC) because
                                                                                   judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           pattern `true` did not match value `false`
                                                             the rule "simplify-lhs" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `sub_perm_heads { a: LeafPerms { leaves: [our, mut [m]] }, b: LeafPerms { leaves: [ref [p], mut [m]] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "simplify-lhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `simplify_perm { perm: LeafPerms { leaves: [our, mut [m]] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                     the rule "apply-to-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_share { a: mut [m], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: shared(mut [m]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`
                                                                 the rule "simplify-rhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `simplify_perm { perm: LeafPerms { leaves: [ref [p], mut [m]] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                     the rule "apply-to-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_share { a: mut [m], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: shared(mut [m]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`
                                                             the rule "simplify-rhs" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `simplify_perm { perm: LeafPerms { leaves: [ref [p], mut [m]] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                 the rule "apply-to-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_share { a: mut [m], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: shared(mut [m]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`"#]]);
}

#[test]
fn c3_shared_leased_two_of_two_variables_dead() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) {
                let m: my Data = new Data();
                let p: mut[m] Data = m.ref;
                let q: mut[m] Data = m.ref;
                let r: ref[p, q] mut[m] Data = p.ref;
                let s: ref[m] Data = r.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self) -> () { let m : my Data = new Data () ; let p : mut [m] Data = m . ref ; let q : mut [m] Data = m . ref ; let r : ref [p, q] mut [m] Data = p . ref ; let s : ref [m] Data = r . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : my Data = new Data () ; let p : mut [m] Data = m . ref ; let q : mut [m] Data = m . ref ; let r : ref [p, q] mut [m] Data = p . ref ; let s : ref [m] Data = r . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : my Data = new Data () ; let p : mut [m] Data = m . ref ; let q : mut [m] Data = m . ref ; let r : ref [p, q] mut [m] Data = p . ref ; let s : ref [m] Data = r . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let m : my Data = new Data () ; let p : mut [m] Data = m . ref ; let q : mut [m] Data = m . ref ; let r : ref [p, q] mut [m] Data = p . ref ; let s : ref [m] Data = r . move ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let m : my Data = new Data () ; let p : mut [m] Data = m . ref ; let q : mut [m] Data = m . ref ; let r : ref [p, q] mut [m] Data = p . ref ; let s : ref [m] Data = r . move ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let m : my Data = new Data () ;, let p : mut [m] Data = m . ref ;, let q : mut [m] Data = m . ref ;, let r : ref [p, q] mut [m] Data = p . ref ;, let s : ref [m] Data = r . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let p : mut [m] Data = m . ref ;, let q : mut [m] Data = m . ref ;, let r : ref [p, q] mut [m] Data = p . ref ;, let s : ref [m] Data = r . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let p : mut [m] Data = m . ref ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m, p}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr_as { expr: m . ref, as_ty: mut [m] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m}, traversed: {} } }` failed at the following rule(s):
                                             the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `sub { a: ref [m] Data, b: mut [m] Data, live_after: LivePlaces { accessed: {m}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                   judgment `sub_perms { a: ref [m], b: mut [m], live_after: LivePlaces { accessed: {m}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `prove_is_unique { a: ref [m], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_predicate { predicate: unique(ref [m]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                               pattern `true` did not match value `false`
                                                     the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `prove_is_unique { a: ref [m], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_predicate { predicate: unique(ref [m]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                               pattern `true` did not match value `false`
                                                     the rule "our-sub-copy" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `prove_is_owned { a: ref [m], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_predicate { predicate: owned(ref [m]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                               pattern `true` did not match value `false`
                                                     the rule "sub_perms_relative" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `sub_perm_heads { a: LeafPerms { leaves: [ref [m]] }, b: LeafPerms { leaves: [mut [m]] }, live_after: LivePlaces { accessed: {m}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "simplify-lhs" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `simplify_perm { perm: LeafPerms { leaves: [ref [m]] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "copy type" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `"flat_map"` failed at the following rule(s):
                                                                 failed at (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_share { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`
                                                         the rule "simplify-rhs" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `simplify_perm { perm: LeafPerms { leaves: [mut [m]] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "copy type" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `"flat_map"` failed at the following rule(s):
                                                                 failed at (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_share { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`"#]]);
}

#[test]
fn c3_shared_leased_one_of_two_variables_dead() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) {
                let m: my Data = new Data();
                let p: ref[m] Data = m.ref;
                let q: ref[m] Data = m.ref;
                let r: ref[p, q] ref[m] Data = p.ref;
                let s: ref[m] Data = r.move;
                q.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self) -> () { let m : my Data = new Data () ; let p : ref [m] Data = m . ref ; let q : ref [m] Data = m . ref ; let r : ref [p, q] ref [m] Data = p . ref ; let s : ref [m] Data = r . move ; q . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : my Data = new Data () ; let p : ref [m] Data = m . ref ; let q : ref [m] Data = m . ref ; let r : ref [p, q] ref [m] Data = p . ref ; let s : ref [m] Data = r . move ; q . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : my Data = new Data () ; let p : ref [m] Data = m . ref ; let q : ref [m] Data = m . ref ; let r : ref [p, q] ref [m] Data = p . ref ; let s : ref [m] Data = r . move ; q . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment had no applicable rules: `sub { a: ref [m] Data, b: (), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: ref [m] Data, q: ref [m] Data, r: ref [@ fresh(0), p] ref [m] Data, s: ref [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }`"#]]);
}

// C4. Subtyping must account for future cancellation.

#[test]
fn c4_shared_d1d2d3_not_subtype_of_shared_d1_shared_d2d3() {
    // This is interesting. It fails because `ref[d1] ref[d2, d3]`
    // is equivalent to `ref[d2, d3]` and there is clearly no subtyping relation.
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) {
                let d1: my Data = new Data();
                let d2: my Data = new Data();
                let d3: my Data = new Data();
                let s1: ref[d1, d2, d3] Data = d1.ref;
                let s2: ref[d1] ref[d2, d3] Data = s1.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self) -> () { let d1 : my Data = new Data () ; let d2 : my Data = new Data () ; let d3 : my Data = new Data () ; let s1 : ref [d1, d2, d3] Data = d1 . ref ; let s2 : ref [d1] ref [d2, d3] Data = s1 . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d1 : my Data = new Data () ; let d2 : my Data = new Data () ; let d3 : my Data = new Data () ; let s1 : ref [d1, d2, d3] Data = d1 . ref ; let s2 : ref [d1] ref [d2, d3] Data = s1 . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d1 : my Data = new Data () ; let d2 : my Data = new Data () ; let d3 : my Data = new Data () ; let s1 : ref [d1, d2, d3] Data = d1 . ref ; let s2 : ref [d1] ref [d2, d3] Data = s1 . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d1 : my Data = new Data () ; let d2 : my Data = new Data () ; let d3 : my Data = new Data () ; let s1 : ref [d1, d2, d3] Data = d1 . ref ; let s2 : ref [d1] ref [d2, d3] Data = s1 . move ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d1 : my Data = new Data () ; let d2 : my Data = new Data () ; let d3 : my Data = new Data () ; let s1 : ref [d1, d2, d3] Data = d1 . ref ; let s2 : ref [d1] ref [d2, d3] Data = s1 . move ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d1 : my Data = new Data () ;, let d2 : my Data = new Data () ;, let d3 : my Data = new Data () ;, let s1 : ref [d1, d2, d3] Data = d1 . ref ;, let s2 : ref [d1] ref [d2, d3] Data = s1 . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let d2 : my Data = new Data () ;, let d3 : my Data = new Data () ;, let s1 : ref [d1, d2, d3] Data = d1 . ref ;, let s2 : ref [d1] ref [d2, d3] Data = s1 . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let d3 : my Data = new Data () ;, let s1 : ref [d1, d2, d3] Data = d1 . ref ;, let s2 : ref [d1] ref [d2, d3] Data = s1 . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let s1 : ref [d1, d2, d3] Data = d1 . ref ;, let s2 : ref [d1] ref [d2, d3] Data = s1 . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                               judgment `type_statements_with_final_ty { statements: [let s2 : ref [d1] ref [d2, d3] Data = s1 . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `type_statement { statement: let s2 : ref [d1] ref [d2, d3] Data = s1 . move ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `type_expr_as { expr: s1 . move, as_ty: ref [d1] ref [d2, d3] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `sub { a: ref [d1, d2, d3] Data, b: ref [d1] ref [d2, d3] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                               judgment `sub_perms { a: ref [d1, d2, d3], b: ref [d1] ref [d2, d3], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_unique { a: ref [d1, d2, d3], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: unique(ref [d1, d2, d3]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`
                                                                 the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_unique { a: ref [d1, d2, d3], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: unique(ref [d1, d2, d3]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`
                                                                 the rule "our-sub-copy" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_owned { a: ref [d1, d2, d3], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: owned(ref [d1, d2, d3]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`
                                                                 the rule "sub_perms_relative" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `sub_perm_heads { a: LeafPerms { leaves: [ref [d1, d2, d3]] }, b: LeafPerms { leaves: [ref [d1], ref [d2, d3]] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "shared-shared" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `sub_place_perms { places_a: {d1, d2, d3}, tail_a: my, places_b: {d1}, tail_b: ref [d2, d3], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "places-places" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `all_prefix_of_any(&places_a, &places_b)`
                                                                             &places_a = {d1, d2, d3}
                                                                             &places_b = {d1}
                                                                     the rule "simplify-lhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `simplify_perm { perm: LeafPerms { leaves: [ref [d1, d2, d3]] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                         the rule "copy type" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `"flat_map"` failed at the following rule(s):
                                                                             failed at (src/file.rs:LL:CC) because
                                                                               judgment `prove_is_share { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       pattern `true` did not match value `false`
                                                                         the rule "dead_shared-up" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `"flat_map"` failed at the following rule(s):
                                                                             failed at (src/file.rs:LL:CC) because
                                                                               judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       pattern `true` did not match value `false`
                                                                     the rule "simplify-rhs" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `sub_perm_heads { a: LeafPerms { leaves: [ref [d1, d2, d3]] }, b: LeafPerms { leaves: [ref [d2, d3]] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "shared-shared" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `sub_place_perms { places_a: {d1, d2, d3}, tail_a: my, places_b: {d2, d3}, tail_b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "places-places" failed at step #0 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `all_prefix_of_any(&places_a, &places_b)`
                                                                                 &places_a = {d1, d2, d3}
                                                                                 &places_b = {d2, d3}
                                                                         the rule "simplify-lhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `simplify_perm { perm: LeafPerms { leaves: [ref [d1, d2, d3]] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                             the rule "copy type" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `"flat_map"` failed at the following rule(s):
                                                                                 failed at (src/file.rs:LL:CC) because
                                                                                   judgment `prove_is_share { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           pattern `true` did not match value `false`
                                                                             the rule "dead_shared-up" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `"flat_map"` failed at the following rule(s):
                                                                                 failed at (src/file.rs:LL:CC) because
                                                                                   judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           pattern `true` did not match value `false`
                                                                         the rule "simplify-rhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `simplify_perm { perm: LeafPerms { leaves: [ref [d2, d3]] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                             the rule "copy type" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `"flat_map"` failed at the following rule(s):
                                                                                 failed at (src/file.rs:LL:CC) because
                                                                                   judgment `prove_is_share { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           pattern `true` did not match value `false`
                                                                             the rule "dead_shared-up" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `"flat_map"` failed at the following rule(s):
                                                                                 failed at (src/file.rs:LL:CC) because
                                                                                   judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: ref [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           pattern `true` did not match value `false`"#]]);
}

#[test]
fn c4_leased_d1d2d3_subtype_of_leased_d1_leased_d2d3() {
    // This one fails because `mut[d1, d2, d3]` and `mut[d1] mut[d2, d3]` are
    // different; the latter would require that `d1` contained data leased from `d2` or `d3`.
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) {
                let d1: my Data = new Data();
                let d2: my Data = new Data();
                let d3: my Data = new Data();
                let s1: mut[d1, d2, d3] Data = d1.mut;
                let s2: mut[d1] mut[d2, d3] Data = s1.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self) -> () { let d1 : my Data = new Data () ; let d2 : my Data = new Data () ; let d3 : my Data = new Data () ; let s1 : mut [d1, d2, d3] Data = d1 . mut ; let s2 : mut [d1] mut [d2, d3] Data = s1 . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d1 : my Data = new Data () ; let d2 : my Data = new Data () ; let d3 : my Data = new Data () ; let s1 : mut [d1, d2, d3] Data = d1 . mut ; let s2 : mut [d1] mut [d2, d3] Data = s1 . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d1 : my Data = new Data () ; let d2 : my Data = new Data () ; let d3 : my Data = new Data () ; let s1 : mut [d1, d2, d3] Data = d1 . mut ; let s2 : mut [d1] mut [d2, d3] Data = s1 . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d1 : my Data = new Data () ; let d2 : my Data = new Data () ; let d3 : my Data = new Data () ; let s1 : mut [d1, d2, d3] Data = d1 . mut ; let s2 : mut [d1] mut [d2, d3] Data = s1 . move ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d1 : my Data = new Data () ; let d2 : my Data = new Data () ; let d3 : my Data = new Data () ; let s1 : mut [d1, d2, d3] Data = d1 . mut ; let s2 : mut [d1] mut [d2, d3] Data = s1 . move ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d1 : my Data = new Data () ;, let d2 : my Data = new Data () ;, let d3 : my Data = new Data () ;, let s1 : mut [d1, d2, d3] Data = d1 . mut ;, let s2 : mut [d1] mut [d2, d3] Data = s1 . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let d2 : my Data = new Data () ;, let d3 : my Data = new Data () ;, let s1 : mut [d1, d2, d3] Data = d1 . mut ;, let s2 : mut [d1] mut [d2, d3] Data = s1 . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let d3 : my Data = new Data () ;, let s1 : mut [d1, d2, d3] Data = d1 . mut ;, let s2 : mut [d1] mut [d2, d3] Data = s1 . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let s1 : mut [d1, d2, d3] Data = d1 . mut ;, let s2 : mut [d1] mut [d2, d3] Data = s1 . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                               judgment `type_statements_with_final_ty { statements: [let s2 : mut [d1] mut [d2, d3] Data = s1 . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `type_statement { statement: let s2 : mut [d1] mut [d2, d3] Data = s1 . move ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `type_expr_as { expr: s1 . move, as_ty: mut [d1] mut [d2, d3] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `sub { a: mut [d1, d2, d3] Data, b: mut [d1] mut [d2, d3] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                               judgment `sub_perms { a: mut [d1, d2, d3], b: mut [d1] mut [d2, d3], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "my-sub-copy" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_owned { a: mut [d1, d2, d3], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: owned(mut [d1, d2, d3]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`
                                                                 the rule "my-sub-owned" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_owned { a: mut [d1, d2, d3], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: owned(mut [d1, d2, d3]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`
                                                                 the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_share { a: mut [d1, d2, d3], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: shared(mut [d1, d2, d3]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`
                                                                 the rule "sub_perms_relative" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `sub_perm_heads { a: LeafPerms { leaves: [mut [d1, d2, d3]] }, b: LeafPerms { leaves: [mut [d1], mut [d2, d3]] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "leased-leased" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `sub_place_perms { places_a: {d1, d2, d3}, tail_a: my, places_b: {d1}, tail_b: mut [d2, d3], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "places-places" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `all_prefix_of_any(&places_a, &places_b)`
                                                                             &places_a = {d1, d2, d3}
                                                                             &places_b = {d1}
                                                                     the rule "simplify-lhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `simplify_perm { perm: LeafPerms { leaves: [mut [d1, d2, d3]] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                         the rule "copy type" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `"flat_map"` failed at the following rule(s):
                                                                             failed at (src/file.rs:LL:CC) because
                                                                               judgment `prove_is_share { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       pattern `true` did not match value `false`
                                                                         the rule "dead_leased-up" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `"flat_map"` failed at the following rule(s):
                                                                             failed at (src/file.rs:LL:CC) because
                                                                               judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       pattern `true` did not match value `false`
                                                                     the rule "simplify-rhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `simplify_perm { perm: LeafPerms { leaves: [mut [d1], mut [d2, d3]] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                         the rule "apply-to-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_is_share { a: mut [d2, d3], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `prove_predicate { predicate: shared(mut [d2, d3]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: mut [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   pattern `true` did not match value `false`"#]]);
}

#[test]
fn c4_leased_d1d2_leased_pair_not_subtype_of_leased_d2() {
    // This one fails because you after cancelling `d1` you don't get `d2`.
    check_program(&term(
        "
        class Pair {
            a: my Data;
            b: my Data;
        }
        class Data { }
        class Main {
            fn test[perm P](my self, pair: P Pair) where unique(P), lent(P) {
                let d1: mut[pair.a] Data = pair.a.mut;
                let d2: mut[pair.b] Data = pair.b.mut;
                let s1: mut[d1, d2] Data = d1.mut;
                let s2: mut[d2] Data = s1.move;
                let _x = self.move.consume(pair.move, s2.move);
            }

            fn consume[perm P](my self, pair: P Pair, from_b: mut[pair.b] Data) where unique(P), lent(P) { (); }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Pair { a : my Data ; b : my Data ; } class Data { } class Main { fn test [perm] (my self pair : ^perm0_0 Pair) -> () where unique(^perm0_0), lent(^perm0_0) { let d1 : mut [pair . a] Data = pair . a . mut ; let d2 : mut [pair . b] Data = pair . b . mut ; let s1 : mut [d1, d2] Data = d1 . mut ; let s2 : mut [d2] Data = s1 . move ; let _x = self . move . consume (pair . move, s2 . move) ; } fn consume [perm] (my self pair : ^perm0_0 Pair, from_b : mut [pair . b] Data) -> () where unique(^perm0_0), lent(^perm0_0) { () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d1 : mut [pair . a] Data = pair . a . mut ; let d2 : mut [pair . b] Data = pair . b . mut ; let s1 : mut [d1, d2] Data = d1 . mut ; let s2 : mut [d2] Data = s1 . move ; let _x = self . move . consume (pair . move, s2 . move) ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, pair: !perm_0 Pair}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d1 : mut [pair . a] Data = pair . a . mut ; let d2 : mut [pair . b] Data = pair . b . mut ; let s1 : mut [d1, d2] Data = d1 . mut ; let s2 : mut [d2] Data = s1 . move ; let _x = self . move . consume (pair . move, s2 . move) ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, pair: !perm_0 Pair}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d1 : mut [pair . a] Data = pair . a . mut ; let d2 : mut [pair . b] Data = pair . b . mut ; let s1 : mut [d1, d2] Data = d1 . mut ; let s2 : mut [d2] Data = s1 . move ; let _x = self . move . consume (pair . move, s2 . move) ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, pair: !perm_0 Pair}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d1 : mut [pair . a] Data = pair . a . mut ; let d2 : mut [pair . b] Data = pair . b . mut ; let s1 : mut [d1, d2] Data = d1 . mut ; let s2 : mut [d2] Data = s1 . move ; let _x = self . move . consume (pair . move, s2 . move) ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, pair: !perm_0 Pair}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d1 : mut [pair . a] Data = pair . a . mut ;, let d2 : mut [pair . b] Data = pair . b . mut ;, let s1 : mut [d1, d2] Data = d1 . mut ;, let s2 : mut [d2] Data = s1 . move ;, let _x = self . move . consume (pair . move, s2 . move) ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, pair: !perm_0 Pair}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let d2 : mut [pair . b] Data = pair . b . mut ;, let s1 : mut [d1, d2] Data = d1 . mut ;, let s2 : mut [d2] Data = s1 . move ;, let _x = self . move . consume (pair . move, s2 . move) ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, pair: !perm_0 Pair}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let s1 : mut [d1, d2] Data = d1 . mut ;, let s2 : mut [d2] Data = s1 . move ;, let _x = self . move . consume (pair . move, s2 . move) ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let s2 : mut [d2] Data = s1 . move ;, let _x = self . move . consume (pair . move, s2 . move) ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: let s2 : mut [d2] Data = s1 . move ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {self, pair, s2}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr_as { expr: s1 . move, as_ty: mut [d2] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {self, pair}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `sub { a: mut [d1, d2] Data, b: mut [d2] Data, live_after: LivePlaces { accessed: {self, pair}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                           judgment `sub_perms { a: mut [d1, d2], b: mut [d2], live_after: LivePlaces { accessed: {self, pair}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "my-sub-copy" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_owned { a: mut [d1, d2], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: owned(mut [d1, d2]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`
                                                             the rule "my-sub-owned" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_owned { a: mut [d1, d2], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: owned(mut [d1, d2]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`
                                                             the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_share { a: mut [d1, d2], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: shared(mut [d1, d2]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`
                                                             the rule "sub_perms_relative" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `sub_perm_heads { a: LeafPerms { leaves: [mut [d1, d2]] }, b: LeafPerms { leaves: [mut [d2]] }, live_after: LivePlaces { accessed: {self, pair}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "leased-leased" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `sub_place_perms { places_a: {d1, d2}, tail_a: my, places_b: {d2}, tail_b: my, live_after: LivePlaces { accessed: {self, pair}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "places-places" failed at step #0 (src/file.rs:LL:CC) because
                                                                       condition evaluted to false: `all_prefix_of_any(&places_a, &places_b)`
                                                                         &places_a = {d1, d2}
                                                                         &places_b = {d2}
                                                                 the rule "simplify-lhs" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `"flat_map"` failed at the following rule(s):
                                                                     failed at (src/file.rs:LL:CC) because
                                                                       judgment `sub_perm_heads { a: LeafPerms { leaves: [mut [pair . a]] }, b: LeafPerms { leaves: [mut [d2]] }, live_after: LivePlaces { accessed: {self, pair}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "leased-leased" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `sub_place_perms { places_a: {pair . a}, tail_a: my, places_b: {d2}, tail_b: my, live_after: LivePlaces { accessed: {self, pair}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "places-places" failed at step #0 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `all_prefix_of_any(&places_a, &places_b)`
                                                                                 &places_a = {pair . a}
                                                                                 &places_b = {d2}
                                                                         the rule "simplify-lhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `simplify_perm { perm: LeafPerms { leaves: [mut [pair . a]] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {self, pair}, traversed: {} } }` failed at the following rule(s):
                                                                             the rule "copy type" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `"flat_map"` failed at the following rule(s):
                                                                                 failed at (src/file.rs:LL:CC) because
                                                                                   judgment `prove_is_share { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       judgment `prove_predicate { predicate: shared(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           pattern `true` did not match value `false`
                                                                         the rule "simplify-rhs" failed at step #1 (src/file.rs:LL:CC) because
                                                                           judgment `sub_perm_heads { a: LeafPerms { leaves: [mut [pair . a]] }, b: LeafPerms { leaves: [mut [pair . b]] }, live_after: LivePlaces { accessed: {self, pair}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "leased-leased" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `sub_place_perms { places_a: {pair . a}, tail_a: my, places_b: {pair . b}, tail_b: my, live_after: LivePlaces { accessed: {self, pair}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "places-places" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   condition evaluted to false: `all_prefix_of_any(&places_a, &places_b)`
                                                                                     &places_a = {pair . a}
                                                                                     &places_b = {pair . b}
                                                                             the rule "simplify-lhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `simplify_perm { perm: LeafPerms { leaves: [mut [pair . a]] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {self, pair}, traversed: {} } }` failed at the following rule(s):
                                                                                 the rule "copy type" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `"flat_map"` failed at the following rule(s):
                                                                                     failed at (src/file.rs:LL:CC) because
                                                                                       judgment `prove_is_share { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                         the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           judgment `prove_predicate { predicate: shared(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               pattern `true` did not match value `false`
                                                                             the rule "simplify-rhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `simplify_perm { perm: LeafPerms { leaves: [mut [pair . b]] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {self, pair}, traversed: {} } }` failed at the following rule(s):
                                                                                 the rule "copy type" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `"flat_map"` failed at the following rule(s):
                                                                                     failed at (src/file.rs:LL:CC) because
                                                                                       judgment `prove_is_share { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                         the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           judgment `prove_predicate { predicate: shared(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               pattern `true` did not match value `false`
                                                                 the rule "simplify-rhs" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `sub_perm_heads { a: LeafPerms { leaves: [mut [d1, d2]] }, b: LeafPerms { leaves: [mut [pair . b]] }, live_after: LivePlaces { accessed: {self, pair}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "leased-leased" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `sub_place_perms { places_a: {d1, d2}, tail_a: my, places_b: {pair . b}, tail_b: my, live_after: LivePlaces { accessed: {self, pair}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "places-places" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `all_prefix_of_any(&places_a, &places_b)`
                                                                             &places_a = {d1, d2}
                                                                             &places_b = {pair . b}
                                                                     the rule "simplify-lhs" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `"flat_map"` failed at the following rule(s):
                                                                         failed at (src/file.rs:LL:CC) because
                                                                           judgment `sub_perm_heads { a: LeafPerms { leaves: [mut [pair . a]] }, b: LeafPerms { leaves: [mut [pair . b]] }, live_after: LivePlaces { accessed: {self, pair}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "leased-leased" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `sub_place_perms { places_a: {pair . a}, tail_a: my, places_b: {pair . b}, tail_b: my, live_after: LivePlaces { accessed: {self, pair}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "places-places" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   condition evaluted to false: `all_prefix_of_any(&places_a, &places_b)`
                                                                                     &places_a = {pair . a}
                                                                                     &places_b = {pair . b}
                                                                             the rule "simplify-lhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `simplify_perm { perm: LeafPerms { leaves: [mut [pair . a]] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {self, pair}, traversed: {} } }` failed at the following rule(s):
                                                                                 the rule "copy type" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `"flat_map"` failed at the following rule(s):
                                                                                     failed at (src/file.rs:LL:CC) because
                                                                                       judgment `prove_is_share { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                         the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           judgment `prove_predicate { predicate: shared(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               pattern `true` did not match value `false`
                                                                             the rule "simplify-rhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `simplify_perm { perm: LeafPerms { leaves: [mut [pair . b]] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {self, pair}, traversed: {} } }` failed at the following rule(s):
                                                                                 the rule "copy type" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `"flat_map"` failed at the following rule(s):
                                                                                     failed at (src/file.rs:LL:CC) because
                                                                                       judgment `prove_is_share { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                         the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           judgment `prove_predicate { predicate: shared(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               pattern `true` did not match value `false`
                                                                     the rule "simplify-rhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `simplify_perm { perm: LeafPerms { leaves: [mut [pair . b]] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {self, pair}, traversed: {} } }` failed at the following rule(s):
                                                                         the rule "copy type" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `"flat_map"` failed at the following rule(s):
                                                                             failed at (src/file.rs:LL:CC) because
                                                                               judgment `prove_is_share { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `prove_predicate { predicate: shared(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: mut [pair . a] Data, d2: mut [pair . b] Data, pair: !perm_0 Pair, s1: mut [d1, d2] Data}, assumptions: {unique(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       pattern `true` did not match value `false`"#]]);
}
