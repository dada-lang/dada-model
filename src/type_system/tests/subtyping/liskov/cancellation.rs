//! # Liveness and cancellation
//!
//! When variables are dead, subtyping allows for *cancellation*, so e.g. if `d1` is dead,
//! then `shared[d1] leased[d2] Foo` is a subtype of `leased[d2] Foo`. Cancellation only
//! applies when we have a shared/leased permission applies to a leased permission.
//!
//! Consideration to test:
//!
//! * C1. Cancellation can remove "relative" permissions like `shared` and `leased`, but not owned permissions
//!   like `my` or `our` nor generic permissions (since in that case we do not know which variables they
//!   may refer to)
//! * C2. Cancellation can only occur if all variables in the permission are dead: so `shared[d1, d2]` can only
//!   be canceled if `d1` and `d2` are both dead.
//! * C3. Cancellation cannot convert a shared permission into a leased permission.
//! * C4. Subtyping must account for future cancellation. So e.g., `leased[d1, d2] Foo` cannot be a subtype of
//!   `leased[d1] leased[d2] Foo` since, if `d1` later goes dead, the supertype could be upcast
//!   to `leased[d2] Foo` but the subtype could not. That would be unsound.

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
                let p: shared[m] Data = m.share;
                let q: shared[p] shared[m] Data = p.share;
                let r: shared[m] Data = q.give;
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
                let p: leased[m] Data = m.lease;
                let q: leased[p] Data = p.lease;
                let r: leased[m] Data = q.give;
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
                let p: my my Data = m.give;
                let q: my Data = p.give;
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
                let p: our my Data = m.give;
                let q: my Data = p.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self) -> () { let m : my Data = new Data () ; let p : our my Data = m . give ; let q : my Data = p . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : my Data = new Data () ; let p : our my Data = m . give ; let q : my Data = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : my Data = new Data () ; let p : our my Data = m . give ; let q : my Data = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let m : my Data = new Data () ; let p : our my Data = m . give ; let q : my Data = p . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let m : my Data = new Data () ; let p : our my Data = m . give ; let q : my Data = p . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let m : my Data = new Data () ;, let p : our my Data = m . give ;, let q : my Data = p . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let p : our my Data = m . give ;, let q : my Data = p . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let q : my Data = p . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: our my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: let q : my Data = p . give ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: our my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr_as { expr: p . give, as_ty: my Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: our my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `sub { a: our my Data, b: my Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: our my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `sub_under { perm_a: my, a: our my Data, perm_b: my, b: my Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: our my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                           judgment `sub_red_terms { red_term_a: RedTerm { red_perm: RedPerm { perms: [our] }, red_ty: NamedTy(Data) }, red_term_b: RedTerm { red_perm: RedPerm { perms: [] }, red_ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: our my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                               judgment `sub_red_perms { a: RedPerm { perms: [our] }, b: RedPerm { perms: [] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: our my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_move { a: our, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: our my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: move(our), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: our my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `is_true`
                                                                 the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_move { a: our, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: our my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: move(our), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: our my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `is_true`
                                                                 the rule "our-sub-copy" failed at step #2 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_copy { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: our my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: copy(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: our my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `is_true`"#]]);
}

// C1. Cancellation cannot remove generic permissions `our`.

#[test]
fn c1_remove_generic_permissions() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self, p: P my Data) {
                let q: my Data = p.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self p : ^perm0_0 my Data) -> () { let q : my Data = p . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let q : my Data = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let q : my Data = p . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let q : my Data = p . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let q : my Data = p . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let q : my Data = p . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: let q : my Data = p . give ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `type_expr_as { expr: p . give, as_ty: my Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `sub { a: !perm_0 my Data, b: my Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `sub_under { perm_a: my, a: !perm_0 my Data, perm_b: my, b: my Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `sub_red_terms { red_term_a: RedTerm { red_perm: RedPerm { perms: [!perm_0] }, red_ty: NamedTy(Data) }, red_term_b: RedTerm { red_perm: RedPerm { perms: [] }, red_ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                       judgment `sub_red_perms { a: RedPerm { perms: [!perm_0] }, b: RedPerm { perms: [] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_move { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: move(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                   condition evaluted to false: `is_true`
                                                         the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_move { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: move(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                   condition evaluted to false: `is_true`
                                                         the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_owned { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: owned(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, p: !perm_0 my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                   condition evaluted to false: `is_true`"#]]);
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
                let p: shared[m] Data = m.share;
                let q: shared[p] shared[m] Data = p.share;
                let r: shared[m] Data = q.give;
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
                let p: shared[m] Data = m.share;
                let q: shared[m] Data = m.share;
                let r: shared[p, q] shared[m] Data = p.share;
                let s: shared[m] Data = r.give;
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
                let p: shared[m] Data = m.share;
                let q: shared[m] Data = m.share;
                let r: shared[p, q] shared[m] Data = p.share;
                let s: shared[m] Data = r.give;
                q.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self) -> () { let m : my Data = new Data () ; let p : shared [m] Data = m . share ; let q : shared [m] Data = m . share ; let r : shared [p, q] shared [m] Data = p . share ; let s : shared [m] Data = r . give ; q . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : my Data = new Data () ; let p : shared [m] Data = m . share ; let q : shared [m] Data = m . share ; let r : shared [p, q] shared [m] Data = p . share ; let s : shared [m] Data = r . give ; q . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : my Data = new Data () ; let p : shared [m] Data = m . share ; let q : shared [m] Data = m . share ; let r : shared [p, q] shared [m] Data = p . share ; let s : shared [m] Data = r . give ; q . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let m : my Data = new Data () ; let p : shared [m] Data = m . share ; let q : shared [m] Data = m . share ; let r : shared [p, q] shared [m] Data = p . share ; let s : shared [m] Data = r . give ; q . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let m : my Data = new Data () ; let p : shared [m] Data = m . share ; let q : shared [m] Data = m . share ; let r : shared [p, q] shared [m] Data = p . share ; let s : shared [m] Data = r . give ; q . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let m : my Data = new Data () ;, let p : shared [m] Data = m . share ;, let q : shared [m] Data = m . share ;, let r : shared [p, q] shared [m] Data = p . share ;, let s : shared [m] Data = r . give ;, q . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let p : shared [m] Data = m . share ;, let q : shared [m] Data = m . share ;, let r : shared [p, q] shared [m] Data = p . share ;, let s : shared [m] Data = r . give ;, q . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let p : shared [m] Data = m . share ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m, p}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr_as { expr: m . share, as_ty: shared [m] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m}, traversed: {} } }` failed at the following rule(s):
                                             the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: m . share, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `access_permitted { access: share, place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `env_permits_access { access: share, place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `parameters_permit_access { parameters: [my Data], access: share, place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `parameter_permits_access { parameter: my Data, access: share, place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `liens { a: my Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `some_lien { a: my Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "apply-perm-ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `some_lien { a: Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                               expression evaluated to an empty collection: `parameters`"#]]);
}

#[test]
fn c2_leased_leased_one_of_one_variables_dead() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) {
                let m: my Data = new Data();
                let p: leased[m] Data = m.lease;
                let q: leased[p] Data = p.lease;
                let r: leased[m] Data = q.give;
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
                let p: leased[m.a] Data = m.a.lease;
                let q: leased[m.b] Data = m.b.lease;
                let r: leased[p, q] Data = p.lease;
                let s: leased[m] Data = r.give;
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
                let p: leased[m] Data = m.lease;
                let q: leased[m] Data = m.lease;
                let r: leased[p, q] leased[m] Data = p.lease;
                let s: leased[m] Data = r.give;
                q.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self) -> () { let m : my Data = new Data () ; let p : leased [m] Data = m . lease ; let q : leased [m] Data = m . lease ; let r : leased [p, q] leased [m] Data = p . lease ; let s : leased [m] Data = r . give ; q . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : my Data = new Data () ; let p : leased [m] Data = m . lease ; let q : leased [m] Data = m . lease ; let r : leased [p, q] leased [m] Data = p . lease ; let s : leased [m] Data = r . give ; q . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : my Data = new Data () ; let p : leased [m] Data = m . lease ; let q : leased [m] Data = m . lease ; let r : leased [p, q] leased [m] Data = p . lease ; let s : leased [m] Data = r . give ; q . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let m : my Data = new Data () ; let p : leased [m] Data = m . lease ; let q : leased [m] Data = m . lease ; let r : leased [p, q] leased [m] Data = p . lease ; let s : leased [m] Data = r . give ; q . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let m : my Data = new Data () ; let p : leased [m] Data = m . lease ; let q : leased [m] Data = m . lease ; let r : leased [p, q] leased [m] Data = p . lease ; let s : leased [m] Data = r . give ; q . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let m : my Data = new Data () ;, let p : leased [m] Data = m . lease ;, let q : leased [m] Data = m . lease ;, let r : leased [p, q] leased [m] Data = p . lease ;, let s : leased [m] Data = r . give ;, q . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let p : leased [m] Data = m . lease ;, let q : leased [m] Data = m . lease ;, let r : leased [p, q] leased [m] Data = p . lease ;, let s : leased [m] Data = r . give ;, q . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let p : leased [m] Data = m . lease ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m, p}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr_as { expr: m . lease, as_ty: leased [m] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m}, traversed: {} } }` failed at the following rule(s):
                                             the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: m . lease, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `access_permitted { access: lease, place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `env_permits_access { access: lease, place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `parameters_permit_access { parameters: [my Data], access: lease, place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `parameter_permits_access { parameter: my Data, access: lease, place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `liens { a: my Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `some_lien { a: my Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "apply-perm-ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `some_lien { a: Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                               expression evaluated to an empty collection: `parameters`"#]]);
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
                let p: leased[m] Data = m.lease;
                let q: shared[p] leased[m] Data = p.share;
                let r: leased[m] Data = q.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self) -> () { let m : my Data = new Data () ; let p : leased [m] Data = m . lease ; let q : shared [p] leased [m] Data = p . share ; let r : leased [m] Data = q . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : my Data = new Data () ; let p : leased [m] Data = m . lease ; let q : shared [p] leased [m] Data = p . share ; let r : leased [m] Data = q . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : my Data = new Data () ; let p : leased [m] Data = m . lease ; let q : shared [p] leased [m] Data = p . share ; let r : leased [m] Data = q . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let m : my Data = new Data () ; let p : leased [m] Data = m . lease ; let q : shared [p] leased [m] Data = p . share ; let r : leased [m] Data = q . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let m : my Data = new Data () ; let p : leased [m] Data = m . lease ; let q : shared [p] leased [m] Data = p . share ; let r : leased [m] Data = q . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let m : my Data = new Data () ;, let p : leased [m] Data = m . lease ;, let q : shared [p] leased [m] Data = p . share ;, let r : leased [m] Data = q . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let p : leased [m] Data = m . lease ;, let q : shared [p] leased [m] Data = p . share ;, let r : leased [m] Data = q . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let q : shared [p] leased [m] Data = p . share ;, let r : leased [m] Data = q . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: let q : shared [p] leased [m] Data = p . share ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {q}, traversed: {} } }` failed at the following rule(s):
                                             the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr_as { expr: p . share, as_ty: shared [p] leased [m] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `sub { a: shared [p] Data, b: shared [p] leased [m] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `sub_under { perm_a: my, a: shared [p] Data, perm_b: my, b: shared [p] leased [m] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                           judgment `sub_red_terms { red_term_a: RedTerm { red_perm: RedPerm { perms: [shared [p]] }, red_ty: NamedTy(Data) }, red_term_b: RedTerm { red_perm: RedPerm { perms: [shared [p], leased [m]] }, red_ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                               judgment `sub_red_perms { a: RedPerm { perms: [shared [p]] }, b: RedPerm { perms: [shared [p], leased [m]] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_move { a: shared [p], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: move(shared [p]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `is_true`
                                                                 the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_move { a: shared [p], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: move(shared [p]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `is_true`
                                                                 the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_owned { a: shared [p], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: owned(shared [p]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `is_true`
                                                                 the rule "shared-dead" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `sub_dead_shared { place_a: p, perm_a: RedPerm { perms: [] }, b: RedPerm { perms: [shared [p], leased [m]] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "sub_dead_shared" failed at step #4 (src/file.rs:LL:CC) because
                                                                       judgment `sub_under { perm_a: our leased [m], a: my, perm_b: my, b: shared [p] leased [m], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                                           judgment `sub_red_terms { red_term_a: RedTerm { red_perm: RedPerm { perms: [our, leased [m]] }, red_ty: None }, red_term_b: RedTerm { red_perm: RedPerm { perms: [shared [p], leased [m]] }, red_ty: None }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "sub-none" failed at step #2 (src/file.rs:LL:CC) because
                                                                               judgment `sub_red_perms { a: RedPerm { perms: [our, leased [m]] }, b: RedPerm { perms: [shared [p], leased [m]] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `prove_is_move { a: our leased [m], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       judgment `prove_predicate { predicate: move(our leased [m]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                         the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                                           condition evaluted to false: `is_true`
                                                                                 the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `prove_is_move { a: our leased [m], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       judgment `prove_predicate { predicate: move(our leased [m]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                         the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                                           condition evaluted to false: `is_true`
                                                                                 the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `prove_is_owned { a: our leased [m], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       judgment `prove_predicate { predicate: owned(our leased [m]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                         the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                                           condition evaluted to false: `is_true`
                                                                 the rule "shared-vs-shared" failed at step #3 (src/file.rs:LL:CC) because
                                                                   judgment `sub_red_perms { a: RedPerm { perms: [] }, b: RedPerm { perms: [leased [m]] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "my-sub-copy" failed at step #2 (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_copy { a: leased [m], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: copy(leased [m]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `is_true`
                                                                     the rule "my-sub-owned" failed at step #2 (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_owned { a: leased [m], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: owned(leased [m]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `is_true`
                                                                     the rule "our-sub-copy" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_copy { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: copy(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data, p: leased [m] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `is_true`"#]]);
}

#[test]
fn c3_shared_leased_two_of_two_variables_dead() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) {
                let m: my Data = new Data();
                let p: leased[m] Data = m.share;
                let q: leased[m] Data = m.share;
                let r: shared[p, q] leased[m] Data = p.share;
                let s: shared[m] Data = r.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self) -> () { let m : my Data = new Data () ; let p : leased [m] Data = m . share ; let q : leased [m] Data = m . share ; let r : shared [p, q] leased [m] Data = p . share ; let s : shared [m] Data = r . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : my Data = new Data () ; let p : leased [m] Data = m . share ; let q : leased [m] Data = m . share ; let r : shared [p, q] leased [m] Data = p . share ; let s : shared [m] Data = r . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : my Data = new Data () ; let p : leased [m] Data = m . share ; let q : leased [m] Data = m . share ; let r : shared [p, q] leased [m] Data = p . share ; let s : shared [m] Data = r . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let m : my Data = new Data () ; let p : leased [m] Data = m . share ; let q : leased [m] Data = m . share ; let r : shared [p, q] leased [m] Data = p . share ; let s : shared [m] Data = r . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let m : my Data = new Data () ; let p : leased [m] Data = m . share ; let q : leased [m] Data = m . share ; let r : shared [p, q] leased [m] Data = p . share ; let s : shared [m] Data = r . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let m : my Data = new Data () ;, let p : leased [m] Data = m . share ;, let q : leased [m] Data = m . share ;, let r : shared [p, q] leased [m] Data = p . share ;, let s : shared [m] Data = r . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let p : leased [m] Data = m . share ;, let q : leased [m] Data = m . share ;, let r : shared [p, q] leased [m] Data = p . share ;, let s : shared [m] Data = r . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let p : leased [m] Data = m . share ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m, p}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr_as { expr: m . share, as_ty: leased [m] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m}, traversed: {} } }` failed at the following rule(s):
                                             the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: m . share, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `access_permitted { access: share, place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `env_permits_access { access: share, place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `parameters_permit_access { parameters: [my Data], access: share, place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `parameter_permits_access { parameter: my Data, access: share, place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `liens { a: my Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `some_lien { a: my Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "apply-perm-ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `some_lien { a: Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                               expression evaluated to an empty collection: `parameters`"#]]);
}

#[test]
fn c3_shared_leased_one_of_two_variables_dead() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) {
                let m: my Data = new Data();
                let p: shared[m] Data = m.share;
                let q: shared[m] Data = m.share;
                let r: shared[p, q] shared[m] Data = p.share;
                let s: shared[m] Data = r.give;
                q.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self) -> () { let m : my Data = new Data () ; let p : shared [m] Data = m . share ; let q : shared [m] Data = m . share ; let r : shared [p, q] shared [m] Data = p . share ; let s : shared [m] Data = r . give ; q . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : my Data = new Data () ; let p : shared [m] Data = m . share ; let q : shared [m] Data = m . share ; let r : shared [p, q] shared [m] Data = p . share ; let s : shared [m] Data = r . give ; q . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : my Data = new Data () ; let p : shared [m] Data = m . share ; let q : shared [m] Data = m . share ; let r : shared [p, q] shared [m] Data = p . share ; let s : shared [m] Data = r . give ; q . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let m : my Data = new Data () ; let p : shared [m] Data = m . share ; let q : shared [m] Data = m . share ; let r : shared [p, q] shared [m] Data = p . share ; let s : shared [m] Data = r . give ; q . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let m : my Data = new Data () ; let p : shared [m] Data = m . share ; let q : shared [m] Data = m . share ; let r : shared [p, q] shared [m] Data = p . share ; let s : shared [m] Data = r . give ; q . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let m : my Data = new Data () ;, let p : shared [m] Data = m . share ;, let q : shared [m] Data = m . share ;, let r : shared [p, q] shared [m] Data = p . share ;, let s : shared [m] Data = r . give ;, q . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let p : shared [m] Data = m . share ;, let q : shared [m] Data = m . share ;, let r : shared [p, q] shared [m] Data = p . share ;, let s : shared [m] Data = r . give ;, q . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let p : shared [m] Data = m . share ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m, p}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr_as { expr: m . share, as_ty: shared [m] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m}, traversed: {} } }` failed at the following rule(s):
                                             the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: m . share, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `access_permitted { access: share, place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `env_permits_access { access: share, place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {m}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `parameters_permit_access { parameters: [my Data], access: share, place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `parameter_permits_access { parameter: my Data, access: share, place: m, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `liens { a: my Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `some_lien { a: my Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "apply-perm-ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `some_lien { a: Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                               expression evaluated to an empty collection: `parameters`"#]]);
}

// C4. Subtyping must account for future cancellation.

#[test]
fn c4_shared_d1d2d3_not_subtype_of_shared_d1_shared_d2d3() {
    // This is interesting. It fails because `shared[d1] shared[d2, d3]`
    // is equivalent to `shared[d2, d3]` and there is clearly no subtyping relation.
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) {
                let d1: my Data = new Data();
                let d2: my Data = new Data();
                let d3: my Data = new Data();
                let s1: shared[d1, d2, d3] Data = d1.share;
                let s2: shared[d1] shared[d2, d3] Data = s1.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self) -> () { let d1 : my Data = new Data () ; let d2 : my Data = new Data () ; let d3 : my Data = new Data () ; let s1 : shared [d1, d2, d3] Data = d1 . share ; let s2 : shared [d1] shared [d2, d3] Data = s1 . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d1 : my Data = new Data () ; let d2 : my Data = new Data () ; let d3 : my Data = new Data () ; let s1 : shared [d1, d2, d3] Data = d1 . share ; let s2 : shared [d1] shared [d2, d3] Data = s1 . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d1 : my Data = new Data () ; let d2 : my Data = new Data () ; let d3 : my Data = new Data () ; let s1 : shared [d1, d2, d3] Data = d1 . share ; let s2 : shared [d1] shared [d2, d3] Data = s1 . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d1 : my Data = new Data () ; let d2 : my Data = new Data () ; let d3 : my Data = new Data () ; let s1 : shared [d1, d2, d3] Data = d1 . share ; let s2 : shared [d1] shared [d2, d3] Data = s1 . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d1 : my Data = new Data () ; let d2 : my Data = new Data () ; let d3 : my Data = new Data () ; let s1 : shared [d1, d2, d3] Data = d1 . share ; let s2 : shared [d1] shared [d2, d3] Data = s1 . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d1 : my Data = new Data () ;, let d2 : my Data = new Data () ;, let d3 : my Data = new Data () ;, let s1 : shared [d1, d2, d3] Data = d1 . share ;, let s2 : shared [d1] shared [d2, d3] Data = s1 . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let d2 : my Data = new Data () ;, let d3 : my Data = new Data () ;, let s1 : shared [d1, d2, d3] Data = d1 . share ;, let s2 : shared [d1] shared [d2, d3] Data = s1 . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let d3 : my Data = new Data () ;, let s1 : shared [d1, d2, d3] Data = d1 . share ;, let s2 : shared [d1] shared [d2, d3] Data = s1 . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let s1 : shared [d1, d2, d3] Data = d1 . share ;, let s2 : shared [d1] shared [d2, d3] Data = s1 . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                               judgment `type_statements_with_final_ty { statements: [let s2 : shared [d1] shared [d2, d3] Data = s1 . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: shared [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `type_statement { statement: let s2 : shared [d1] shared [d2, d3] Data = s1 . give ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: shared [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `type_expr_as { expr: s1 . give, as_ty: shared [d1] shared [d2, d3] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: shared [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `sub { a: shared [d1, d2, d3] Data, b: shared [d1] shared [d2, d3] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: shared [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `sub_under { perm_a: my, a: shared [d1, d2, d3] Data, perm_b: my, b: shared [d1] shared [d2, d3] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: shared [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                                   judgment `sub_red_terms { red_term_a: RedTerm { red_perm: RedPerm { perms: [shared [d1, d2, d3]] }, red_ty: NamedTy(Data) }, red_term_b: RedTerm { red_perm: RedPerm { perms: [shared [d2, d3]] }, red_ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: shared [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                                       judgment `sub_red_perms { a: RedPerm { perms: [shared [d1, d2, d3]] }, b: RedPerm { perms: [shared [d2, d3]] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: shared [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_is_move { a: shared [d1, d2, d3], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: shared [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `prove_predicate { predicate: move(shared [d1, d2, d3]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: shared [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                                   condition evaluted to false: `is_true`
                                                                         the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_is_move { a: shared [d1, d2, d3], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: shared [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `prove_predicate { predicate: move(shared [d1, d2, d3]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: shared [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                                   condition evaluted to false: `is_true`
                                                                         the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_is_owned { a: shared [d1, d2, d3], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: shared [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `prove_predicate { predicate: owned(shared [d1, d2, d3]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: shared [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                                   condition evaluted to false: `is_true`
                                                                         the rule "shared-dead" failed at step #1 (src/file.rs:LL:CC) because
                                                                           judgment `sub_dead_shared { place_a: d1, perm_a: RedPerm { perms: [] }, b: RedPerm { perms: [shared [d2, d3]] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: shared [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "sub_dead_shared" failed at step #2 (src/file.rs:LL:CC) because
                                                                               judgment `prove_is_lent { a: my Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: shared [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `prove_predicate { predicate: lent(my Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: shared [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                                       condition evaluted to false: `is_true`
                                                                         the rule "shared-vs-shared" failed at step #2 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `places_a.iter().all(|place_a|
                                                                           { places_b.iter().any(|place_b| { place_b.is_prefix_of(&place_a) }) })`"#]]);
}

#[test]
fn c4_leased_d1d2d3_subtype_of_leased_d1_leased_d2d3() {
    // This one fails because `leased[d1, d2, d3]` and `leased[d1] leased[d2, d3]` are
    // different; the latter would require that `d1` contained data leased from `d2` or `d3`.
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) {
                let d1: my Data = new Data();
                let d2: my Data = new Data();
                let d3: my Data = new Data();
                let s1: leased[d1, d2, d3] Data = d1.lease;
                let s2: leased[d1] leased[d2, d3] Data = s1.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self) -> () { let d1 : my Data = new Data () ; let d2 : my Data = new Data () ; let d3 : my Data = new Data () ; let s1 : leased [d1, d2, d3] Data = d1 . lease ; let s2 : leased [d1] leased [d2, d3] Data = s1 . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d1 : my Data = new Data () ; let d2 : my Data = new Data () ; let d3 : my Data = new Data () ; let s1 : leased [d1, d2, d3] Data = d1 . lease ; let s2 : leased [d1] leased [d2, d3] Data = s1 . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d1 : my Data = new Data () ; let d2 : my Data = new Data () ; let d3 : my Data = new Data () ; let s1 : leased [d1, d2, d3] Data = d1 . lease ; let s2 : leased [d1] leased [d2, d3] Data = s1 . give ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d1 : my Data = new Data () ; let d2 : my Data = new Data () ; let d3 : my Data = new Data () ; let s1 : leased [d1, d2, d3] Data = d1 . lease ; let s2 : leased [d1] leased [d2, d3] Data = s1 . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d1 : my Data = new Data () ; let d2 : my Data = new Data () ; let d3 : my Data = new Data () ; let s1 : leased [d1, d2, d3] Data = d1 . lease ; let s2 : leased [d1] leased [d2, d3] Data = s1 . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d1 : my Data = new Data () ;, let d2 : my Data = new Data () ;, let d3 : my Data = new Data () ;, let s1 : leased [d1, d2, d3] Data = d1 . lease ;, let s2 : leased [d1] leased [d2, d3] Data = s1 . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let d2 : my Data = new Data () ;, let d3 : my Data = new Data () ;, let s1 : leased [d1, d2, d3] Data = d1 . lease ;, let s2 : leased [d1] leased [d2, d3] Data = s1 . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let d3 : my Data = new Data () ;, let s1 : leased [d1, d2, d3] Data = d1 . lease ;, let s2 : leased [d1] leased [d2, d3] Data = s1 . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let s1 : leased [d1, d2, d3] Data = d1 . lease ;, let s2 : leased [d1] leased [d2, d3] Data = s1 . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                               judgment `type_statements_with_final_ty { statements: [let s2 : leased [d1] leased [d2, d3] Data = s1 . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: leased [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `type_statement { statement: let s2 : leased [d1] leased [d2, d3] Data = s1 . give ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: leased [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `type_expr_as { expr: s1 . give, as_ty: leased [d1] leased [d2, d3] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: leased [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `sub { a: leased [d1, d2, d3] Data, b: leased [d1] leased [d2, d3] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: leased [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `sub_under { perm_a: my, a: leased [d1, d2, d3] Data, perm_b: my, b: leased [d1] leased [d2, d3] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: leased [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                                   judgment `sub_red_terms { red_term_a: RedTerm { red_perm: RedPerm { perms: [leased [d1, d2, d3]] }, red_ty: NamedTy(Data) }, red_term_b: RedTerm { red_perm: RedPerm { perms: [leased [d1], leased [d2, d3]] }, red_ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: leased [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                                       judgment `sub_red_perms { a: RedPerm { perms: [leased [d1, d2, d3]] }, b: RedPerm { perms: [leased [d1], leased [d2, d3]] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: leased [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "leased-dead" failed at step #1 (src/file.rs:LL:CC) because
                                                                           judgment `sub_dead_leased { place_a: d1, perm_a: RedPerm { perms: [] }, b: RedPerm { perms: [leased [d1], leased [d2, d3]] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: leased [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "sub_dead_leased" failed at step #2 (src/file.rs:LL:CC) because
                                                                               judgment `prove_is_lent { a: my Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: leased [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `prove_predicate { predicate: lent(my Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: leased [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                                       condition evaluted to false: `is_true`
                                                                         the rule "leased-vs-leased" failed at step #2 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `places_a.iter().all(|place_a|
                                                                           { places_b.iter().any(|place_b| { place_b.is_prefix_of(&place_a) }) })`
                                                                         the rule "my-sub-copy" failed at step #1 (src/file.rs:LL:CC) because
                                                                           judgment `prove_is_owned { a: leased [d1, d2, d3], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: leased [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `prove_predicate { predicate: owned(leased [d1, d2, d3]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: leased [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                                   condition evaluted to false: `is_true`
                                                                         the rule "my-sub-owned" failed at step #1 (src/file.rs:LL:CC) because
                                                                           judgment `prove_is_owned { a: leased [d1, d2, d3], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: leased [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `prove_predicate { predicate: owned(leased [d1, d2, d3]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: leased [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                                   condition evaluted to false: `is_true`
                                                                         the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_is_owned { a: leased [d1, d2, d3], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: leased [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `prove_predicate { predicate: owned(leased [d1, d2, d3]), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: my Data, d2: my Data, d3: my Data, s1: leased [d1, d2, d3] Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                                   condition evaluted to false: `is_true`"#]]);
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
            fn test[perm P](my self, pair: P Pair) where move(P), lent(P) {
                let d1: leased[pair.a] Data = pair.a.lease;
                let d2: leased[pair.b] Data = pair.b.lease;
                let s1: leased[d1, d2] Data = d1.lease;
                let s2: leased[d2] Data = s1.give;
                let _x = self.give.consume(pair.give, s2.give);
            }

            fn consume[perm P](my self, pair: P Pair, from_b: leased[pair.b] Data) where move(P), lent(P) { (); }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Pair { a : my Data ; b : my Data ; } class Data { } class Main { fn test [perm] (my self pair : ^perm0_0 Pair) -> () where move(^perm0_0), lent(^perm0_0) { let d1 : leased [pair . a] Data = pair . a . lease ; let d2 : leased [pair . b] Data = pair . b . lease ; let s1 : leased [d1, d2] Data = d1 . lease ; let s2 : leased [d2] Data = s1 . give ; let _x = self . give . consume (pair . give, s2 . give) ; } fn consume [perm] (my self pair : ^perm0_0 Pair, from_b : leased [pair . b] Data) -> () where move(^perm0_0), lent(^perm0_0) { () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d1 : leased [pair . a] Data = pair . a . lease ; let d2 : leased [pair . b] Data = pair . b . lease ; let s1 : leased [d1, d2] Data = d1 . lease ; let s2 : leased [d2] Data = s1 . give ; let _x = self . give . consume (pair . give, s2 . give) ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d1 : leased [pair . a] Data = pair . a . lease ; let d2 : leased [pair . b] Data = pair . b . lease ; let s1 : leased [d1, d2] Data = d1 . lease ; let s2 : leased [d2] Data = s1 . give ; let _x = self . give . consume (pair . give, s2 . give) ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let d1 : leased [pair . a] Data = pair . a . lease ; let d2 : leased [pair . b] Data = pair . b . lease ; let s1 : leased [d1, d2] Data = d1 . lease ; let s2 : leased [d2] Data = s1 . give ; let _x = self . give . consume (pair . give, s2 . give) ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let d1 : leased [pair . a] Data = pair . a . lease ; let d2 : leased [pair . b] Data = pair . b . lease ; let s1 : leased [d1, d2] Data = d1 . lease ; let s2 : leased [d2] Data = s1 . give ; let _x = self . give . consume (pair . give, s2 . give) ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let d1 : leased [pair . a] Data = pair . a . lease ;, let d2 : leased [pair . b] Data = pair . b . lease ;, let s1 : leased [d1, d2] Data = d1 . lease ;, let s2 : leased [d2] Data = s1 . give ;, let _x = self . give . consume (pair . give, s2 . give) ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: let d1 : leased [pair . a] Data = pair . a . lease ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {self, d1, pair, pair . b}, traversed: {} } }` failed at the following rule(s):
                                     the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `type_expr_as { expr: pair . a . lease, as_ty: leased [pair . a] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {self, pair, pair . b}, traversed: {} } }` failed at the following rule(s):
                                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr { expr: pair . a . lease, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {self, pair, pair . b}, traversed: {} } }` failed at the following rule(s):
                                             the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `access_permitted { access: lease, place: pair . a, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {self, pair, pair . b}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `env_permits_access { access: lease, place: pair . a, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {self, pair, pair . b}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `parameters_permit_access { parameters: [my Main, !perm_0 Pair], access: lease, place: pair . a, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `parameter_permits_access { parameter: my Main, access: lease, place: pair . a, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `liens { a: my Main, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `some_lien { a: my Main, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "apply-perm-ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `some_lien { a: Main, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                           expression evaluated to an empty collection: `parameters`"#]]);
}
