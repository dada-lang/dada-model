//! # Subpermission
//!
//! All operations permitted by supertype must be permitted by the subtype.
//!
//! C1. This begins with edits on the data structure itself, so `our Foo` cannot be a subtype of `my Foo`
//! since the latter permits field mutation.
//!
//! C2. This also includes restrictions on what can be done in the environment. So `ref[d1] Foo` cannot
//! be a subtype of `ref[d2] Foo` since the latter permits `d1` to be modified but the subtype does not.
//! (The latter also restricts edits to `d2`, but that's ok in the supertype, it can be more restrictive.)

use crate::{dada_lang::term, type_system::check_program};
use formality_core::{test, test_util::ResultTestExt};

// C1. This begins with edits on the data structure itself, so `our Foo` cannot be a subtype of `my Foo`
// since the latter permits field mutation.

#[test]
fn c1_my_subtype_of_our() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test(my self) {
                let m: my Data = new Data();
                let p: our Data = m.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test (my self) -> () { let m : my Data = new Data () ; let p : our Data = m . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : my Data = new Data () ; let p : our Data = m . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : my Data = new Data () ; let p : our Data = m . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let m : my Data = new Data () ; let p : our Data = m . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let m : my Data = new Data () ; let p : our Data = m . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let m : my Data = new Data () ;, let p : our Data = m . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let p : our Data = m . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let p : our Data = m . move ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr_as { expr: m . move, as_ty: our Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `sub { a: my Data, b: our Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                   judgment `sub_perms { perm_a: my, perm_b: our, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub_red_perms" failed at step #2 (src/file.rs:LL:CC) because
                                                       judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Our] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub_red_perms" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Our] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "my <: unique" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_my { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "prove" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_unique { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: unique(our), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`"#]]);
}

#[test]
fn c1_our_not_subtype_of_my() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test(my self) {
                let m: our Data = new Data();
                let p: my Data = m.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test (my self) -> () { let m : our Data = new Data () ; let p : my Data = m . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : our Data = new Data () ; let p : my Data = m . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : our Data = new Data () ; let p : my Data = m . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let m : our Data = new Data () ; let p : my Data = m . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let m : our Data = new Data () ; let p : my Data = m . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let m : our Data = new Data () ;, let p : my Data = m . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: let m : our Data = new Data () ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {m}, traversed: {} } }` failed at the following rule(s):
                                     the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `type_expr_as { expr: new Data (), as_ty: our Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `sub { a: Data, b: our Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                               judgment `sub_perms { perm_a: my, perm_b: our, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub_red_perms" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Our] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub_red_perms" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Our] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "my <: unique" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_my { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "prove" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_unique { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: unique(our), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`"#]]);
}

#[test]
fn c1_my_subtype_of_shared() {
    // In this test, the data is given from `n` and hence has type `my Data`.
    // But the type indicates it is shared from `m`.
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test(my self) {
                let m: my Data = new Data();
                let n: my Data = new Data();
                let p: ref[m] Data = n.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test (my self) -> () { let m : my Data = new Data () ; let n : my Data = new Data () ; let p : ref [m] Data = n . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : my Data = new Data () ; let n : my Data = new Data () ; let p : ref [m] Data = n . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : my Data = new Data () ; let n : my Data = new Data () ; let p : ref [m] Data = n . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let m : my Data = new Data () ; let n : my Data = new Data () ; let p : ref [m] Data = n . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let m : my Data = new Data () ; let n : my Data = new Data () ; let p : ref [m] Data = n . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let m : my Data = new Data () ;, let n : my Data = new Data () ;, let p : ref [m] Data = n . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let n : my Data = new Data () ;, let p : ref [m] Data = n . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let p : ref [m] Data = n . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: let p : ref [m] Data = n . move ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr_as { expr: n . move, as_ty: ref [m] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `sub { a: my Data, b: ref [m] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                       judgment `sub_perms { perm_a: my, perm_b: ref [m], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub_red_perms" failed at step #2 (src/file.rs:LL:CC) because
                                                           judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Rfd(m)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub_red_perms" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Rfd(m)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "my <: unique" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_my { a: ref [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "prove" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_unique { a: ref [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: unique(ref [m]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`"#]]);
}

#[test]
fn c1_our_subtype_of_shared() {
    // In this test, the data is given from `n` and hence has type `our Data`.
    // But the type indicates it is shared from `m`.
    // This is less accurate than the ideal but allowed by subtyping.
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test(my self) {
                let m: my Data = new Data();
                let n: our Data = m.share;
                let p: ref[m] Data = n.move;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn c1_my_not_subtype_of_P() {
    // my is not a subtype of generic permission `P` because it may be leased
    // (which would violate compatible layout rules).
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) {
                let m: my Data = new Data();
                let p: P Data = n.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self) -> () { let m : my Data = new Data () ; let p : ^perm0_0 Data = n . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : my Data = new Data () ; let p : !perm_0 Data = n . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : my Data = new Data () ; let p : !perm_0 Data = n . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let m : my Data = new Data () ; let p : !perm_0 Data = n . move ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let m : my Data = new Data () ; let p : !perm_0 Data = n . move ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let m : my Data = new Data () ;, let p : !perm_0 Data = n . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let p : !perm_0 Data = n . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let p : !perm_0 Data = n . move ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr_as { expr: n . move, as_ty: !perm_0 Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: n . move, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "move place" failed at step #1 (src/file.rs:LL:CC) because
                                                   no variable named `n`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn c1_my_subtype_of_P_where_P_shared() {
    // my IS a subtype of generic permission `P`
    // because it is declared as `shared` and hence is layout compatible.
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) where shared(P) {
                let m: my Data = new Data();
                let p: P Data = m.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self) -> () where shared(^perm0_0) { let m : my Data = new Data () ; let p : ^perm0_0 Data = m . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : my Data = new Data () ; let p : !perm_0 Data = m . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : my Data = new Data () ; let p : !perm_0 Data = m . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let m : my Data = new Data () ; let p : !perm_0 Data = m . move ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let m : my Data = new Data () ; let p : !perm_0 Data = m . move ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let m : my Data = new Data () ;, let p : !perm_0 Data = m . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let p : !perm_0 Data = m . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let p : !perm_0 Data = m . move ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr_as { expr: m . move, as_ty: !perm_0 Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `sub { a: my Data, b: !perm_0 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                   judgment `sub_perms { perm_a: my, perm_b: !perm_0, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub_red_perms" failed at step #2 (src/file.rs:LL:CC) because
                                                       judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Var(!perm_0)] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub_red_perms" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Var(!perm_0)] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "my <: unique" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_my { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "prove" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_unique { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: unique(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: my Data}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn c1_newData_assignable_to_P_where_P_shared() {
    // my IS a subtype of generic permission `P`
    // because it is declared as `shared` and hence is layout compatible.
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) where shared(P) {
                let m: P Data = new Data();
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self) -> () where shared(^perm0_0) { let m : ^perm0_0 Data = new Data () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : !perm_0 Data = new Data () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : !perm_0 Data = new Data () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let m : !perm_0 Data = new Data () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let m : !perm_0 Data = new Data () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let m : !perm_0 Data = new Data () ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: let m : !perm_0 Data = new Data () ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `type_expr_as { expr: new Data (), as_ty: !perm_0 Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `sub { a: Data, b: !perm_0 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                               judgment `sub_perms { perm_a: my, perm_b: !perm_0, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub_red_perms" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Var(!perm_0)] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub_red_perms" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Var(!perm_0)] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "my <: unique" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_my { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "prove" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_unique { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: unique(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn c1_our_not_subtype_of_P_where_P_copy() {
    // `our` is a subtype of generic permission `P`
    // when it is declared as `copy`.
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) where shared(P) {
                let m: my Data = new Data();
                let o: our Data = m.share;
                let p: P Data = o.move;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn c1_P_not_subtype_of_my_where_P_shared() {
    // P is *not* a subtype of `my`, even though it is declared as `shared`.
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) where shared(P) {
                let m: P Data = new Data();
                let p: my Data = n.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self) -> () where shared(^perm0_0) { let m : ^perm0_0 Data = new Data () ; let p : my Data = n . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : !perm_0 Data = new Data () ; let p : my Data = n . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : !perm_0 Data = new Data () ; let p : my Data = n . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let m : !perm_0 Data = new Data () ; let p : my Data = n . move ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let m : !perm_0 Data = new Data () ; let p : my Data = n . move ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let m : !perm_0 Data = new Data () ;, let p : my Data = n . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: let m : !perm_0 Data = new Data () ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {n}, traversed: {} } }` failed at the following rule(s):
                                     the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `type_expr_as { expr: new Data (), as_ty: !perm_0 Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {n}, traversed: {} } }` failed at the following rule(s):
                                         the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `sub { a: Data, b: !perm_0 Data, live_after: LivePlaces { accessed: {n}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                               judgment `sub_perms { perm_a: my, perm_b: !perm_0, live_after: LivePlaces { accessed: {n}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub_red_perms" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Var(!perm_0)] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub_red_perms" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Var(!perm_0)] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "my <: unique" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_my { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "prove" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_unique { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: unique(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn c1_P_not_subtype_of_our_where_P_shared() {
    // P is *not* a subtype of `our`, even though it is declared as shared.
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) where shared(P) {
                let m: P Data = new Data();
                let p: our Data = n.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self) -> () where shared(^perm0_0) { let m : ^perm0_0 Data = new Data () ; let p : our Data = n . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : !perm_0 Data = new Data () ; let p : our Data = n . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : !perm_0 Data = new Data () ; let p : our Data = n . move ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let m : !perm_0 Data = new Data () ; let p : our Data = n . move ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let m : !perm_0 Data = new Data () ; let p : our Data = n . move ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let m : !perm_0 Data = new Data () ;, let p : our Data = n . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: let m : !perm_0 Data = new Data () ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {n}, traversed: {} } }` failed at the following rule(s):
                                     the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `type_expr_as { expr: new Data (), as_ty: !perm_0 Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {n}, traversed: {} } }` failed at the following rule(s):
                                         the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `sub { a: Data, b: !perm_0 Data, live_after: LivePlaces { accessed: {n}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                               judgment `sub_perms { perm_a: my, perm_b: !perm_0, live_after: LivePlaces { accessed: {n}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub_red_perms" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Var(!perm_0)] }} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub_red_perms" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Var(!perm_0)] }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "my <: unique" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_my { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "prove" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_unique { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: unique(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn c1_P_not_subtype_of_Q_where_PQ_shared() {
    // P is *not* a subtype of `our`, even though it is declared as shared.
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P, perm Q](my self) where shared(P), shared(Q) {
                let m: P Data = new Data();
                let p: Q Data = m.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm, perm] (my self) -> () where shared(^perm0_0), shared(^perm0_1) { let m : ^perm0_0 Data = new Data () ; let p : ^perm0_1 Data = m . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : !perm_0 Data = new Data () ; let p : !perm_1 Data = m . move ; }, as_ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : !perm_0 Data = new Data () ; let p : !perm_1 Data = m . move ; }, as_ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let m : !perm_0 Data = new Data () ; let p : !perm_1 Data = m . move ; }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let m : !perm_0 Data = new Data () ; let p : !perm_1 Data = m . move ; }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let m : !perm_0 Data = new Data () ;, let p : !perm_1 Data = m . move ;], ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: let m : !perm_0 Data = new Data () ;, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {m}, traversed: {} } }` failed at the following rule(s):
                                     the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `type_expr_as { expr: new Data (), as_ty: !perm_0 Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `sub { a: Data, b: !perm_0 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                               judgment `sub_perms { perm_a: my, perm_b: !perm_0, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub_red_perms" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Var(!perm_0)] }} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub_red_perms" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Var(!perm_0)] }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "my <: unique" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_my { a: !perm_0, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "prove" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_unique { a: !perm_0, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: unique(!perm_0), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn c1_newData_assignable_to_shared() {
    // Variation of [`c1_my_subtype_of_shared`][] in which
    // `new Data()` is assigned to a `ref[m] Data` variable.
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test(my self) {
                let p: ref[m] Data = new Data();
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test (my self) -> () { let p : ref [m] Data = new Data () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let p : ref [m] Data = new Data () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let p : ref [m] Data = new Data () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let p : ref [m] Data = new Data () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let p : ref [m] Data = new Data () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let p : ref [m] Data = new Data () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: let p : ref [m] Data = new Data () ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `type_expr_as { expr: new Data (), as_ty: ref [m] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `sub { a: Data, b: ref [m] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                               judgment `sub_perms { perm_a: my, perm_b: ref [m], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub_red_perms" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `red_perm { env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} }, perm: ref [m] }` failed at the following rule(s):
                                                     the rule "collect" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `some_expanded_red_chain { perm: ref [m], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "(mut | ref) from my" failed at step #2 (src/file.rs:LL:CC) because
                                                           no variable named `m`
                                                         the rule "(mut | ref) from non-my" failed at step #2 (src/file.rs:LL:CC) because
                                                           no variable named `m`
                                                         the rule "inextensible" failed at step #1 (src/file.rs:LL:CC) because
                                                           pattern `None | Some(RedLink::Our) | Some(RedLink::Var(_))` did not match value `Some(Rfd(m))`
                                                         the rule "mv" failed at step #1 (src/file.rs:LL:CC) because
                                                           pattern `Some((red_chain_head, RedLink::Mv(place)))` did not match value `Some((RedChain { links: [] }, Rfd(m)))`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn c1_my_not_subtype_of_leased() {
    // `my` is not a subtype of leased. This is actually because of the layout rules;
    // permissions-wise they would be compatible.
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test(my self) {
                let m: my Data = new Data();
                let p: mut[m] Data = new Data();
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test (my self) -> () { let m : my Data = new Data () ; let p : mut [m] Data = new Data () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : my Data = new Data () ; let p : mut [m] Data = new Data () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : my Data = new Data () ; let p : mut [m] Data = new Data () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let m : my Data = new Data () ; let p : mut [m] Data = new Data () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let m : my Data = new Data () ; let p : mut [m] Data = new Data () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let m : my Data = new Data () ;, let p : mut [m] Data = new Data () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let p : mut [m] Data = new Data () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let p : mut [m] Data = new Data () ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr_as { expr: new Data (), as_ty: mut [m] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `sub { a: Data, b: mut [m] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                   judgment `sub_perms { perm_a: my, perm_b: mut [m], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub_red_perms" failed at step #2 (src/file.rs:LL:CC) because
                                                       judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Mtd(m)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub_red_perms" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Mtd(m)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "my <: unique" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_my { a: mut [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "prove" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_owned { a: mut [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: owned(mut [m]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`"#]]);
}

#[test]
fn c1_leased_not_subtype_of_shared() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test(my self) {
                let m: my Data = new Data();
                let p: mut[m] Data = m.mut;
                let q: ref[m] Data = p.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test (my self) -> () { let m : my Data = new Data () ; let p : mut [m] Data = m . mut ; let q : ref [m] Data = p . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : my Data = new Data () ; let p : mut [m] Data = m . mut ; let q : ref [m] Data = p . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : my Data = new Data () ; let p : mut [m] Data = m . mut ; let q : ref [m] Data = p . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let m : my Data = new Data () ; let p : mut [m] Data = m . mut ; let q : ref [m] Data = p . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let m : my Data = new Data () ; let p : mut [m] Data = m . mut ; let q : ref [m] Data = p . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let m : my Data = new Data () ;, let p : mut [m] Data = m . mut ;, let q : ref [m] Data = p . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let p : mut [m] Data = m . mut ;, let q : ref [m] Data = p . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let q : ref [m] Data = p . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: let q : ref [m] Data = p . move ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr_as { expr: p . move, as_ty: ref [m] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `sub { a: mut [m] Data, b: ref [m] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                       judgment `sub_perms { perm_a: mut [m], perm_b: ref [m], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub_red_perms" failed at step #2 (src/file.rs:LL:CC) because
                                                           judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Mtd(m)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Rfd(m)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub_red_perms" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Mtd(m)] }, red_chain_b: RedChain { links: [Rfd(m)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "mut dead" failed at step #2 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`
                                                                 the rule "our vs shared" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_our { a: mut [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "prove" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_shared { a: mut [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: shared(mut [m]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`"#]]);
}

#[test]
fn c1_shared_not_subtype_of_leased() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test(my self) {
                let m: my Data = new Data();
                let p: ref[m] Data = m.ref;
                let q: mut[m] Data = p.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test (my self) -> () { let m : my Data = new Data () ; let p : ref [m] Data = m . ref ; let q : mut [m] Data = p . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : my Data = new Data () ; let p : ref [m] Data = m . ref ; let q : mut [m] Data = p . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : my Data = new Data () ; let p : ref [m] Data = m . ref ; let q : mut [m] Data = p . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let m : my Data = new Data () ; let p : ref [m] Data = m . ref ; let q : mut [m] Data = p . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let m : my Data = new Data () ; let p : ref [m] Data = m . ref ; let q : mut [m] Data = p . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let m : my Data = new Data () ;, let p : ref [m] Data = m . ref ;, let q : mut [m] Data = p . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let p : ref [m] Data = m . ref ;, let q : mut [m] Data = p . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let q : mut [m] Data = p . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: let q : mut [m] Data = p . move ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr_as { expr: p . move, as_ty: mut [m] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `sub { a: ref [m] Data, b: mut [m] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                       judgment `sub_perms { perm_a: ref [m], perm_b: mut [m], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub_red_perms" failed at step #2 (src/file.rs:LL:CC) because
                                                           judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Rfd(m)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Mtd(m)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub_red_perms" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Rfd(m)] }, red_chain_b: RedChain { links: [Mtd(m)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "our vs shared" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_our { a: ref [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "prove" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_owned { a: ref [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: owned(ref [m]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`
                                                                 the rule "ref dead" failed at step #2 (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`"#]]);
}

// C2. This also includes restrictions on what can be done in the environment. So `ref[d1] Foo` cannot
// be a subtype of `ref[d2] Foo` since the latter permits `d1` to be modified but the subtype does not.
// (The latter also restricts edits to `d2`, but that's ok in the supertype, it can be more restrictive.)

#[test]
#[allow(non_snake_case)]
fn c2_shared_m_subtype_of_shared_mn() {
    // `ref[m]` is a subtype of `ref[m, n]`: neither permit `m` to be modified.
    // The supertype `ref[m, n]` additionally prohibits `n` from being modified.
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test(my self) {
                let m: my Data = new Data();
                let n: my Data = new Data();
                let p: ref[m] Data = m.ref;
                let q: ref[m, n] Data = p.move;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn c2_leased_m_subtype_of_leased_mn() {
    // `mut[m]` is a subtype of `mut[m, n]`: neither permit `m` to be modified.
    // The supertype `mut[m, n]` additionally prohibits `n` from being modified.
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test(my self) {
                let m: my Data = new Data();
                let n: my Data = new Data();
                let p: mut[m] Data = m.mut;
                let q: mut[m, n] Data = p.move;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn c2_leased_mn_not_subtype_of_leased_m() {
    // `mut[m, n]` is not a subtype of `mut[m]`: the supertype permits `n` to be modified.
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test(my self) {
                let m: my Data = new Data();
                let n: my Data = new Data();
                let p: mut[m, n] Data = m.mut;
                let q: mut[m] Data = p.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test (my self) -> () { let m : my Data = new Data () ; let n : my Data = new Data () ; let p : mut [m, n] Data = m . mut ; let q : mut [m] Data = p . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : my Data = new Data () ; let n : my Data = new Data () ; let p : mut [m, n] Data = m . mut ; let q : mut [m] Data = p . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let m : my Data = new Data () ; let n : my Data = new Data () ; let p : mut [m, n] Data = m . mut ; let q : mut [m] Data = p . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let m : my Data = new Data () ; let n : my Data = new Data () ; let p : mut [m, n] Data = m . mut ; let q : mut [m] Data = p . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let m : my Data = new Data () ; let n : my Data = new Data () ; let p : mut [m, n] Data = m . mut ; let q : mut [m] Data = p . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let m : my Data = new Data () ;, let n : my Data = new Data () ;, let p : mut [m, n] Data = m . mut ;, let q : mut [m] Data = p . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let n : my Data = new Data () ;, let p : mut [m, n] Data = m . mut ;, let q : mut [m] Data = p . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let p : mut [m, n] Data = m . mut ;, let q : mut [m] Data = p . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let q : mut [m] Data = p . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: let q : mut [m] Data = p . move ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr_as { expr: p . move, as_ty: mut [m] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `sub { a: mut [m, n] Data, b: mut [m] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                           judgment `sub_perms { perm_a: mut [m, n], perm_b: mut [m], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub_red_perms" failed at step #2 (src/file.rs:LL:CC) because
                                                               judgment `"flat_map"` failed at the following rule(s):
                                                                 failed at (src/file.rs:LL:CC) because
                                                                   judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Mtd(n)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Mtd(m)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "sub_red_perms" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Mtd(n)] }, red_chain_b: RedChain { links: [Mtd(m)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "mut dead" failed at step #2 (src/file.rs:LL:CC) because
                                                                           judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   pattern `true` did not match value `false`
                                                                         the rule "mut vs mut" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                                                             place_b = m
                                                                             &place_a = n
                                                                         the rule "our vs shared" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_is_our { a: mut [n], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "prove" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `prove_is_shared { a: mut [n], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `prove_predicate { predicate: shared(mut [n]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       pattern `true` did not match value `false`"#]]);
}
