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
    .assert_ok(expect_test::expect!["()"]);
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
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let p : my Data = m . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: our Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let p : my Data = m . move ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: our Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr_as { expr: m . move, as_ty: my Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: our Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `sub { a: our Data, b: my Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: our Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                   judgment `sub_perms { a: our, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: our Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `prove_is_unique { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: our Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_predicate { predicate: unique(our), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: our Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                               pattern `true` did not match value `false`
                                                     the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `prove_is_unique { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: our Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_predicate { predicate: unique(our), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: our Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                               pattern `true` did not match value `false`
                                                     the rule "our-sub-copy" failed at step #2 (src/file.rs:LL:CC) because
                                                       judgment `prove_is_share { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: our Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: our Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                               pattern `true` did not match value `false`"#]]);
}

#[test]
fn c1_my_subtype_of_shared() {
    // In this test, the data is given from `n` and hence has type `my Data`.
    // But the type indicates it is shared from `m`.
    // This is less accurate than the ideal but allowed by subtyping.
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
    .assert_ok(expect_test::expect!["()"]);
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
                let n: our Data = new Data();
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
                                                 the rule "give place" failed at step #1 (src/file.rs:LL:CC) because
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
    .assert_ok(expect_test::expect!["()"]);
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
    .assert_ok(expect_test::expect!["()"]);
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
                let m: our Data = new Data();
                let p: P Data = m.move;
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
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let p : my Data = n . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: !perm_0 Data}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let p : my Data = n . move ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: !perm_0 Data}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr_as { expr: n . move, as_ty: my Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: !perm_0 Data}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: n . move, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: !perm_0 Data}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "give place" failed at step #1 (src/file.rs:LL:CC) because
                                                   no variable named `n`"#]]);
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
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let p : our Data = n . move ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: !perm_0 Data}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let p : our Data = n . move ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: !perm_0 Data}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr_as { expr: n . move, as_ty: our Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: !perm_0 Data}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: n . move, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, m: !perm_0 Data}, assumptions: {shared(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "give place" failed at step #1 (src/file.rs:LL:CC) because
                                                   no variable named `n`"#]]);
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
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let p : !perm_1 Data = m . move ;], ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, m: !perm_0 Data}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let p : !perm_1 Data = m . move ;, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, m: !perm_0 Data}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr_as { expr: m . move, as_ty: !perm_1 Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, m: !perm_0 Data}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `sub { a: !perm_0 Data, b: !perm_1 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, m: !perm_0 Data}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                   judgment `sub_perms { a: !perm_0, b: !perm_1, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, m: !perm_0 Data}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `prove_is_unique { a: !perm_0, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, m: !perm_0 Data}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_predicate { predicate: unique(!perm_0), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, m: !perm_0 Data}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                               pattern `true` did not match value `false`
                                                     the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `prove_is_unique { a: !perm_0, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, m: !perm_0 Data}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_predicate { predicate: unique(!perm_0), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, m: !perm_0 Data}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                               pattern `true` did not match value `false`
                                                     the rule "our-sub-copy" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `prove_is_owned { a: !perm_0, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, m: !perm_0 Data}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_predicate { predicate: owned(!perm_0), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, m: !perm_0 Data}, assumptions: {shared(!perm_0), shared(!perm_1), relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
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
                let m: my Data = new Data();
                let p: ref[m] Data = new Data();
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
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
                                                   judgment `sub_perms { a: my, b: mut [m], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "my-sub-copy" failed at step #2 (src/file.rs:LL:CC) because
                                                       judgment `prove_is_share { a: mut [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_predicate { predicate: shared(mut [m]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                               pattern `true` did not match value `false`
                                                     the rule "my-sub-owned" failed at step #2 (src/file.rs:LL:CC) because
                                                       judgment `prove_is_owned { a: mut [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_predicate { predicate: owned(mut [m]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                               pattern `true` did not match value `false`
                                                     the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `prove_is_share { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                               pattern `true` did not match value `false`
                                                     the rule "sub_perms_relative" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `sub_perm_heads { a: LeafPerms { leaves: [] }, b: LeafPerms { leaves: [mut [m]] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "simplify-rhs" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `simplify_perm { perm: LeafPerms { leaves: [mut [m]] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "copy type" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `"flat_map"` failed at the following rule(s):
                                                                 failed at (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_share { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                           pattern `true` did not match value `false`
                                                             the rule "dead_leased-up" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `"flat_map"` failed at the following rule(s):
                                                                 failed at (src/file.rs:LL:CC) because
                                                                   judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
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
                                                       judgment `sub_perms { a: mut [m], b: ref [m], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "my-sub-copy" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_owned { a: mut [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: owned(mut [m]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   pattern `true` did not match value `false`
                                                         the rule "my-sub-owned" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_owned { a: mut [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: owned(mut [m]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   pattern `true` did not match value `false`
                                                         the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_share { a: mut [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: shared(mut [m]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   pattern `true` did not match value `false`
                                                         the rule "sub_perms_relative" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `sub_perm_heads { a: LeafPerms { leaves: [mut [m]] }, b: LeafPerms { leaves: [ref [m]] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "simplify-lhs" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `simplify_perm { perm: LeafPerms { leaves: [mut [m]] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                 the rule "copy type" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `"flat_map"` failed at the following rule(s):
                                                                     failed at (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_share { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`
                                                                 the rule "dead_leased-up" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `"flat_map"` failed at the following rule(s):
                                                                     failed at (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`
                                                             the rule "simplify-rhs" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `simplify_perm { perm: LeafPerms { leaves: [ref [m]] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                 the rule "copy type" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `"flat_map"` failed at the following rule(s):
                                                                     failed at (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_share { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`
                                                                 the rule "dead_shared-up" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `"flat_map"` failed at the following rule(s):
                                                                     failed at (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: mut [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
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
                                                       judgment `sub_perms { a: ref [m], b: mut [m], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_unique { a: ref [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: unique(ref [m]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   pattern `true` did not match value `false`
                                                         the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_unique { a: ref [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: unique(ref [m]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   pattern `true` did not match value `false`
                                                         the rule "our-sub-copy" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_owned { a: ref [m], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: owned(ref [m]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   pattern `true` did not match value `false`
                                                         the rule "sub_perms_relative" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `sub_perm_heads { a: LeafPerms { leaves: [ref [m]] }, b: LeafPerms { leaves: [mut [m]] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "simplify-lhs" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `simplify_perm { perm: LeafPerms { leaves: [ref [m]] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                 the rule "copy type" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `"flat_map"` failed at the following rule(s):
                                                                     failed at (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_share { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`
                                                                 the rule "dead_shared-up" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `"flat_map"` failed at the following rule(s):
                                                                     failed at (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`
                                                             the rule "simplify-rhs" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `simplify_perm { perm: LeafPerms { leaves: [mut [m]] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                 the rule "copy type" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `"flat_map"` failed at the following rule(s):
                                                                     failed at (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_share { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, p: ref [m] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                               pattern `true` did not match value `false`
                                                                 the rule "dead_leased-up" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `"flat_map"` failed at the following rule(s):
                                                                     failed at (src/file.rs:LL:CC) because
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
                                                           judgment `sub_perms { a: mut [m, n], b: mut [m], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "my-sub-copy" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_owned { a: mut [m, n], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: owned(mut [m, n]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`
                                                             the rule "my-sub-owned" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_owned { a: mut [m, n], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: owned(mut [m, n]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`
                                                             the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_share { a: mut [m, n], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: shared(mut [m, n]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`
                                                             the rule "sub_perms_relative" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `sub_perm_heads { a: LeafPerms { leaves: [mut [m, n]] }, b: LeafPerms { leaves: [mut [m]] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "leased-leased" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `sub_place_perms { places_a: {m, n}, tail_a: my, places_b: {m}, tail_b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "places-places" failed at step #0 (src/file.rs:LL:CC) because
                                                                       condition evaluted to false: `all_prefix_of_any(&places_a, &places_b)`
                                                                         &places_a = {m, n}
                                                                         &places_b = {m}
                                                                 the rule "simplify-lhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `simplify_perm { perm: LeafPerms { leaves: [mut [m, n]] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                     the rule "copy type" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `"flat_map"` failed at the following rule(s):
                                                                         failed at (src/file.rs:LL:CC) because
                                                                           judgment `prove_is_share { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   pattern `true` did not match value `false`
                                                                     the rule "dead_leased-up" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `"flat_map"` failed at the following rule(s):
                                                                         failed at (src/file.rs:LL:CC) because
                                                                           judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   pattern `true` did not match value `false`
                                                                 the rule "simplify-rhs" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `simplify_perm { perm: LeafPerms { leaves: [mut [m]] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                     the rule "copy type" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `"flat_map"` failed at the following rule(s):
                                                                         failed at (src/file.rs:LL:CC) because
                                                                           judgment `prove_is_share { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   pattern `true` did not match value `false`
                                                                     the rule "dead_leased-up" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `"flat_map"` failed at the following rule(s):
                                                                         failed at (src/file.rs:LL:CC) because
                                                                           judgment `prove_is_lent { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `prove_predicate { predicate: lent(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, m: my Data, n: my Data, p: mut [m, n] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   pattern `true` did not match value `false`"#]]);
}
