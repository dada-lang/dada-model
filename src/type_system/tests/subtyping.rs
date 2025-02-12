//! Tests for subtyping. These tests can be grouped into various categories.
//!
//! ## Liskov Substitution Principle (LSP)
//!
//! The "Liskov Substitution Principle" is that if T1 <: T2, then a value of type T1 can be
//! substituted for a value of type T2 and nothing can go wrong. The "liskov" directory
//! aims to systematically explore this area.
//!
//! ## Other stuff
//!
//! The other tests here need to be categorized. =)

use crate::{dada_lang::term, type_system::check_program};
use formality_core::{test, test_util::ResultTestExt};

mod liskov;

#[test]
#[allow(non_snake_case)]
fn forall_P_give_from_my_d1_P_d2_to_shared_d2() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self, d1: my Data, d2: P Data) -> shared[d2] Data {
                d1.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
fn give_from_my_d1_to_our_d2() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test(my self, d1: my Data) -> our Data {
                d1.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn give_from_our_Data_to_shared_self() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test(my self) -> shared[self] Data {
                let d: our Data = new Data();
                d.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

/// `our` is a subtype of `copy(P)`.
#[test]
#[allow(non_snake_case)]
fn give_from_our_Data_to_copy_P() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) -> P Data
            where
              copy(P)
            {
                let d: our Data = new Data();
                d.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

/// `our` is not a subtype of arbitrary P.
#[test]
#[allow(non_snake_case)]
fn give_from_our_Data_to_any_P() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) -> P Data
            {
                let d: our Data = new Data();
                d.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self) -> ^perm0_0 Data { let d : our Data = new Data () ; d . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d : our Data = new Data () ; d . give ; }, as_ty: !perm_0 Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d : our Data = new Data () ; d . give ; }, as_ty: !perm_0 Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: our Data, b: !perm_0 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: our Data, chain_b: Chain { liens: [] }, b: !perm_0 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #4 (src/file.rs:LL:CC) because
                               judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [Our] }, ty: NamedTy(Data) }, ty_chains_b: {TyChain { chain: Chain { liens: [Variable(!perm_0)] }, ty: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [Our] }, ty: NamedTy(Data) }, ty_chain_b: TyChain { chain: Chain { liens: [Variable(!perm_0)] }, ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_chains { chain_a: Chain { liens: [Our] }, chain_b: Chain { liens: [Variable(!perm_0)] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "my-sub-copy" failed at step #1 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_moved(&env)`
                                             chain_a = Chain { liens: [Our] }
                                             &env = Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }
                                         the rule "my-sub-owned" failed at step #1 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_moved(&env)`
                                             chain_a = Chain { liens: [Our] }
                                             &env = Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }
                                         the rule "our-sub-copy" failed at step #2 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_b.is_copy(&env)`
                                             chain_b = Chain { liens: [Variable(!perm_0)] }
                                             &env = Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }"#]]);
}

/// `our` is not a subtype of arbitrary P.
#[test]
#[allow(non_snake_case)]
fn give_from_our_Data_to_leased_P() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self) -> P Data
            where
                move(P),
                lent(P),
            {
                let d: our Data = new Data();
                d.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self) -> ^perm0_0 Data where move(^perm0_0), lent(^perm0_0) { let d : our Data = new Data () ; d . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d : our Data = new Data () ; d . give ; }, as_ty: !perm_0 Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d : our Data = new Data () ; d . give ; }, as_ty: !perm_0 Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: our Data, b: !perm_0 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: our Data, chain_b: Chain { liens: [] }, b: !perm_0 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #4 (src/file.rs:LL:CC) because
                               judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [Our] }, ty: NamedTy(Data) }, ty_chains_b: {TyChain { chain: Chain { liens: [Variable(!perm_0)] }, ty: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [Our] }, ty: NamedTy(Data) }, ty_chain_b: TyChain { chain: Chain { liens: [Variable(!perm_0)] }, ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_chains { chain_a: Chain { liens: [Our] }, chain_b: Chain { liens: [Variable(!perm_0)] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "my-sub-copy" failed at step #1 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_moved(&env)`
                                             chain_a = Chain { liens: [Our] }
                                             &env = Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }
                                         the rule "my-sub-owned" failed at step #1 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_moved(&env)`
                                             chain_a = Chain { liens: [Our] }
                                             &env = Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }
                                         the rule "our-sub-copy" failed at step #2 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_b.is_copy(&env)`
                                             chain_b = Chain { liens: [Variable(!perm_0)] }
                                             &env = Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }"#]]);
}

#[test]
fn give_from_my_d1_our_d2_to_given_d2() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test(my self, d1: my Data, d2: our Data) -> given[d2] Data {
                d1.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

/// Return "given" from `d1` and give from `d1`.
/// It is indistinguishable as both of them are `our` Data, so the result is `our`.
#[test]
fn share_from_our_d1_our_d2_to_given_d1() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test(my self, d1: our Data, d2: our Data) -> given[d1] Data {
                d1.share;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

/// Return "given" from `d2` even though we really give from `d1`.
/// It is indistinguishable as both of them are `our` Data, so the result is `our`.
#[test]
fn share_from_our_d1_our_d2_to_given_d2() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test(my self, d1: our Data, d2: our Data) -> given[d2] Data {
                d1.share;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

/// Return "given" from `d2` even though we really give from `d1`.
/// It is indistinguishable as both of them are `our` Data, so the result is `our`.
#[test]
fn share_from_local_to_our() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test(my self, d1: our Data, d2: our Data) -> given[d2] Data {
                let d = new Data();
                d.share;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test (my self d1 : our Data, d2 : our Data) -> given [d2] Data { let d = new Data () ; d . share ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d = new Data () ; d . share ; }, as_ty: given [d2] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d = new Data () ; d . share ; }, as_ty: given [d2] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: shared [d] Data, b: given [d2] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: shared [d] Data, chain_b: Chain { liens: [] }, b: given [d2] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #4 (src/file.rs:LL:CC) because
                               judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [Shared(d)] }, ty: NamedTy(Data) }, ty_chains_b: {TyChain { chain: Chain { liens: [Our] }, ty: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [Shared(d)] }, ty: NamedTy(Data) }, ty_chain_b: TyChain { chain: Chain { liens: [Our] }, ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_chains { chain_a: Chain { liens: [Shared(d)] }, chain_b: Chain { liens: [Our] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Shared(d)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 }
                                         the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Shared(d)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 }
                                         the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Shared(d)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 }
                                         the rule "shared-dead" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `prove_is_lent { a: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: lent(Data), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                   condition evaluted to false: `is_true`"#]]);
}

#[test]
fn provide_shared_from_d1_expect_shared_from_d1() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test(my self, d1: my Data, d2: my Data) -> shared[d1] Data {
                d1.share;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
fn provide_shared_from_d2_expect_shared_from_d1() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test(my self, d1: my Data, d2: my Data) -> shared[d1] Data {
                d2.share;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test (my self d1 : my Data, d2 : my Data) -> shared [d1] Data { d2 . share ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { d2 . share ; }, as_ty: shared [d1] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d2 . share ; }, as_ty: shared [d1] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: shared [d2] Data, b: shared [d1] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: shared [d2] Data, chain_b: Chain { liens: [] }, b: shared [d1] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #4 (src/file.rs:LL:CC) because
                               judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [Shared(d2)] }, ty: NamedTy(Data) }, ty_chains_b: {TyChain { chain: Chain { liens: [Shared(d1)] }, ty: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [Shared(d2)] }, ty: NamedTy(Data) }, ty_chain_b: TyChain { chain: Chain { liens: [Shared(d1)] }, ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_chains { chain_a: Chain { liens: [Shared(d2)] }, chain_b: Chain { liens: [Shared(d1)] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Shared(d2)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }
                                         the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Shared(d2)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }
                                         the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Shared(d2)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }
                                         the rule "shared-dead" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `prove_is_lent { a: my Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: lent(my Data), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                   condition evaluted to false: `is_true`
                                         the rule "shared-vs-shared" failed at step #2 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                             place_b = d1
                                             &place_a = d2"#]]);
}

#[test]
fn provide_shared_from_d2_expect_shared_from_d1_or_d2() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test(my self, d1: my Data, d2: my Data) -> shared[d1, d2] Data {
                d2.share;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
fn provide_shared_from_d1_next_expect_shared_from_d1() {
    check_program(&term(
        "
        class Data {
            next: my Data;
        }

        class Main {
            fn test(my self, d1: my Data, d2: my Data) -> shared[d1] Data {
                d1.next.share;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
fn provide_shared_from_d1_next_expect_shared_from_d2() {
    check_program(&term(
        "
        class Data {
            next: my Data;
        }

        class Main {
            fn test(my self, d1: my Data, d2: my Data) -> shared[d2] Data {
                d1.next.share;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { next : my Data ; } class Main { fn test (my self d1 : my Data, d2 : my Data) -> shared [d2] Data { d1 . next . share ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { d1 . next . share ; }, as_ty: shared [d2] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . next . share ; }, as_ty: shared [d2] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: shared [d1 . next] Data, b: shared [d2] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: shared [d1 . next] Data, chain_b: Chain { liens: [] }, b: shared [d2] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #4 (src/file.rs:LL:CC) because
                               judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [Shared(d1 . next)] }, ty: NamedTy(Data) }, ty_chains_b: {TyChain { chain: Chain { liens: [Shared(d2)] }, ty: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [Shared(d1 . next)] }, ty: NamedTy(Data) }, ty_chain_b: TyChain { chain: Chain { liens: [Shared(d2)] }, ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_chains { chain_a: Chain { liens: [Shared(d1 . next)] }, chain_b: Chain { liens: [Shared(d2)] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Shared(d1 . next)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }
                                         the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Shared(d1 . next)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }
                                         the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Shared(d1 . next)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }
                                         the rule "shared-dead" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `prove_is_lent { a: my my Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: lent(my my Data), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                   condition evaluted to false: `is_true`
                                         the rule "shared-vs-shared" failed at step #2 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                             place_b = d2
                                             &place_a = d1 . next"#]]);
}

#[test]
fn provide_shared_from_d1_expect_shared_from_d1_next() {
    check_program(&term(
        "
        class Data {
            next: my Data;
        }

        class Main {
            fn test(my self, d1: my Data, d2: my Data) -> shared[d1.next] Data {
                d1.share;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { next : my Data ; } class Main { fn test (my self d1 : my Data, d2 : my Data) -> shared [d1 . next] Data { d1 . share ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { d1 . share ; }, as_ty: shared [d1 . next] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . share ; }, as_ty: shared [d1 . next] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: shared [d1] Data, b: shared [d1 . next] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: shared [d1] Data, chain_b: Chain { liens: [] }, b: shared [d1 . next] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #4 (src/file.rs:LL:CC) because
                               judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [Shared(d1)] }, ty: NamedTy(Data) }, ty_chains_b: {TyChain { chain: Chain { liens: [Shared(d1 . next)] }, ty: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [Shared(d1)] }, ty: NamedTy(Data) }, ty_chain_b: TyChain { chain: Chain { liens: [Shared(d1 . next)] }, ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_chains { chain_a: Chain { liens: [Shared(d1)] }, chain_b: Chain { liens: [Shared(d1 . next)] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Shared(d1)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }
                                         the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Shared(d1)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }
                                         the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Shared(d1)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }
                                         the rule "shared-dead" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `prove_is_lent { a: my Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: lent(my Data), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                   condition evaluted to false: `is_true`
                                         the rule "shared-vs-shared" failed at step #2 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                             place_b = d1 . next
                                             &place_a = d1"#]]);
}

#[test]
fn provide_leased_from_d1_next_expect_shared_from_d1() {
    check_program(&term(
        "
        class Data {
            next: my Data;
        }

        class Main {
            fn test(my self, d1: my Data, d2: my Data) -> shared[d1] Data {
                d1.next.lease;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { next : my Data ; } class Main { fn test (my self d1 : my Data, d2 : my Data) -> shared [d1] Data { d1 . next . lease ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { d1 . next . lease ; }, as_ty: shared [d1] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . next . lease ; }, as_ty: shared [d1] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: leased [d1 . next] Data, b: shared [d1] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: leased [d1 . next] Data, chain_b: Chain { liens: [] }, b: shared [d1] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #4 (src/file.rs:LL:CC) because
                               judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [Leased(d1 . next)] }, ty: NamedTy(Data) }, ty_chains_b: {TyChain { chain: Chain { liens: [Shared(d1)] }, ty: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [Leased(d1 . next)] }, ty: NamedTy(Data) }, ty_chain_b: TyChain { chain: Chain { liens: [Shared(d1)] }, ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_chains { chain_a: Chain { liens: [Leased(d1 . next)] }, chain_b: Chain { liens: [Shared(d1)] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "leased-dead" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `prove_is_lent { a: my my Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: lent(my my Data), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                   condition evaluted to false: `is_true`
                                         the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Leased(d1 . next)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }
                                         the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Leased(d1 . next)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }
                                         the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Leased(d1 . next)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn shared_from_P_d1_to_given_from_P_d1() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self, d1: P Data, d2: our Data) -> given[d1] Data {
                d1.share;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self d1 : ^perm0_0 Data, d2 : our Data) -> given [d1] Data { d1 . share ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { d1 . share ; }, as_ty: given [d1] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . share ; }, as_ty: given [d1] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: shared [d1] Data, b: given [d1] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: shared [d1] Data, chain_b: Chain { liens: [] }, b: given [d1] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #4 (src/file.rs:LL:CC) because
                               judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [Shared(d1)] }, ty: NamedTy(Data) }, ty_chains_b: {TyChain { chain: Chain { liens: [Variable(!perm_0)] }, ty: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [Shared(d1)] }, ty: NamedTy(Data) }, ty_chain_b: TyChain { chain: Chain { liens: [Variable(!perm_0)] }, ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_chains { chain_a: Chain { liens: [Shared(d1)] }, chain_b: Chain { liens: [Variable(!perm_0)] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Shared(d1)] }
                                             &env = Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }
                                         the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Shared(d1)] }
                                             &env = Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }
                                         the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Shared(d1)] }
                                             &env = Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }
                                         the rule "shared-dead" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `prove_is_lent { a: !perm_0 Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: lent(!perm_0 Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                   condition evaluted to false: `is_true`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn given_from_P_d1_to_given_from_P_d1() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self, d1: P Data, d2: our Data) -> given[d1] Data {
                d1.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn given_from_P_d1_to_given_from_P_d2() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P, perm Q](my self, d1: P Data, d2: P Data) -> given[d2] Data {
                d1.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn given_from_P_d1_to_given_from_Q_d2() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P, perm Q](my self, d1: P Data, d2: Q Data) -> given[d2] Data {
                d1.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm, perm] (my self d1 : ^perm0_0 Data, d2 : ^perm0_1 Data) -> given [d2] Data { d1 . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { d1 . give ; }, as_ty: given [d2] Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . give ; }, as_ty: given [d2] Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: !perm_0 Data, b: given [d2] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: !perm_0 Data, chain_b: Chain { liens: [] }, b: given [d2] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #4 (src/file.rs:LL:CC) because
                               judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [Variable(!perm_0)] }, ty: NamedTy(Data) }, ty_chains_b: {TyChain { chain: Chain { liens: [Variable(!perm_1)] }, ty: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [Variable(!perm_0)] }, ty: NamedTy(Data) }, ty_chain_b: TyChain { chain: Chain { liens: [Variable(!perm_1)] }, ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_chains { chain_a: Chain { liens: [Variable(!perm_0)] }, chain_b: Chain { liens: [Variable(!perm_1)] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Variable(!perm_0)] }
                                             &env = Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }
                                         the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Variable(!perm_0)] }
                                             &env = Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }
                                         the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Variable(!perm_0)] }
                                             &env = Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn shared_from_P_d1_to_shared_from_P_d1() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P, perm Q](my self, d1: P Data, d2: P Data) -> shared[d1] Data {
                d1.share;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect![["()"]]);
}

#[test]
#[allow(non_snake_case)]
fn shared_from_P_d1_to_shared_from_P_d2() {
    // Interesting example: we declare `shared[d2]` but return `shared[d1]`.
    // Even though both of them have permission `P`, we give an error.
    // The distinction of which `P` we shared from is important: we are not going to be incrementing
    // the ref count, so if `d1` were dropped, which the type signature suggests would be ok,
    // then the data would be freed.
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P, perm Q](my self, d1: P Data, d2: P Data) -> shared[d2] Data {
                d1.share;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm, perm] (my self d1 : ^perm0_0 Data, d2 : ^perm0_0 Data) -> shared [d2] Data { d1 . share ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { d1 . share ; }, as_ty: shared [d2] Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . share ; }, as_ty: shared [d2] Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: shared [d1] Data, b: shared [d2] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: shared [d1] Data, chain_b: Chain { liens: [] }, b: shared [d2] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #4 (src/file.rs:LL:CC) because
                               judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [Shared(d1)] }, ty: NamedTy(Data) }, ty_chains_b: {TyChain { chain: Chain { liens: [Shared(d2)] }, ty: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [Shared(d1)] }, ty: NamedTy(Data) }, ty_chain_b: TyChain { chain: Chain { liens: [Shared(d2)] }, ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_chains { chain_a: Chain { liens: [Shared(d1)] }, chain_b: Chain { liens: [Shared(d2)] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Shared(d1)] }
                                             &env = Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }
                                         the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Shared(d1)] }
                                             &env = Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }
                                         the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Shared(d1)] }
                                             &env = Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }
                                         the rule "shared-dead" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `prove_is_lent { a: !perm_0 Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: lent(!perm_0 Data), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                   condition evaluted to false: `is_true`
                                         the rule "shared-vs-shared" failed at step #2 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                             place_b = d2
                                             &place_a = d1"#]]);
}

/// Test for a case where the `leased[pair2] in the type of `data` is not implied by the `shared[pair1]`.
/// This type is actually semi uninhabitable.
#[test]
#[allow(non_snake_case)]
fn shared_pair1_leased_pair2_to_shared_pair1() {
    check_program(&term(
        "
        class Pair {
            d1: Data;
            d2: Data;
        }
        class Data {
        }
        class Main {
            fn test(my self, pair1: Pair, pair2: Pair, data: shared[pair1] leased[pair2] Data) -> shared[pair1] Data {
                data.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Pair { d1 : Data ; d2 : Data ; } class Data { } class Main { fn test (my self pair1 : Pair, pair2 : Pair, data : shared [pair1] leased [pair2] Data) -> shared [pair1] Data { data . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { data . give ; }, as_ty: shared [pair1] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: shared [pair1] leased [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { data . give ; }, as_ty: shared [pair1] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: shared [pair1] leased [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: shared [pair1] leased [pair2] Data, b: shared [pair1] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: shared [pair1] leased [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: shared [pair1] leased [pair2] Data, chain_b: Chain { liens: [] }, b: shared [pair1] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: shared [pair1] leased [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #4 (src/file.rs:LL:CC) because
                               judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [Shared(pair1), Leased(pair2)] }, ty: NamedTy(Data) }, ty_chains_b: {TyChain { chain: Chain { liens: [Shared(pair1)] }, ty: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: shared [pair1] leased [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [Shared(pair1), Leased(pair2)] }, ty: NamedTy(Data) }, ty_chain_b: TyChain { chain: Chain { liens: [Shared(pair1)] }, ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: shared [pair1] leased [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_chains { chain_a: Chain { liens: [Shared(pair1), Leased(pair2)] }, chain_b: Chain { liens: [Shared(pair1)] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: shared [pair1] leased [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Shared(pair1), Leased(pair2)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: shared [pair1] leased [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 }
                                         the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Shared(pair1), Leased(pair2)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: shared [pair1] leased [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 }
                                         the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Shared(pair1), Leased(pair2)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: shared [pair1] leased [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 }
                                         the rule "shared-dead" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `prove_is_lent { a: Pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: shared [pair1] leased [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: lent(Pair), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: shared [pair1] leased [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                   condition evaluted to false: `is_true`
                                         the rule "shared-vs-shared" failed at step #3 (src/file.rs:LL:CC) because
                                           judgment `sub_chains { chain_a: Chain { liens: [Leased(pair2)] }, chain_b: Chain { liens: [] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: shared [pair1] leased [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "leased-dead" failed at step #2 (src/file.rs:LL:CC) because
                                               judgment `prove_is_lent { a: Pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: shared [pair1] leased [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `prove_predicate { predicate: lent(Pair), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: shared [pair1] leased [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                       condition evaluted to false: `is_true`
                                             the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                               condition evaluted to false: `chain_a.is_owned(&env)`
                                                 chain_a = Chain { liens: [Leased(pair2)] }
                                                 &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: shared [pair1] leased [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 }
                                             the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                               condition evaluted to false: `chain_a.is_owned(&env)`
                                                 chain_a = Chain { liens: [Leased(pair2)] }
                                                 &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: shared [pair1] leased [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 }
                                             the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                               condition evaluted to false: `chain_a.is_owned(&env)`
                                                 chain_a = Chain { liens: [Leased(pair2)] }
                                                 &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: shared [pair1] leased [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 }"#]]);
}
#[test]
#[allow(non_snake_case)]
fn our_leased_to_our() {
    check_program(&term(
        "
        class Pair {
            d1: Data;
            d2: Data;
        }
        class Data {
        }
        class Main {
            fn test(my self, pair: Pair, data: our leased[pair] Data) -> our Data {
                data.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Pair { d1 : Data ; d2 : Data ; } class Data { } class Main { fn test (my self pair : Pair, data : our leased [pair] Data) -> our Data { data . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { data . give ; }, as_ty: our Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { data . give ; }, as_ty: our Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: our leased [pair] Data, b: our Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: our leased [pair] Data, chain_b: Chain { liens: [] }, b: our Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #4 (src/file.rs:LL:CC) because
                               judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [Our, Leased(pair)] }, ty: NamedTy(Data) }, ty_chains_b: {TyChain { chain: Chain { liens: [Our] }, ty: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [Our, Leased(pair)] }, ty: NamedTy(Data) }, ty_chain_b: TyChain { chain: Chain { liens: [Our] }, ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_chains { chain_a: Chain { liens: [Our, Leased(pair)] }, chain_b: Chain { liens: [Our] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Our, Leased(pair)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 }
                                         the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Our, Leased(pair)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 }
                                         the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Our, Leased(pair)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 }
                                         the rule "our-vs-our" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `sub_chains { chain_a: Chain { liens: [Leased(pair)] }, chain_b: Chain { liens: [] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "leased-dead" failed at step #2 (src/file.rs:LL:CC) because
                                               judgment `prove_is_lent { a: Pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `prove_predicate { predicate: lent(Pair), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                       condition evaluted to false: `is_true`
                                             the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                               condition evaluted to false: `chain_a.is_owned(&env)`
                                                 chain_a = Chain { liens: [Leased(pair)] }
                                                 &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 }
                                             the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                               condition evaluted to false: `chain_a.is_owned(&env)`
                                                 chain_a = Chain { liens: [Leased(pair)] }
                                                 &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 }
                                             the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                               condition evaluted to false: `chain_a.is_owned(&env)`
                                                 chain_a = Chain { liens: [Leased(pair)] }
                                                 &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn our_leased_pair_to_our_leased_pair() {
    check_program(&term(
        "
        class Pair {
            d1: Data;
            d2: Data;
        }
        class Data {
        }
        class Main {
            fn test(my self, pair: Pair, data: our leased[pair] Data) -> our leased[pair] Data {
                data.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn our_leased_pair_d1_to_our_leased_pair() {
    check_program(&term(
        "
        class Pair {
            d1: Data;
            d2: Data;
        }
        class Data {
        }
        class Main {
            fn test(my self, pair: Pair, data: our leased[pair.d1] Data) -> our leased[pair] Data {
                data.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn shared_vec_my_Data_to_shared_vec_my_Data() {
    check_program(&term(
        "
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(my self, source: my Vec[my Data], data: shared[source] Vec[my Data]) -> shared[source] Vec[my Data] {
                data.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn shared_vec_my_Data_to_shared_vec_shared_Data() {
    check_program(&term(
        "
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(my self, source: my Vec[my Data], data: shared[source] Vec[my Data]) -> shared[source] Vec[shared[source] Data] {
                data.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn leased_vec_my_Data_to_leased_vec_my_Data() {
    check_program(&term(
        "
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(my self, source: my Vec[my Data], data: leased[source] Vec[my Data]) -> leased[source] Vec[my Data] {
                data.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn leased_vec_my_Data_to_leased_vec_leased_Data() {
    check_program(&term(
        "
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(my self, source: my Vec[my Data], data: leased[source] Vec[my Data]) -> leased[source] Vec[leased[source] Data] {
                data.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Vec [ty] { } class Data { } class Main { fn test (my self source : my Vec[my Data], data : leased [source] Vec[my Data]) -> leased [source] Vec[leased [source] Data] { data . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { data . give ; }, as_ty: leased [source] Vec[leased [source] Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { data . give ; }, as_ty: leased [source] Vec[leased [source] Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: leased [source] Vec[my Data], b: leased [source] Vec[leased [source] Data], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: leased [source] Vec[my Data], chain_b: Chain { liens: [] }, b: leased [source] Vec[leased [source] Data], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #4 (src/file.rs:LL:CC) because
                               judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [Leased(source)] }, ty: NamedTy(Vec[my Data]) }, ty_chains_b: {TyChain { chain: Chain { liens: [Leased(source)] }, ty: NamedTy(Vec[leased [source] Data]) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [Leased(source)] }, ty: NamedTy(Vec[my Data]) }, ty_chain_b: TyChain { chain: Chain { liens: [Leased(source)] }, ty: NamedTy(Vec[leased [source] Data]) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #7 (src/file.rs:LL:CC) because
                                       judgment `sub_generic_parameter { variances: [], a: my Data, b: leased [source] Data, liens_a: Chain { liens: [Leased(source)] }, liens_b: Chain { liens: [Leased(source)] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "covariant-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `perms_b.is_copy(&env)`
                                             perms_b = Chain { liens: [Leased(source)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 }
                                         the rule "covariant-owned" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `perms_b.is_owned(&env)`
                                             perms_b = Chain { liens: [Leased(source)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 }
                                         the rule "invariant" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `sub { a: my Data, b: leased [source] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: my Data, chain_b: Chain { liens: [] }, b: leased [source] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub" failed at step #4 (src/file.rs:LL:CC) because
                                                   judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [] }, ty: NamedTy(Data) }, ty_chains_b: {TyChain { chain: Chain { liens: [Leased(source)] }, ty: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [] }, ty: NamedTy(Data) }, ty_chain_b: TyChain { chain: Chain { liens: [Leased(source)] }, ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                                           judgment `sub_chains { chain_a: Chain { liens: [] }, chain_b: Chain { liens: [Leased(source)] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "my-sub-copy" failed at step #2 (src/file.rs:LL:CC) because
                                                               condition evaluted to false: `chain_b.is_copy(&env)`
                                                                 chain_b = Chain { liens: [Leased(source)] }
                                                                 &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 }
                                                             the rule "my-sub-owned" failed at step #2 (src/file.rs:LL:CC) because
                                                               condition evaluted to false: `chain_b.is_owned(&env)`
                                                                 chain_b = Chain { liens: [Leased(source)] }
                                                                 &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 }
                                                             the rule "our-sub-copy" failed at step #1 (src/file.rs:LL:CC) because
                                                               condition evaluted to false: `chain_a.is_copy(&env)`
                                                                 chain_a = Chain { liens: [] }
                                                                 &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn leased_vec_leased_Data_to_leased_vec_my_Data() {
    check_program(&term(
        "
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(my self, source: my Vec[my Data], data: leased[source] Vec[leased[source] Data]) -> leased[source] Vec[my Data] {
                data.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Vec [ty] { } class Data { } class Main { fn test (my self source : my Vec[my Data], data : leased [source] Vec[leased [source] Data]) -> leased [source] Vec[my Data] { data . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { data . give ; }, as_ty: leased [source] Vec[my Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { data . give ; }, as_ty: leased [source] Vec[my Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: leased [source] Vec[leased [source] Data], b: leased [source] Vec[my Data], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: leased [source] Vec[leased [source] Data], chain_b: Chain { liens: [] }, b: leased [source] Vec[my Data], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #4 (src/file.rs:LL:CC) because
                               judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [Leased(source)] }, ty: NamedTy(Vec[leased [source] Data]) }, ty_chains_b: {TyChain { chain: Chain { liens: [Leased(source)] }, ty: NamedTy(Vec[my Data]) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [Leased(source)] }, ty: NamedTy(Vec[leased [source] Data]) }, ty_chain_b: TyChain { chain: Chain { liens: [Leased(source)] }, ty: NamedTy(Vec[my Data]) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #7 (src/file.rs:LL:CC) because
                                       judgment `sub_generic_parameter { variances: [], a: leased [source] Data, b: my Data, liens_a: Chain { liens: [Leased(source)] }, liens_b: Chain { liens: [Leased(source)] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "covariant-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `perms_b.is_copy(&env)`
                                             perms_b = Chain { liens: [Leased(source)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 }
                                         the rule "covariant-owned" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `perms_b.is_owned(&env)`
                                             perms_b = Chain { liens: [Leased(source)] }
                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 }
                                         the rule "invariant" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `sub { a: leased [source] Data, b: my Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: leased [source] Data, chain_b: Chain { liens: [] }, b: my Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub" failed at step #4 (src/file.rs:LL:CC) because
                                                   judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [Leased(source)] }, ty: NamedTy(Data) }, ty_chains_b: {TyChain { chain: Chain { liens: [] }, ty: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [Leased(source)] }, ty: NamedTy(Data) }, ty_chain_b: TyChain { chain: Chain { liens: [] }, ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                                           judgment `sub_chains { chain_a: Chain { liens: [Leased(source)] }, chain_b: Chain { liens: [] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "leased-dead" failed at step #2 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_lent { a: my Vec[my Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is-lent" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: lent(my Vec[my Data]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                       condition evaluted to false: `is_true`
                                                             the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                               condition evaluted to false: `chain_a.is_owned(&env)`
                                                                 chain_a = Chain { liens: [Leased(source)] }
                                                                 &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 }
                                                             the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                               condition evaluted to false: `chain_a.is_owned(&env)`
                                                                 chain_a = Chain { liens: [Leased(source)] }
                                                                 &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 }
                                                             the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                               condition evaluted to false: `chain_a.is_owned(&env)`
                                                                 chain_a = Chain { liens: [Leased(source)] }
                                                                 &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn leased_vec_leased_Data_to_leased_vec_leased_Data() {
    check_program(&term(
        "
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(my self, source: my Vec[my Data], data: leased[source] Vec[leased[source] Data]) -> leased[source] Vec[leased[source] Data] {
                data.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn forall_P_vec_my_Data_to_P_vec_P_Data() {
    check_program(&term(
        "
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test[perm P](my self, source: my Vec[my Data], data: P Vec[Data]) -> P Vec[P Data] {
                data.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Vec [ty] { } class Data { } class Main { fn test [perm] (my self source : my Vec[my Data], data : ^perm0_0 Vec[Data]) -> ^perm0_0 Vec[^perm0_0 Data] { data . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { data . give ; }, as_ty: !perm_0 Vec[!perm_0 Data], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { data . give ; }, as_ty: !perm_0 Vec[!perm_0 Data], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: !perm_0 Vec[Data], b: !perm_0 Vec[!perm_0 Data], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: !perm_0 Vec[Data], chain_b: Chain { liens: [] }, b: !perm_0 Vec[!perm_0 Data], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #4 (src/file.rs:LL:CC) because
                               judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [Variable(!perm_0)] }, ty: NamedTy(Vec[Data]) }, ty_chains_b: {TyChain { chain: Chain { liens: [Variable(!perm_0)] }, ty: NamedTy(Vec[!perm_0 Data]) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [Variable(!perm_0)] }, ty: NamedTy(Vec[Data]) }, ty_chain_b: TyChain { chain: Chain { liens: [Variable(!perm_0)] }, ty: NamedTy(Vec[!perm_0 Data]) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #7 (src/file.rs:LL:CC) because
                                       judgment `sub_generic_parameter { variances: [], a: Data, b: !perm_0 Data, liens_a: Chain { liens: [Variable(!perm_0)] }, liens_b: Chain { liens: [Variable(!perm_0)] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "covariant-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `perms_b.is_copy(&env)`
                                             perms_b = Chain { liens: [Variable(!perm_0)] }
                                             &env = Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }
                                         the rule "covariant-owned" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `perms_b.is_owned(&env)`
                                             perms_b = Chain { liens: [Variable(!perm_0)] }
                                             &env = Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }
                                         the rule "invariant" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `sub { a: Data, b: !perm_0 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: Data, chain_b: Chain { liens: [] }, b: !perm_0 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub" failed at step #4 (src/file.rs:LL:CC) because
                                                   judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [] }, ty: NamedTy(Data) }, ty_chains_b: {TyChain { chain: Chain { liens: [Variable(!perm_0)] }, ty: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [] }, ty: NamedTy(Data) }, ty_chain_b: TyChain { chain: Chain { liens: [Variable(!perm_0)] }, ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                                           judgment `sub_chains { chain_a: Chain { liens: [] }, chain_b: Chain { liens: [Variable(!perm_0)] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "my-sub-copy" failed at step #2 (src/file.rs:LL:CC) because
                                                               condition evaluted to false: `chain_b.is_copy(&env)`
                                                                 chain_b = Chain { liens: [Variable(!perm_0)] }
                                                                 &env = Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }
                                                             the rule "my-sub-owned" failed at step #2 (src/file.rs:LL:CC) because
                                                               condition evaluted to false: `chain_b.is_owned(&env)`
                                                                 chain_b = Chain { liens: [Variable(!perm_0)] }
                                                                 &env = Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }
                                                             the rule "our-sub-copy" failed at step #1 (src/file.rs:LL:CC) because
                                                               condition evaluted to false: `chain_a.is_copy(&env)`
                                                                 chain_a = Chain { liens: [] }
                                                                 &env = Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_shared_P_P_vec_my_Data_to_P_vec_P_Data() {
    check_program(&term(
        "
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test[perm P](my self, source: my Vec[my Data], data: P Vec[Data]) -> P Vec[P Data]
            where
                copy(P),
            {
                data.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn our_vec_my_Data_to_our_vec_our_Data() {
    check_program(&term(
        "
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(my self, source: my Vec[my Data], data: our Vec[Data]) -> our Vec[our Data]
            {
                data.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn our_vec_our_Data_to_our_vec_my_Data() {
    check_program(&term(
        "
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(my self, source: my Vec[my Data], data: our Vec[our Data]) -> our Vec[my Data]
            {
                data.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn our_vec_shared_Data_to_shared_vec_my_Data() {
    check_program(&term(
        "
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(my self, source: my Vec[my Data], data: my Vec[shared[source] Data]) -> shared[source] Vec[my Data]
            {
                data.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn ordering_matters() {
    check_program(&term(
        "
        class Data { }
        class Pair[ty D] {
          first: D;
          second: D;
        }
        class Main {
            fn test[perm P, perm Q](my self, pair: P Pair[Q Data]) -> Q P Data {
                pair.first.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair [ty] { first : ^ty0_0 ; second : ^ty0_0 ; } class Main { fn test [perm, perm] (my self pair : ^perm0_0 Pair[^perm0_1 Data]) -> ^perm0_1 ^perm0_0 Data { pair . first . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { pair . first . give ; }, as_ty: !perm_1 !perm_0 Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, pair: !perm_0 Pair[!perm_1 Data]}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { pair . first . give ; }, as_ty: !perm_1 !perm_0 Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, pair: !perm_0 Pair[!perm_1 Data]}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: !perm_0 !perm_1 Data, b: !perm_1 !perm_0 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, pair: !perm_0 Pair[!perm_1 Data]}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: !perm_0 !perm_1 Data, chain_b: Chain { liens: [] }, b: !perm_1 !perm_0 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, pair: !perm_0 Pair[!perm_1 Data]}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #4 (src/file.rs:LL:CC) because
                               judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [Variable(!perm_0), Variable(!perm_1)] }, ty: NamedTy(Data) }, ty_chains_b: {TyChain { chain: Chain { liens: [Variable(!perm_1), Variable(!perm_0)] }, ty: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, pair: !perm_0 Pair[!perm_1 Data]}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [Variable(!perm_0), Variable(!perm_1)] }, ty: NamedTy(Data) }, ty_chain_b: TyChain { chain: Chain { liens: [Variable(!perm_1), Variable(!perm_0)] }, ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, pair: !perm_0 Pair[!perm_1 Data]}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_chains { chain_a: Chain { liens: [Variable(!perm_0), Variable(!perm_1)] }, chain_b: Chain { liens: [Variable(!perm_1), Variable(!perm_0)] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, pair: !perm_0 Pair[!perm_1 Data]}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Variable(!perm_0), Variable(!perm_1)] }
                                             &env = Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, pair: !perm_0 Pair[!perm_1 Data]}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }
                                         the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Variable(!perm_0), Variable(!perm_1)] }
                                             &env = Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, pair: !perm_0 Pair[!perm_1 Data]}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }
                                         the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                             chain_a = Chain { liens: [Variable(!perm_0), Variable(!perm_1)] }
                                             &env = Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, pair: !perm_0 Pair[!perm_1 Data]}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }"#]]);
}
