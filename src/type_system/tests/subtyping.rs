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
                           judgment `sub_under { cx_a: {}, a: our Data, cx_b: {}, b: !perm_0 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_some { lien_data_a: LienData { liens: {Copy}, data: NamedTy(Data) }, lien_datas_b: {LienData { liens: {Var(!perm_0)}, data: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_lien_data { lien_data_a: LienData { liens: {Copy}, data: NamedTy(Data) }, lien_data_b: LienData { liens: {Var(!perm_0)}, data: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_lien_sets { liens_a: {Copy}, liens_b: {Var(!perm_0)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `sub_some_lien { lien_a: Copy, liens_b: {Var(!perm_0)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `sub_lien { lien_a: Copy, lien_b: Var(!perm_0), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "Copy-vs-CopyVar" failed at step #0 (src/file.rs:LL:CC) because
                                                   condition evaluted to false: `env.is(&v, IsCopy)`
                                                     env = Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }
                                                     &v = !perm_0
                                                     IsCopy = IsCopy"#]]);
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
              leased(P),
            {
                let d: our Data = new Data();
                d.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self) -> ^perm0_0 Data where leased(^perm0_0) { let d : our Data = new Data () ; d . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d : our Data = new Data () ; d . give ; }, as_ty: !perm_0 Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {leased(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d : our Data = new Data () ; d . give ; }, as_ty: !perm_0 Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main}, assumptions: {leased(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: our Data, b: !perm_0 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {leased(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under { cx_a: {}, a: our Data, cx_b: {}, b: !perm_0 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {leased(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_some { lien_data_a: LienData { liens: {Copy}, data: NamedTy(Data) }, lien_datas_b: {LienData { liens: {Var(!perm_0)}, data: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {leased(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_lien_data { lien_data_a: LienData { liens: {Copy}, data: NamedTy(Data) }, lien_data_b: LienData { liens: {Var(!perm_0)}, data: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {leased(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_lien_sets { liens_a: {Copy}, liens_b: {Var(!perm_0)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {leased(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `sub_some_lien { lien_a: Copy, liens_b: {Var(!perm_0)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {leased(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `sub_lien { lien_a: Copy, lien_b: Var(!perm_0), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {leased(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "Copy-vs-CopyVar" failed at step #0 (src/file.rs:LL:CC) because
                                                   condition evaluted to false: `env.is(&v, IsCopy)`
                                                     env = Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d: our Data}, assumptions: {leased(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }
                                                     &v = !perm_0
                                                     IsCopy = IsCopy"#]]);
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
                           judgment `sub_under { cx_a: {}, a: shared [d] Data, cx_b: {}, b: given [d2] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_some { lien_data_a: LienData { liens: {Copy, Lent, Shared(d)}, data: NamedTy(Data) }, lien_datas_b: {LienData { liens: {Copy}, data: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_lien_data { lien_data_a: LienData { liens: {Copy, Lent, Shared(d)}, data: NamedTy(Data) }, lien_data_b: LienData { liens: {Copy}, data: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_lien_sets { liens_a: {Copy, Lent, Shared(d)}, liens_b: {Copy}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `"flat_map"` failed at the following rule(s):
                                             failed at (src/file.rs:LL:CC) because
                                               judgment `sub_some_lien { lien_a: Lent, liens_b: {Copy}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment had no applicable rules: `sub_lien { lien_a: Lent, lien_b: Copy, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 } }`"#]]);
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
                       judgment `sub { a: shared [d2] my Data, b: shared [d1] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under { cx_a: {}, a: shared [d2] my Data, cx_b: {}, b: shared [d1] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_some { lien_data_a: LienData { liens: {Copy, Lent, Shared(d2)}, data: NamedTy(Data) }, lien_datas_b: {LienData { liens: {Copy, Lent, Shared(d1)}, data: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_lien_data { lien_data_a: LienData { liens: {Copy, Lent, Shared(d2)}, data: NamedTy(Data) }, lien_data_b: LienData { liens: {Copy, Lent, Shared(d1)}, data: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_lien_sets { liens_a: {Copy, Lent, Shared(d2)}, liens_b: {Copy, Lent, Shared(d1)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `"flat_map"` failed at the following rule(s):
                                             failed at (src/file.rs:LL:CC) because
                                               judgment `"flat_map"` failed at the following rule(s):
                                                 failed at (src/file.rs:LL:CC) because
                                                   judgment `sub_some_lien { lien_a: Shared(d2), liens_b: {Copy, Lent, Shared(d1)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "dead" failed at step #3 (src/file.rs:LL:CC) because
                                                       condition evaluted to false: `liens_place.is_lent(&env)`
                                                         liens_place = {}
                                                         &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }"#]]);
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
                       judgment `sub { a: shared [d1 . next] my my Data, b: shared [d2] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under { cx_a: {}, a: shared [d1 . next] my my Data, cx_b: {}, b: shared [d2] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_some { lien_data_a: LienData { liens: {Copy, Lent, Shared(d1 . next)}, data: NamedTy(Data) }, lien_datas_b: {LienData { liens: {Copy, Lent, Shared(d2)}, data: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_lien_data { lien_data_a: LienData { liens: {Copy, Lent, Shared(d1 . next)}, data: NamedTy(Data) }, lien_data_b: LienData { liens: {Copy, Lent, Shared(d2)}, data: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_lien_sets { liens_a: {Copy, Lent, Shared(d1 . next)}, liens_b: {Copy, Lent, Shared(d2)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `"flat_map"` failed at the following rule(s):
                                             failed at (src/file.rs:LL:CC) because
                                               judgment `"flat_map"` failed at the following rule(s):
                                                 failed at (src/file.rs:LL:CC) because
                                                   judgment `sub_some_lien { lien_a: Shared(d1 . next), liens_b: {Copy, Lent, Shared(d2)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "dead" failed at step #3 (src/file.rs:LL:CC) because
                                                       condition evaluted to false: `liens_place.is_lent(&env)`
                                                         liens_place = {}
                                                         &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }"#]]);
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
                       judgment `sub { a: shared [d1] my Data, b: shared [d1 . next] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under { cx_a: {}, a: shared [d1] my Data, cx_b: {}, b: shared [d1 . next] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_some { lien_data_a: LienData { liens: {Copy, Lent, Shared(d1)}, data: NamedTy(Data) }, lien_datas_b: {LienData { liens: {Copy, Lent, Shared(d1 . next)}, data: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_lien_data { lien_data_a: LienData { liens: {Copy, Lent, Shared(d1)}, data: NamedTy(Data) }, lien_data_b: LienData { liens: {Copy, Lent, Shared(d1 . next)}, data: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_lien_sets { liens_a: {Copy, Lent, Shared(d1)}, liens_b: {Copy, Lent, Shared(d1 . next)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `"flat_map"` failed at the following rule(s):
                                             failed at (src/file.rs:LL:CC) because
                                               judgment `"flat_map"` failed at the following rule(s):
                                                 failed at (src/file.rs:LL:CC) because
                                                   judgment `sub_some_lien { lien_a: Shared(d1), liens_b: {Copy, Lent, Shared(d1 . next)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "dead" failed at step #3 (src/file.rs:LL:CC) because
                                                       condition evaluted to false: `liens_place.is_lent(&env)`
                                                         liens_place = {}
                                                         &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }"#]]);
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
                       judgment `sub { a: leased [d1 . next] my my Data, b: shared [d1] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under { cx_a: {}, a: leased [d1 . next] my my Data, cx_b: {}, b: shared [d1] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_some { lien_data_a: LienData { liens: {Lent, Leased(d1 . next)}, data: NamedTy(Data) }, lien_datas_b: {LienData { liens: {Copy, Lent, Shared(d1)}, data: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_lien_data { lien_data_a: LienData { liens: {Lent, Leased(d1 . next)}, data: NamedTy(Data) }, lien_data_b: LienData { liens: {Copy, Lent, Shared(d1)}, data: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_lien_sets { liens_a: {Lent, Leased(d1 . next)}, liens_b: {Copy, Lent, Shared(d1)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `"flat_map"` failed at the following rule(s):
                                             failed at (src/file.rs:LL:CC) because
                                               judgment `sub_some_lien { lien_a: Leased(d1 . next), liens_b: {Copy, Lent, Shared(d1)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "dead" failed at step #3 (src/file.rs:LL:CC) because
                                                   condition evaluted to false: `liens_place.is_lent(&env)`
                                                     liens_place = {}
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
                       judgment `sub { a: shared [d1] !perm_0 Data, b: given [d1] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under { cx_a: {}, a: shared [d1] !perm_0 Data, cx_b: {}, b: given [d1] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_some { lien_data_a: LienData { liens: {Copy, Lent, Shared(d1), Var(!perm_0)}, data: NamedTy(Data) }, lien_datas_b: {LienData { liens: {Var(!perm_0)}, data: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_lien_data { lien_data_a: LienData { liens: {Copy, Lent, Shared(d1), Var(!perm_0)}, data: NamedTy(Data) }, lien_data_b: LienData { liens: {Var(!perm_0)}, data: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_lien_sets { liens_a: {Copy, Lent, Shared(d1), Var(!perm_0)}, liens_b: {Var(!perm_0)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `sub_some_lien { lien_a: Copy, liens_b: {Var(!perm_0)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `sub_lien { lien_a: Copy, lien_b: Var(!perm_0), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "Copy-vs-CopyVar" failed at step #0 (src/file.rs:LL:CC) because
                                                   condition evaluted to false: `env.is(&v, IsCopy)`
                                                     env = Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }
                                                     &v = !perm_0
                                                     IsCopy = IsCopy"#]]);
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
                           judgment `sub_under { cx_a: {}, a: !perm_0 Data, cx_b: {}, b: given [d2] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_some { lien_data_a: LienData { liens: {Var(!perm_0)}, data: NamedTy(Data) }, lien_datas_b: {LienData { liens: {Var(!perm_1)}, data: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_lien_data { lien_data_a: LienData { liens: {Var(!perm_0)}, data: NamedTy(Data) }, lien_data_b: LienData { liens: {Var(!perm_1)}, data: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_lien_sets { liens_a: {Var(!perm_0)}, liens_b: {Var(!perm_1)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `sub_some_lien { lien_a: Var(!perm_0), liens_b: {Var(!perm_1)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `sub_lien { lien_a: Var(!perm_0), lien_b: Var(!perm_1), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "OwnedVar-vs-CopyVar" failed at step #0 (src/file.rs:LL:CC) because
                                                   condition evaluted to false: `env.is(&a, IsOwned)`
                                                     env = Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }
                                                     &a = !perm_0
                                                     IsOwned = IsOwned"#]]);
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
                       judgment `sub { a: shared [d1] !perm_0 Data, b: shared [d2] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_under { cx_a: {}, a: shared [d1] !perm_0 Data, cx_b: {}, b: shared [d2] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_some { lien_data_a: LienData { liens: {Copy, Lent, Shared(d1), Var(!perm_0)}, data: NamedTy(Data) }, lien_datas_b: {LienData { liens: {Copy, Lent, Shared(d2), Var(!perm_0)}, data: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_lien_data { lien_data_a: LienData { liens: {Copy, Lent, Shared(d1), Var(!perm_0)}, data: NamedTy(Data) }, lien_data_b: LienData { liens: {Copy, Lent, Shared(d2), Var(!perm_0)}, data: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_lien_sets { liens_a: {Copy, Lent, Shared(d1), Var(!perm_0)}, liens_b: {Copy, Lent, Shared(d2), Var(!perm_0)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `"flat_map"` failed at the following rule(s):
                                             failed at (src/file.rs:LL:CC) because
                                               judgment `"flat_map"` failed at the following rule(s):
                                                 failed at (src/file.rs:LL:CC) because
                                                   judgment `sub_some_lien { lien_a: Shared(d1), liens_b: {Copy, Lent, Shared(d2), Var(!perm_0)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "dead" failed at step #3 (src/file.rs:LL:CC) because
                                                       condition evaluted to false: `liens_place.is_lent(&env)`
                                                         liens_place = {Var(!perm_0)}
                                                         &env = Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {relative(!perm_0), relative(!perm_1), atomic(!perm_0), atomic(!perm_1)}, fresh: 0 }"#]]);
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
                           judgment `sub_under { cx_a: {}, a: shared [pair1] leased [pair2] Data, cx_b: {}, b: shared [pair1] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: shared [pair1] leased [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_some { lien_data_a: LienData { liens: {Copy, Lent, Shared(pair1), Leased(pair2)}, data: NamedTy(Data) }, lien_datas_b: {LienData { liens: {Copy, Lent, Shared(pair1)}, data: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: shared [pair1] leased [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_lien_data { lien_data_a: LienData { liens: {Copy, Lent, Shared(pair1), Leased(pair2)}, data: NamedTy(Data) }, lien_data_b: LienData { liens: {Copy, Lent, Shared(pair1)}, data: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: shared [pair1] leased [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_lien_sets { liens_a: {Copy, Lent, Shared(pair1), Leased(pair2)}, liens_b: {Copy, Lent, Shared(pair1)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: shared [pair1] leased [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `"flat_map"` failed at the following rule(s):
                                             failed at (src/file.rs:LL:CC) because
                                               judgment `"flat_map"` failed at the following rule(s):
                                                 failed at (src/file.rs:LL:CC) because
                                                   judgment `"flat_map"` failed at the following rule(s):
                                                     failed at (src/file.rs:LL:CC) because
                                                       judgment `sub_some_lien { lien_a: Leased(pair2), liens_b: {Copy, Lent, Shared(pair1)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: shared [pair1] leased [pair2] Data, pair1: Pair, pair2: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "dead" failed at step #3 (src/file.rs:LL:CC) because
                                                           condition evaluted to false: `liens_place.is_lent(&env)`
                                                             liens_place = {}
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
                           judgment `sub_under { cx_a: {}, a: our leased [pair] Data, cx_b: {}, b: our Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_some { lien_data_a: LienData { liens: {Copy, Lent, Leased(pair)}, data: NamedTy(Data) }, lien_datas_b: {LienData { liens: {Copy}, data: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_lien_data { lien_data_a: LienData { liens: {Copy, Lent, Leased(pair)}, data: NamedTy(Data) }, lien_data_b: LienData { liens: {Copy}, data: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_lien_sets { liens_a: {Copy, Lent, Leased(pair)}, liens_b: {Copy}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `"flat_map"` failed at the following rule(s):
                                             failed at (src/file.rs:LL:CC) because
                                               judgment `sub_some_lien { lien_a: Lent, liens_b: {Copy}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment had no applicable rules: `sub_lien { lien_a: Lent, lien_b: Copy, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased [pair] Data, pair: Pair}, assumptions: {}, fresh: 0 } }`"#]]);
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
                           judgment `sub_under { cx_a: {}, a: leased [source] Vec[my Data], cx_b: {}, b: leased [source] Vec[leased [source] Data], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_some { lien_data_a: LienData { liens: {Lent, Leased(source)}, data: NamedTy(Vec[my Data]) }, lien_datas_b: {LienData { liens: {Lent, Leased(source)}, data: NamedTy(Vec[leased [source] Data]) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_lien_data { lien_data_a: LienData { liens: {Lent, Leased(source)}, data: NamedTy(Vec[my Data]) }, lien_data_b: LienData { liens: {Lent, Leased(source)}, data: NamedTy(Vec[leased [source] Data]) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #7 (src/file.rs:LL:CC) because
                                       judgment `sub_generic_parameter { variances: [], a: my Data, b: leased [source] Data, liens_a: {Lent, Leased(source)}, liens_b: {Lent, Leased(source)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "invariant" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `sub { a: my Data, b: leased [source] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `sub_under { cx_a: {}, a: my Data, cx_b: {}, b: leased [source] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `sub_some { lien_data_a: LienData { liens: {}, data: NamedTy(Data) }, lien_datas_b: {LienData { liens: {Lent, Leased(source)}, data: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `sub_lien_data { lien_data_a: LienData { liens: {}, data: NamedTy(Data) }, lien_data_b: LienData { liens: {Lent, Leased(source)}, data: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                                           judgment `sub_lien_sets { liens_a: {}, liens_b: {Lent, Leased(source)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `layout_compatible { liens_a: {}, liens_b: {Lent, Leased(source)}, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "by value" failed at step #1 (src/file.rs:LL:CC) because
                                                                   condition evaluted to false: `liens_b.is_copy(&env) || liens_b.is_owned(&env)`
                                                                 the rule "leased" failed at step #0 (src/file.rs:LL:CC) because
                                                                   condition evaluted to false: `liens_a.is_leased(&env)`
                                                                     liens_a = {}
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
                           judgment `sub_under { cx_a: {}, a: leased [source] Vec[leased [source] Data], cx_b: {}, b: leased [source] Vec[my Data], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_some { lien_data_a: LienData { liens: {Lent, Leased(source)}, data: NamedTy(Vec[leased [source] Data]) }, lien_datas_b: {LienData { liens: {Lent, Leased(source)}, data: NamedTy(Vec[my Data]) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_lien_data { lien_data_a: LienData { liens: {Lent, Leased(source)}, data: NamedTy(Vec[leased [source] Data]) }, lien_data_b: LienData { liens: {Lent, Leased(source)}, data: NamedTy(Vec[my Data]) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #7 (src/file.rs:LL:CC) because
                                       judgment `sub_generic_parameter { variances: [], a: leased [source] Data, b: my Data, liens_a: {Lent, Leased(source)}, liens_b: {Lent, Leased(source)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "invariant" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `sub { a: leased [source] Data, b: my Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `sub_under { cx_a: {}, a: leased [source] Data, cx_b: {}, b: my Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `sub_some { lien_data_a: LienData { liens: {Lent, Leased(source)}, data: NamedTy(Data) }, lien_datas_b: {LienData { liens: {}, data: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `sub_lien_data { lien_data_a: LienData { liens: {Lent, Leased(source)}, data: NamedTy(Data) }, lien_data_b: LienData { liens: {}, data: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                                           judgment `sub_lien_sets { liens_a: {Lent, Leased(source)}, liens_b: {}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `sub_some_lien { lien_a: Lent, liens_b: {}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [source] Vec[leased [source] Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                                                   expression evaluated to an empty collection: `&liens_b`"#]]);
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
                           judgment `sub_under { cx_a: {}, a: !perm_0 Vec[Data], cx_b: {}, b: !perm_0 Vec[!perm_0 Data], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_some { lien_data_a: LienData { liens: {Var(!perm_0)}, data: NamedTy(Vec[Data]) }, lien_datas_b: {LienData { liens: {Var(!perm_0)}, data: NamedTy(Vec[!perm_0 Data]) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_lien_data { lien_data_a: LienData { liens: {Var(!perm_0)}, data: NamedTy(Vec[Data]) }, lien_data_b: LienData { liens: {Var(!perm_0)}, data: NamedTy(Vec[!perm_0 Data]) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "sub-named" failed at step #7 (src/file.rs:LL:CC) because
                                       judgment `sub_generic_parameter { variances: [], a: Data, b: !perm_0 Data, liens_a: {Var(!perm_0)}, liens_b: {Var(!perm_0)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                         the rule "covariant-copy" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `lien_set_is_copy { liens: {Var(!perm_0)}, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "some" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `lien_is_copy { lien: Var(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "var is copy" failed at step #0 (src/file.rs:LL:CC) because
                                                   condition evaluted to false: `env.is(&var, IsCopy)`
                                                     env = Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }
                                                     &var = !perm_0
                                                     IsCopy = IsCopy
                                         the rule "covariant-owned" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `lien_set_is_owned { liens: {Var(!perm_0)}, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "some" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `lien_is_owned { lien: Var(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "var is move" failed at step #0 (src/file.rs:LL:CC) because
                                                   condition evaluted to false: `env.is(&var, IsOwned)`
                                                     env = Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }
                                                     &var = !perm_0
                                                     IsOwned = IsOwned
                                         the rule "invariant" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `sub { a: Data, b: !perm_0 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `sub_under { cx_a: {}, a: Data, cx_b: {}, b: !perm_0 Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `sub_some { lien_data_a: LienData { liens: {}, data: NamedTy(Data) }, lien_datas_b: {LienData { liens: {Var(!perm_0)}, data: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `sub_lien_data { lien_data_a: LienData { liens: {}, data: NamedTy(Data) }, lien_data_b: LienData { liens: {Var(!perm_0)}, data: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                                           judgment `sub_lien_sets { liens_a: {}, liens_b: {Var(!perm_0)}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `layout_compatible { liens_a: {}, liens_b: {Var(!perm_0)}, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Vec[Data], source: my Vec[my Data]}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "by value" failed at step #1 (src/file.rs:LL:CC) because
                                                                   condition evaluted to false: `liens_b.is_copy(&env) || liens_b.is_owned(&env)`
                                                                 the rule "leased" failed at step #0 (src/file.rs:LL:CC) because
                                                                   condition evaluted to false: `liens_a.is_leased(&env)`
                                                                     liens_a = {}
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
