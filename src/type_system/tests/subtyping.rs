use crate::{dada_lang::term, type_system::check_program};
use formality_core::{test, test_util::ResultTestExt};

/// Return "given" from `d1` and give from `d1`.
/// It is indistinguishable as both of them are `our` Data, so the result is `our`.
#[test]
fn give_from_our_d1_to_our() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test(my self, d1: our Data, d2: our Data) -> given{d1} Data {
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
fn give_from_our_d2_to_our() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test(my self, d1: our Data, d2: our Data) -> given{d2} Data {
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
            fn test(my self, d1: our Data, d2: our Data) -> given{d2} Data {
                let d = new Data();
                d.share;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test (my self d1 : our Data, d2 : our Data) -> given {d2} Data { let d = new Data () ; d . share ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d = new Data () ; d . share ; }, as_ty: given {d2} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d = new Data () ; d . share ; }, as_ty: given {d2} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: shared {d} Data, b: given {d2} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_in_cx { chain_a: my, a: shared {d} Data, chain_b: my, b: given {d2} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_ty_chain_sets { ty_liens_a: {NamedTy(shared{d}, Data)}, ty_liens_b: {NamedTy(our, Data)}, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chains { ty_chain_a: NamedTy(shared{d}, Data), ty_chain_b: NamedTy(our, Data), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                     the rule "named ty" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment had no applicable rules: `sub_lien_chains { a: shared{d}, b: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }`"#]]);
}

#[test]
fn provide_shared_from_d1_expect_shared_from_d1() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test(my self, d1: my Data, d2: my Data) -> shared{d1} Data {
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
            fn test(my self, d1: my Data, d2: my Data) -> shared{d1} Data {
                d2.share;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test (my self d1 : my Data, d2 : my Data) -> shared {d1} Data { d2 . share ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { d2 . share ; }, as_ty: shared {d1} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d2 . share ; }, as_ty: shared {d1} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: shared {d2} my Data, b: shared {d1} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_in_cx { chain_a: my, a: shared {d2} my Data, chain_b: my, b: shared {d1} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_ty_chain_sets { ty_liens_a: {NamedTy(shared{d2}, Data)}, ty_liens_b: {NamedTy(shared{d1}, Data)}, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chains { ty_chain_a: NamedTy(shared{d2}, Data), ty_chain_b: NamedTy(shared{d1}, Data), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                     the rule "named ty" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_lien_chains { a: shared{d2}, b: shared{d1}, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                         the rule "sh-sh" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `place_covered_by_place(&a, &b)`
                                             &a = d2
                                             &b = d1"#]]);
}

#[test]
fn provide_shared_from_d2_expect_shared_from_d1_or_d2() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test(my self, d1: my Data, d2: my Data) -> shared{d1, d2} Data {
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
            fn test(my self, d1: my Data, d2: my Data) -> shared{d1} Data {
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
            fn test(my self, d1: my Data, d2: my Data) -> shared{d2} Data {
                d1.next.share;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { next : my Data ; } class Main { fn test (my self d1 : my Data, d2 : my Data) -> shared {d2} Data { d1 . next . share ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { d1 . next . share ; }, as_ty: shared {d2} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . next . share ; }, as_ty: shared {d2} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: shared {d1 . next} my my Data, b: shared {d2} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_in_cx { chain_a: my, a: shared {d1 . next} my my Data, chain_b: my, b: shared {d2} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_ty_chain_sets { ty_liens_a: {NamedTy(shared{d1 . next}, Data)}, ty_liens_b: {NamedTy(shared{d2}, Data)}, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chains { ty_chain_a: NamedTy(shared{d1 . next}, Data), ty_chain_b: NamedTy(shared{d2}, Data), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                     the rule "named ty" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_lien_chains { a: shared{d1 . next}, b: shared{d2}, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                         the rule "sh-sh" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `place_covered_by_place(&a, &b)`
                                             &a = d1 . next
                                             &b = d2"#]]);
}

#[test]
fn provide_shared_from_d1_expect_shared_from_d1_next() {
    check_program(&term(
        "
        class Data {
            next: my Data;
        }

        class Main {
            fn test(my self, d1: my Data, d2: my Data) -> shared{d1.next} Data {
                d1.share;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { next : my Data ; } class Main { fn test (my self d1 : my Data, d2 : my Data) -> shared {d1 . next} Data { d1 . share ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { d1 . share ; }, as_ty: shared {d1 . next} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . share ; }, as_ty: shared {d1 . next} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: shared {d1} my Data, b: shared {d1 . next} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_in_cx { chain_a: my, a: shared {d1} my Data, chain_b: my, b: shared {d1 . next} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_ty_chain_sets { ty_liens_a: {NamedTy(shared{d1}, Data)}, ty_liens_b: {NamedTy(shared{d1 . next}, Data)}, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chains { ty_chain_a: NamedTy(shared{d1}, Data), ty_chain_b: NamedTy(shared{d1 . next}, Data), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                     the rule "named ty" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_lien_chains { a: shared{d1}, b: shared{d1 . next}, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                         the rule "sh-sh" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `place_covered_by_place(&a, &b)`
                                             &a = d1
                                             &b = d1 . next"#]]);
}

#[test]
fn provide_leased_from_d1_next_expect_shared_from_d1() {
    check_program(&term(
        "
        class Data {
            next: my Data;
        }

        class Main {
            fn test(my self, d1: my Data, d2: my Data) -> shared{d1} Data {
                d1.next.lease;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { next : my Data ; } class Main { fn test (my self d1 : my Data, d2 : my Data) -> shared {d1} Data { d1 . next . lease ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { d1 . next . lease ; }, as_ty: shared {d1} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . next . lease ; }, as_ty: shared {d1} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: leased {d1 . next} my my Data, b: shared {d1} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_in_cx { chain_a: my, a: leased {d1 . next} my my Data, chain_b: my, b: shared {d1} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_ty_chain_sets { ty_liens_a: {NamedTy(leased{d1 . next}, Data)}, ty_liens_b: {NamedTy(shared{d1}, Data)}, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chains { ty_chain_a: NamedTy(leased{d1 . next}, Data), ty_chain_b: NamedTy(shared{d1}, Data), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                     the rule "named ty" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment had no applicable rules: `sub_lien_chains { a: leased{d1 . next}, b: shared{d1}, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn shared_from_P_d1_to_given_from_P_d1() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self, d1: P Data, d2: our Data) -> given{d1} Data {
                d1.share;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm] (my self d1 : ^perm0_0 Data, d2 : our Data) -> given {d1} Data { d1 . share ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { d1 . share ; }, as_ty: given {d1} Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . share ; }, as_ty: given {d1} Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: shared {d1} !perm_0 Data, b: given {d1} Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_in_cx { chain_a: my, a: shared {d1} !perm_0 Data, chain_b: my, b: given {d1} Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_ty_chain_sets { ty_liens_a: {NamedTy(shared{d1} !perm_0, Data)}, ty_liens_b: {NamedTy(!perm_0, Data)}, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chains { ty_chain_a: NamedTy(shared{d1} !perm_0, Data), ty_chain_b: NamedTy(!perm_0, Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                     the rule "named ty" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment had no applicable rules: `sub_lien_chains { a: shared{d1} !perm_0, b: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn given_from_P_d1_to_given_from_P_d1() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P](my self, d1: P Data, d2: our Data) -> given{d1} Data {
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
            fn test[perm P, perm Q](my self, d1: P Data, d2: P Data) -> given{d2} Data {
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
            fn test[perm P, perm Q](my self, d1: P Data, d2: Q Data) -> given{d2} Data {
                d1.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm, perm] (my self d1 : ^perm0_0 Data, d2 : ^perm0_1 Data) -> given {d2} Data { d1 . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { d1 . give ; }, as_ty: given {d2} Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . give ; }, as_ty: given {d2} Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: !perm_0 Data, b: given {d2} Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {d1} } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_in_cx { chain_a: my, a: !perm_0 Data, chain_b: my, b: given {d2} Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {d1} } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_ty_chain_sets { ty_liens_a: {NamedTy(!perm_0, Data)}, ty_liens_b: {NamedTy(!perm_1, Data)}, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {d1} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chains { ty_chain_a: NamedTy(!perm_0, Data), ty_chain_b: NamedTy(!perm_1, Data), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {d1} } }` failed at the following rule(s):
                                     the rule "named ty" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment had no applicable rules: `sub_lien_chains { a: !perm_0, b: !perm_1, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {d1} } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn shared_from_P_d1_to_shared_from_P_d1() {
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P, perm Q](my self, d1: P Data, d2: P Data) -> shared{d1} Data {
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
    // Interesting example: we declare `shared{d2}` but return `shared{d1}`.
    // Even though both of them have permission `P`, we give an error.
    // The distinction of which `P` we shared from is important: we are not going to be incrementing
    // the ref count, so if `d1` were dropped, which the type signature suggests would be ok,
    // then the data would be freed.
    check_program(&term(
        "
        class Data { }
        class Main {
            fn test[perm P, perm Q](my self, d1: P Data, d2: P Data) -> shared{d2} Data {
                d1.share;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Main { fn test [perm, perm] (my self d1 : ^perm0_0 Data, d2 : ^perm0_0 Data) -> shared {d2} Data { d1 . share ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { d1 . share ; }, as_ty: shared {d2} Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . share ; }, as_ty: shared {d2} Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: shared {d1} !perm_0 Data, b: shared {d2} Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_in_cx { chain_a: my, a: shared {d1} !perm_0 Data, chain_b: my, b: shared {d2} Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_ty_chain_sets { ty_liens_a: {NamedTy(shared{d1} !perm_0, Data)}, ty_liens_b: {NamedTy(shared{d2} !perm_0, Data)}, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chains { ty_chain_a: NamedTy(shared{d1} !perm_0, Data), ty_chain_b: NamedTy(shared{d2} !perm_0, Data), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                     the rule "named ty" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `sub_lien_chains { a: shared{d1} !perm_0, b: shared{d2} !perm_0, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                         the rule "sh-sh" failed at step #0 (src/file.rs:LL:CC) because
                                           condition evaluted to false: `place_covered_by_place(&a, &b)`
                                             &a = d1
                                             &b = d2"#]]);
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
            fn test(my self, pair: Pair, data: our leased{pair} Data) -> our Data {
                data.give;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Pair { d1 : Data ; d2 : Data ; } class Data { } class Main { fn test (my self pair : Pair, data : our leased {pair} Data) -> our Data { data . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { data . give ; }, as_ty: our Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { data . give ; }, as_ty: our Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: our leased {pair} Data, b: our Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {data} } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_in_cx { chain_a: my, a: our leased {pair} Data, chain_b: my, b: our Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {data} } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_ty_chain_sets { ty_liens_a: {NamedTy(our leased{pair}, Data)}, ty_liens_b: {NamedTy(our, Data)}, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {data} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chains { ty_chain_a: NamedTy(our leased{pair}, Data), ty_chain_b: NamedTy(our, Data), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {data} } }` failed at the following rule(s):
                                     the rule "named ty" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment had no applicable rules: `sub_lien_chains { a: our leased{pair}, b: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {data} } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
#[ignore = "FIXME our leased"]
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
            fn test(my self, pair: Pair, data: our leased{pair} Data) -> our leased{pair} Data {
                data.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect![[r#"
        check program `class Pair { d1 : Data ; d2 : Data ; } class Data { } class Main { fn test (my self pair : Pair, data : our leased {pair} Data) -> our Data { data . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { data . give ; }, as_ty: our Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { data . give ; }, as_ty: our Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: our leased {pair} Data, b: our Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {data} } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_in_cx { chain_a: my, a: our leased {pair} Data, chain_b: my, b: our Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {data} } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_ty_chain_sets { ty_liens_a: {NamedTy(our leased{pair}, Data)}, ty_liens_b: {NamedTy(our, Data)}, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {data} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chains { ty_chain_a: NamedTy(our leased{pair}, Data), ty_chain_b: NamedTy(our, Data), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {data} } }` failed at the following rule(s):
                                     the rule "named ty" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment had no applicable rules: `sub_lien_chains { a: our leased{pair}, b: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {data} } }`
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: our leased {pair} Data, b: our Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_in_cx { chain_a: my, a: our leased {pair} Data, chain_b: my, b: our Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_ty_chain_sets { ty_liens_a: {NamedTy(our leased{pair}, Data)}, ty_liens_b: {NamedTy(our, Data)}, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chains { ty_chain_a: NamedTy(our leased{pair}, Data), ty_chain_b: NamedTy(our, Data), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                     the rule "named ty" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment had no applicable rules: `sub_lien_chains { a: our leased{pair}, b: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
#[ignore = "FIXME our leased"]
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
            fn test(my self, pair: Pair, data: our leased{pair.d1} Data) -> our leased{pair} Data {
                data.give;
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect![[r#"
        check program `class Pair { d1 : Data ; d2 : Data ; } class Data { } class Main { fn test (my self pair : Pair, data : our leased {pair} Data) -> our Data { data . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { data . give ; }, as_ty: our Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { data . give ; }, as_ty: our Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: our leased {pair} Data, b: our Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {data} } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_in_cx { chain_a: my, a: our leased {pair} Data, chain_b: my, b: our Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {data} } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_ty_chain_sets { ty_liens_a: {NamedTy(our leased{pair}, Data)}, ty_liens_b: {NamedTy(our, Data)}, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {data} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chains { ty_chain_a: NamedTy(our leased{pair}, Data), ty_chain_b: NamedTy(our, Data), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {data} } }` failed at the following rule(s):
                                     the rule "named ty" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment had no applicable rules: `sub_lien_chains { a: our leased{pair}, b: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {data} } }`
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: our leased {pair} Data, b: our Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_in_cx { chain_a: my, a: our leased {pair} Data, chain_b: my, b: our Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_ty_chain_sets { ty_liens_a: {NamedTy(our leased{pair}, Data)}, ty_liens_b: {NamedTy(our, Data)}, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chains { ty_chain_a: NamedTy(our leased{pair}, Data), ty_chain_b: NamedTy(our, Data), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                     the rule "named ty" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment had no applicable rules: `sub_lien_chains { a: our leased{pair}, b: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: our leased {pair} Data, pair: Pair}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }`"#]]);
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
            fn test(my self, source: my Vec[my Data], data: shared{source} Vec[my Data]) -> shared{source} Vec[my Data] {
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
            fn test(my self, source: my Vec[my Data], data: shared{source} Vec[my Data]) -> shared{source} Vec[shared{source} Data] {
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
            fn test(my self, source: my Vec[my Data], data: leased{source} Vec[my Data]) -> leased{source} Vec[my Data] {
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
            fn test(my self, source: my Vec[my Data], data: leased{source} Vec[my Data]) -> leased{source} Vec[leased{source} Data] {
                data.give;
            }
        }
        ",
    ))
    // ERROR is correct, but the reason seems kinda bogus
    .assert_err(expect_test::expect![[r#"
        check program `class Vec [ty] { } class Data { } class Main { fn test (my self source : my Vec[my Data], data : leased {source} Vec[my Data]) -> leased {source} Vec[leased {source} Data] { data . give ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { data . give ; }, as_ty: leased {source} Vec[leased {source} Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased {source} Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { data . give ; }, as_ty: leased {source} Vec[leased {source} Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased {source} Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: leased {source} Vec[my Data], b: leased {source} Vec[leased {source} Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased {source} Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {data} } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_in_cx { chain_a: my, a: leased {source} Vec[my Data], chain_b: my, b: leased {source} Vec[leased {source} Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased {source} Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {data} } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_ty_chain_sets { ty_liens_a: {NamedTy(leased{source}, Vec[my Data])}, ty_liens_b: {NamedTy(leased{source}, Vec[leased {source} Data])}, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased {source} Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {data} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `sub_ty_chains { ty_chain_a: NamedTy(leased{source}, Vec[my Data]), ty_chain_b: NamedTy(leased{source}, Vec[leased {source} Data]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased {source} Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {data} } }` failed at the following rule(s):
                                     the rule "named ty" failed at step #4 (src/file.rs:LL:CC) because
                                       judgment `sub_in_cx { chain_a: leased{source}, a: my Data, chain_b: leased{source}, b: leased {source} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased {source} Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {data} } }` failed at the following rule(s):
                                         the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `sub_ty_chain_sets { ty_liens_a: {NamedTy(leased{source}, Data)}, ty_liens_b: {NamedTy(leased{source} leased{source}, Data)}, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased {source} Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {data} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `sub_ty_chains { ty_chain_a: NamedTy(leased{source}, Data), ty_chain_b: NamedTy(leased{source} leased{source}, Data), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased {source} Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {data} } }` failed at the following rule(s):
                                                 the rule "named ty" failed at step #3 (src/file.rs:LL:CC) because
                                                   judgment `sub_lien_chains { a: leased{source}, b: leased{source} leased{source}, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased {source} Vec[my Data], source: my Vec[my Data]}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {data} } }` failed at the following rule(s):
                                                     the rule "l-l" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment had no applicable rules: `lien_chain_strictly_covered_by { a: my, b: leased{source} }`"#]]);
}
