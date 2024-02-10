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
            3: judgment `can_type_expr_as { expr: { let d = new Data () ; d . share ; }, as_ty: given {d2} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let d = new Data () ; d . share ; }, as_ty: given {d2} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: shared {d} Data, b: given {d2} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_in { terms_a: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, a: shared {d} Data, terms_b: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, b: given {d2} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_terms { terms_a: Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {(Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {}, shared_places: {d}, leased_places: {} }, Data)}, shared_places: {d}, leased_places: {} }, terms_b: Terms { unique: true, shared: true, leased: false, vars: {}, named_tys: {(Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, Data), (Terms { unique: true, shared: true, leased: false, vars: {}, named_tys: {(Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, Data)}, shared_places: {}, leased_places: {} }, Data)}, shared_places: {}, leased_places: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, d1: our Data, d2: our Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "sub_teams" failed at step #2 (src/file.rs:LL:CC) because
                                   condition evaluted to false: `all_places_covered_by_one_of(&terms_a.shared_places, &terms_b.shared_places)`
                                     &terms_a.shared_places = {d}
                                     &terms_b.shared_places = {}"#]]);
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
            3: judgment `can_type_expr_as { expr: { d2 . share ; }, as_ty: shared {d1} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d2 . share ; }, as_ty: shared {d1} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: shared {d2} my Data, b: shared {d1} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_in { terms_a: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, a: shared {d2} my Data, terms_b: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, b: shared {d1} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_terms { terms_a: Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {(Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {}, shared_places: {d2}, leased_places: {} }, Data)}, shared_places: {d2}, leased_places: {} }, terms_b: Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {(Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {}, shared_places: {d1}, leased_places: {} }, Data)}, shared_places: {d1}, leased_places: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "sub_teams" failed at step #2 (src/file.rs:LL:CC) because
                                   condition evaluted to false: `all_places_covered_by_one_of(&terms_a.shared_places, &terms_b.shared_places)`
                                     &terms_a.shared_places = {d2}
                                     &terms_b.shared_places = {d1}"#]]);
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
            3: judgment `can_type_expr_as { expr: { d1 . next . share ; }, as_ty: shared {d2} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . next . share ; }, as_ty: shared {d2} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: shared {d1 . next} my my Data, b: shared {d2} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_in { terms_a: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, a: shared {d1 . next} my my Data, terms_b: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, b: shared {d2} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_terms { terms_a: Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {(Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {}, shared_places: {d1 . next}, leased_places: {} }, Data)}, shared_places: {d1 . next}, leased_places: {} }, terms_b: Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {(Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {}, shared_places: {d2}, leased_places: {} }, Data)}, shared_places: {d2}, leased_places: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "sub_teams" failed at step #2 (src/file.rs:LL:CC) because
                                   condition evaluted to false: `all_places_covered_by_one_of(&terms_a.shared_places, &terms_b.shared_places)`
                                     &terms_a.shared_places = {d1 . next}
                                     &terms_b.shared_places = {d2}"#]]);
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
            3: judgment `can_type_expr_as { expr: { d1 . share ; }, as_ty: shared {d1 . next} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . share ; }, as_ty: shared {d1 . next} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: shared {d1} my Data, b: shared {d1 . next} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_in { terms_a: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, a: shared {d1} my Data, terms_b: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, b: shared {d1 . next} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_terms { terms_a: Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {(Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {}, shared_places: {d1}, leased_places: {} }, Data)}, shared_places: {d1}, leased_places: {} }, terms_b: Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {(Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {}, shared_places: {d1 . next}, leased_places: {} }, Data)}, shared_places: {d1 . next}, leased_places: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "sub_teams" failed at step #2 (src/file.rs:LL:CC) because
                                   condition evaluted to false: `all_places_covered_by_one_of(&terms_a.shared_places, &terms_b.shared_places)`
                                     &terms_a.shared_places = {d1}
                                     &terms_b.shared_places = {d1 . next}"#]]);
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
            3: judgment `can_type_expr_as { expr: { d1 . next . lease ; }, as_ty: shared {d1} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . next . lease ; }, as_ty: shared {d1} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: leased {d1 . next} my my Data, b: shared {d1} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_in { terms_a: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, a: leased {d1 . next} my my Data, terms_b: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, b: shared {d1} Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_terms { terms_a: Terms { unique: true, shared: false, leased: true, vars: {}, named_tys: {(Terms { unique: true, shared: false, leased: true, vars: {}, named_tys: {}, shared_places: {}, leased_places: {d1 . next} }, Data)}, shared_places: {}, leased_places: {d1 . next} }, terms_b: Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {(Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {}, shared_places: {d1}, leased_places: {} }, Data)}, shared_places: {d1}, leased_places: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d1: my Data, d2: my Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "sub_teams" failed at step #1 (src/file.rs:LL:CC) because
                                   condition evaluted to false: `terms_a.leased <= terms_b.leased`"#]]);
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
            3: judgment `can_type_expr_as { expr: { d1 . share ; }, as_ty: given {d1} Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . share ; }, as_ty: given {d1} Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: shared {d1} !perm_0 Data, b: given {d1} Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_in { terms_a: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, a: shared {d1} !perm_0 Data, terms_b: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, b: given {d1} Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_terms { terms_a: Terms { unique: false, shared: true, leased: false, vars: {(Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {}, shared_places: {d1}, leased_places: {} }, !perm_0), (Terms { unique: false, shared: true, leased: false, vars: {(Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {}, shared_places: {d1}, leased_places: {} }, !perm_0)}, named_tys: {}, shared_places: {d1}, leased_places: {} }, !perm_0)}, named_tys: {(Terms { unique: false, shared: true, leased: false, vars: {(Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {}, shared_places: {d1}, leased_places: {} }, !perm_0), (Terms { unique: false, shared: true, leased: false, vars: {(Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {}, shared_places: {d1}, leased_places: {} }, !perm_0)}, named_tys: {}, shared_places: {d1}, leased_places: {} }, !perm_0)}, named_tys: {}, shared_places: {d1}, leased_places: {} }, Data)}, shared_places: {d1}, leased_places: {} }, terms_b: Terms { unique: true, shared: false, leased: false, vars: {(Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, !perm_0)}, named_tys: {(Terms { unique: true, shared: false, leased: false, vars: {(Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, !perm_0)}, named_tys: {}, shared_places: {}, leased_places: {} }, Data), (Terms { unique: true, shared: false, leased: false, vars: {(Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, !perm_0)}, named_tys: {(Terms { unique: true, shared: false, leased: false, vars: {(Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, !perm_0)}, named_tys: {}, shared_places: {}, leased_places: {} }, Data)}, shared_places: {}, leased_places: {} }, Data)}, shared_places: {}, leased_places: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, d1: !perm_0 Data, d2: our Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "sub_teams" failed at step #0 (src/file.rs:LL:CC) because
                                   condition evaluted to false: `terms_a.shared <= terms_b.shared`"#]]);
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
            3: judgment `can_type_expr_as { expr: { d1 . give ; }, as_ty: given {d2} Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . give ; }, as_ty: given {d2} Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: !perm_0 Data, b: given {d2} Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {d1} } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_in { terms_a: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, a: !perm_0 Data, terms_b: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, b: given {d2} Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {d1} } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_terms { terms_a: Terms { unique: true, shared: false, leased: false, vars: {(Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, !perm_0)}, named_tys: {(Terms { unique: true, shared: false, leased: false, vars: {(Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, !perm_0)}, named_tys: {}, shared_places: {}, leased_places: {} }, Data)}, shared_places: {}, leased_places: {} }, terms_b: Terms { unique: true, shared: false, leased: false, vars: {(Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, !perm_1)}, named_tys: {(Terms { unique: true, shared: false, leased: false, vars: {(Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, !perm_1)}, named_tys: {}, shared_places: {}, leased_places: {} }, Data), (Terms { unique: true, shared: false, leased: false, vars: {(Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, !perm_1)}, named_tys: {(Terms { unique: true, shared: false, leased: false, vars: {(Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, !perm_1)}, named_tys: {}, shared_places: {}, leased_places: {} }, Data)}, shared_places: {}, leased_places: {} }, Data)}, shared_places: {}, leased_places: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {d1} } }` failed at the following rule(s):
                                 the rule "sub_teams" failed at step #4 (src/file.rs:LL:CC) because
                                   judgment `sub_forall_exists { a_s: {(Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, !perm_0)}, b_s: {(Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, !perm_1)}, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {d1} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment had no applicable rules: `sub_base { terms_a: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, a: !perm_0, terms_b: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, b: !perm_1, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_1 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {d1} } }`"#]]);
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
            3: judgment `can_type_expr_as { expr: { d1 . share ; }, as_ty: shared {d2} Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { d1 . share ; }, as_ty: shared {d2} Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: shared {d1} !perm_0 Data, b: shared {d2} Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `sub_in { terms_a: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, a: shared {d1} !perm_0 Data, terms_b: Terms { unique: true, shared: false, leased: false, vars: {}, named_tys: {}, shared_places: {}, leased_places: {} }, b: shared {d2} Data, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                               judgment `sub_terms { terms_a: Terms { unique: false, shared: true, leased: false, vars: {(Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {}, shared_places: {d1}, leased_places: {} }, !perm_0), (Terms { unique: false, shared: true, leased: false, vars: {(Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {}, shared_places: {d1}, leased_places: {} }, !perm_0)}, named_tys: {}, shared_places: {d1}, leased_places: {} }, !perm_0)}, named_tys: {(Terms { unique: false, shared: true, leased: false, vars: {(Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {}, shared_places: {d1}, leased_places: {} }, !perm_0), (Terms { unique: false, shared: true, leased: false, vars: {(Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {}, shared_places: {d1}, leased_places: {} }, !perm_0)}, named_tys: {}, shared_places: {d1}, leased_places: {} }, !perm_0)}, named_tys: {}, shared_places: {d1}, leased_places: {} }, Data)}, shared_places: {d1}, leased_places: {} }, terms_b: Terms { unique: false, shared: true, leased: false, vars: {(Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {}, shared_places: {d2}, leased_places: {} }, !perm_0)}, named_tys: {(Terms { unique: false, shared: true, leased: false, vars: {(Terms { unique: false, shared: true, leased: false, vars: {}, named_tys: {}, shared_places: {d2}, leased_places: {} }, !perm_0)}, named_tys: {}, shared_places: {d2}, leased_places: {} }, Data)}, shared_places: {d2}, leased_places: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !perm_1], local_variables: {self: my Main, d1: !perm_0 Data, d2: !perm_0 Data}, assumptions: {}, fresh: 0 }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "sub_teams" failed at step #2 (src/file.rs:LL:CC) because
                                   condition evaluted to false: `all_places_covered_by_one_of(&terms_a.shared_places, &terms_b.shared_places)`
                                     &terms_a.shared_places = {d1}
                                     &terms_b.shared_places = {d2}"#]]);
}
