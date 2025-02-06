use crate::{dada_lang::term, type_system::check_program};
use formality_core::{test, test_util::ResultTestExt};

/// Pair is leased from P, but when you assign to its fields,
/// you must meet the full type as if it were owned (i.e., here, we need
/// to assign a `my` Data).
#[test]
fn assign_leased_to_field_of_lease_that_is_typed_as_my() {
    check_program(&term(
        "
        class Data { }
        class Pair { d1: Data; d2: Data; }
        class Main {
            fn test[perm P](my self, pair: P Pair, data: P Data) -> ()
            where
                move(P),
                lent(P),
            {
                pair.d1 = data.give;
                ();
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { d1 : Data ; d2 : Data ; } class Main { fn test [perm] (my self pair : ^perm0_0 Pair, data : ^perm0_0 Data) -> () where move(^perm0_0), lent(^perm0_0) { pair . d1 = data . give ; () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { pair . d1 = data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { pair . d1 = data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { pair . d1 = data . give ; () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { pair . d1 = data . give ; () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [pair . d1 = data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: pair . d1 = data . give ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "reassign" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_expr_as { expr: data . give, as_ty: Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {pair} } }` failed at the following rule(s):
                                         the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `sub { a: !perm_0 Data, b: Data, live_after: LivePlaces { accessed: {}, traversed: {pair} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: !perm_0 Data, chain_b: Chain { liens: [] }, b: Data, live_after: LivePlaces { accessed: {}, traversed: {pair} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [Variable(!perm_0)] }, ty: NamedTy(Data) }, ty_chains_b: {TyChain { chain: Chain { liens: [] }, ty: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {pair} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [Variable(!perm_0)] }, ty: NamedTy(Data) }, ty_chain_b: TyChain { chain: Chain { liens: [] }, ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {pair} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                                           judgment `sub_chains { chain_a: Chain { liens: [Variable(!perm_0)] }, chain_b: Chain { liens: [] }, live_after: LivePlaces { accessed: {}, traversed: {pair} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                               condition evaluted to false: `chain_a.is_owned(&env)`
                                                                 chain_a = Chain { liens: [Variable(!perm_0)] }
                                                                 &env = Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }
                                                             the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                               condition evaluted to false: `chain_a.is_owned(&env)`
                                                                 chain_a = Chain { liens: [Variable(!perm_0)] }
                                                                 &env = Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }
                                                             the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                               condition evaluted to false: `chain_a.is_owned(&env)`
                                                                 chain_a = Chain { liens: [Variable(!perm_0)] }
                                                                 &env = Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {move(!perm_0), lent(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }"#]]);
}

/// Pair is leased from P, but when you assign to its fields,
/// you must meet the full type as if it were owned (i.e., here, we need
/// to assign a `my` Data).
#[test]
fn assign_owned_to_field_of_lease_that_is_typed_as_my() {
    check_program(&term(
        "
        class Data { }
        class Pair { d1: Data; d2: Data; }
        class Main {
            fn test[perm P](my self, pair: P Pair, data: my Data) -> ()
            where
                move(P),
                lent(P),
            {
                pair.d1 = data.give;
                ();
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

/// Test that field is not assignable when using a perm var that is not shared.
#[test]
#[allow(non_snake_case)]
fn forall_shared_P_assign_to_field_of_P_pair() {
    check_program(&term(
        "
        class Data { }
        class Pair { d1: Data; d2: Data; }
        class Main {
            fn test[perm P](my self, pair: P Pair, data: my Data) -> ()
            where
                copy(P),
            {
                pair.d1 = data.give;
                ();
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { d1 : Data ; d2 : Data ; } class Main { fn test [perm] (my self pair : ^perm0_0 Pair, data : my Data) -> () where copy(^perm0_0) { pair . d1 = data . give ; () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { pair . d1 = data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: my Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { pair . d1 = data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: my Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { pair . d1 = data . give ; () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: my Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { pair . d1 = data . give ; () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: my Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [pair . d1 = data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: my Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: pair . d1 = data . give ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: my Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "reassign" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `prove_is_moved { a: !perm_0 Pair, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, @ fresh(0): Data, data: my Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                         the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `prove_predicate { predicate: move(!perm_0 Pair), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, @ fresh(0): Data, data: my Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                             the rule "moved" failed at step #1 (src/file.rs:LL:CC) because
                                               condition evaluted to false: `is_moved`"#]]);
}

/// Test that field is not assignable when using a perm var that is not shared.
#[test]
#[allow(non_snake_case)]
fn forall_P_assign_to_field_of_P_pair() {
    check_program(&term(
        "
        class Data { }
        class Pair { d1: Data; d2: Data; }
        class Main {
            fn test[perm P](my self, pair: P Pair, data: my Data) -> () {
                pair.d1 = data.give;
                ();
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { d1 : Data ; d2 : Data ; } class Main { fn test [perm] (my self pair : ^perm0_0 Pair, data : my Data) -> () { pair . d1 = data . give ; () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { pair . d1 = data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: my Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { pair . d1 = data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: my Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { pair . d1 = data . give ; () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: my Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { pair . d1 = data . give ; () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: my Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [pair . d1 = data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: my Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: pair . d1 = data . give ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: my Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "reassign" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `prove_is_moved { a: !perm_0 Pair, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, @ fresh(0): Data, data: my Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                         the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `prove_predicate { predicate: move(!perm_0 Pair), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, @ fresh(0): Data, data: my Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                             the rule "moved" failed at step #1 (src/file.rs:LL:CC) because
                                               condition evaluted to false: `is_moved`"#]]);
}
