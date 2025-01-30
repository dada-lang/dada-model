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
                leased(P),
            {
                pair.d1 = data.give;
                ();
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { d1 : Data ; d2 : Data ; } class Main { fn test [perm] (my self pair : ^perm0_0 Pair, data : ^perm0_0 Data) -> () where leased(^perm0_0) { pair . d1 = data . give ; () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { pair . d1 = data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {leased(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { pair . d1 = data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {leased(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { pair . d1 = data . give ; () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {leased(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { pair . d1 = data . give ; () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {leased(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [pair . d1 = data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {leased(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: pair . d1 = data . give ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {leased(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "reassign" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_expr_as { expr: data . give, as_ty: Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {leased(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {pair} } }` failed at the following rule(s):
                                         the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `sub { a: !perm_0 Data, b: Data, live_after: LivePlaces { accessed: {}, traversed: {pair} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {leased(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `sub_under_perms { perms_a: Perms { copied: false, shared_from: {}, leased_from: {}, variables: {} }, a: !perm_0 Data, perms_b: Perms { copied: false, shared_from: {}, leased_from: {}, variables: {} }, b: Data, live_after: LivePlaces { accessed: {}, traversed: {pair} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {leased(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `sub_some { lien_data_a: LienData { perms: Perms { copied: false, shared_from: {}, leased_from: {}, variables: {!perm_0} }, data: NamedTy(Data) }, lien_datas_b: {LienData { perms: Perms { copied: false, shared_from: {}, leased_from: {}, variables: {} }, data: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {pair} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {leased(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `sub_lien_data { lien_data_a: LienData { perms: Perms { copied: false, shared_from: {}, leased_from: {}, variables: {!perm_0} }, data: NamedTy(Data) }, lien_data_b: LienData { perms: Perms { copied: false, shared_from: {}, leased_from: {}, variables: {} }, data: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {pair} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {leased(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                                           judgment `sub_perms { perms_a: Perms { copied: false, shared_from: {}, leased_from: {}, variables: {!perm_0} }, perms_b: Perms { copied: false, shared_from: {}, leased_from: {}, variables: {} }, live_after: LivePlaces { accessed: {}, traversed: {pair} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {leased(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                               condition evaluted to false: `perms_a.is_lent(&env).implies(perms_b.is_lent(&env))`"#]]);
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
                leased(P),
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
                                       judgment `is_unique { a: !perm_0 Pair, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, @ fresh(0): Data, data: my Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                         the rule "is_leased" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `lien_chain_is_unique { chain: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, @ fresh(0): Data, data: my Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                             the rule "leased" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `lien_chain_is_leased { chain: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, @ fresh(0): Data, data: my Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                                 the rule "var" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `prove_predicate { predicate: leased(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, @ fresh(0): Data, data: my Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                                     the rule "leased" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `is_leased { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, @ fresh(0): Data, data: my Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                                         the rule "is_leased" failed at step #1 (src/file.rs:LL:CC) because
                                                           cyclic proof attempt: `lien_chain_is_leased { chain: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, @ fresh(0): Data, data: my Data, pair: !perm_0 Pair}, assumptions: {copy(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }`"#]]);
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
                                       judgment `is_unique { a: !perm_0 Pair, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, @ fresh(0): Data, data: my Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                         the rule "is_leased" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `lien_chain_is_unique { chain: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, @ fresh(0): Data, data: my Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                             the rule "leased" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `lien_chain_is_leased { chain: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, @ fresh(0): Data, data: my Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                                 the rule "var" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `prove_predicate { predicate: leased(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, @ fresh(0): Data, data: my Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                                     the rule "leased" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `is_leased { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, @ fresh(0): Data, data: my Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }` failed at the following rule(s):
                                                         the rule "is_leased" failed at step #1 (src/file.rs:LL:CC) because
                                                           cyclic proof attempt: `lien_chain_is_leased { chain: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, @ fresh(0): Data, data: my Data, pair: !perm_0 Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 1 } }`"#]]);
}
