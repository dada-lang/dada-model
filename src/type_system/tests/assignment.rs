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
            3: judgment `can_type_expr_as { expr: { pair . d1 = data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {leased(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { pair . d1 = data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {leased(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { pair . d1 = data . give ; () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {leased(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { pair . d1 = data . give ; () ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {leased(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [pair . d1 = data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {leased(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: pair . d1 = data . give ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {leased(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "let" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_expr_as { expr: data . give, as_ty: Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {leased(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {pair} } }` failed at the following rule(s):
                                         the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `sub { a: !perm_0 Data, b: Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {leased(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `sub_in_cx { chain_a: my, a: !perm_0 Data, chain_b: my, b: Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {leased(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                   judgment `sub_ty_chain_sets { ty_liens_a: {NamedTy(!perm_0, Data)}, ty_liens_b: {NamedTy(my, Data)}, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {leased(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `sub_ty_chains { ty_chain_a: NamedTy(!perm_0, Data), ty_chain_b: NamedTy(my, Data), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {leased(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "named ty" failed at step #3 (src/file.rs:LL:CC) because
                                                           judgment had no applicable rules: `sub_lien_chains { a: !perm_0, b: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: my Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {leased(!perm_0)}, fresh: 0 } }`"#]]);
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
