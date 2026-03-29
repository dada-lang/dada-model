use formality_core::test;

/// Pair is leased from P, but when you assign to its fields,
/// you must meet the full type as if it were owned (i.e., here, we need
/// to assign a `given` Data).
#[test]
fn assign_leased_to_field_of_lease_that_is_typed_as_given() {
    crate::assert_err!({
        class Data { }
        class Pair { d1: Data; d2: Data; }
        class Main {
            fn test[perm P](given self, pair: P Pair, data: P Data) -> ()
            where
                P is mut,
            {
                pair.d1 = data.give;
                ();
            }
        }
        }, expect_test::expect![[r#"src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, data: !perm_0 Data, pair: !perm_0 Pair}, assumptions: {!perm_0 is mut, !perm_0 is relative, !perm_0 is atomic}, fresh: 0 } }"#]]);
}

/// Pair is leased from P, but when you assign to its fields,
/// you must meet the full type as if it were owned (i.e., here, we need
/// to assign a `given` Data).
#[test]
fn assign_owned_to_field_of_lease_that_is_typed_as_given() {
    crate::assert_ok!({
        class Data { }
        class Pair { d1: Data; d2: Data; }
        class Main {
            fn test[perm P](given self, pair: P Pair, data: given Data) -> ()
            where
                P is mut,
            {
                pair.d1 = data.give;
                ();
            }
        }
        });
}

/// Test that field is not assignable when using a perm var that is not shared.
#[test]
#[allow(non_snake_case)]
fn forall_shared_P_assign_to_field_of_P_pair() {
    crate::assert_err!({
        class Data { }
        class Pair { d1: Data; d2: Data; }
        class Main {
            fn test[perm P](given self, pair: P Pair, data: given Data) -> ()
            where
                P is copy,
            {
                pair.d1 = data.give;
                ();
            }
        }
        }, expect_test::expect![[r#"
            src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, @ fresh(0): Data, data: given Data, pair: !perm_0 Pair}, assumptions: {!perm_0 is copy, !perm_0 is relative, !perm_0 is atomic}, fresh: 1 } }

            src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, @ fresh(0): Data, data: given Data, pair: !perm_0 Pair}, assumptions: {!perm_0 is copy, !perm_0 is relative, !perm_0 is atomic}, fresh: 1 } }

            src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, @ fresh(0): Data, data: given Data, pair: !perm_0 Pair}, assumptions: {!perm_0 is copy, !perm_0 is relative, !perm_0 is atomic}, fresh: 1 } }"#]]);
}

/// Test that field is not assignable when using a perm var that is not shared.
#[test]
#[allow(non_snake_case)]
fn forall_P_assign_to_field_of_P_pair() {
    crate::assert_err!({
        class Data { }
        class Pair { d1: Data; d2: Data; }
        class Main {
            fn test[perm P](given self, pair: P Pair, data: given Data) -> () {
                pair.d1 = data.give;
                ();
            }
        }
        }, expect_test::expect![[r#"
            src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, @ fresh(0): Data, data: given Data, pair: !perm_0 Pair}, assumptions: {!perm_0 is relative, !perm_0 is atomic}, fresh: 1 } }

            src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, @ fresh(0): Data, data: given Data, pair: !perm_0 Pair}, assumptions: {!perm_0 is relative, !perm_0 is atomic}, fresh: 1 } }

            src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, @ fresh(0): Data, data: given Data, pair: !perm_0 Pair}, assumptions: {!perm_0 is relative, !perm_0 is atomic}, fresh: 1 } }"#]]);
}
