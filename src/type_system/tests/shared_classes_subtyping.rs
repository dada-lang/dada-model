use formality_core::test;

#[test]
#[allow(non_snake_case)]
fn pair_given_Data_given_Data_to_pair_given_Data_given_Data() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self, d1: (given Data, given Data)) -> (given Data, given Data) {
                d1.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn pair_our_Data_our_Data_to_pair_given_Data_given_Data() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self, d1: (shared Data, shared Data)) -> (given Data, given Data) {
                d1.give;
            }
        }
        }, expect_test::expect![[r#"
            src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: (shared Data, shared Data)}, assumptions: {!perm_0 is relative, !perm_0 is atomic}, fresh: 0 } }

            src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: (shared Data, shared Data)}, assumptions: {!perm_0 is relative, !perm_0 is atomic}, fresh: 0 } }

            src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: (shared Data, shared Data)}, assumptions: {!perm_0 is relative, !perm_0 is atomic}, fresh: 0 } }

            src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: (shared Data, shared Data)}, assumptions: {!perm_0 is relative, !perm_0 is atomic}, fresh: 0 } }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn our_pair_Data_Data_to_pair_Data_Data() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self, d1: shared (Data, Data)) -> (Data, Data) {
                d1.give;
            }
        }
        }, expect_test::expect![[r#"
            src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: shared (Data, Data)}, assumptions: {!perm_0 is relative, !perm_0 is atomic}, fresh: 0 } }

            src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: shared (Data, Data)}, assumptions: {!perm_0 is relative, !perm_0 is atomic}, fresh: 0 } }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn our_pair_Data_Data_to_given_pair_Data_Data() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self, d1: shared (Data, Data)) -> given (Data, Data) {
                d1.give;
            }
        }
        }, expect_test::expect![[r#"
            src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: shared (Data, Data)}, assumptions: {!perm_0 is relative, !perm_0 is atomic}, fresh: 0 } }

            src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d1: shared (Data, Data)}, assumptions: {!perm_0 is relative, !perm_0 is atomic}, fresh: 0 } }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn my_pair_Data_Data_share_to_our_pair_Data_Data() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self, d1: given (Data, Data)) -> shared (Data, Data) {
                d1.give.share;
            }
        }
        });
}
