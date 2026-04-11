//! Tests for subpermissions.
//!
//! Perm P is a *subpermission* of perm Q when `P T` is a subtype of `Q T` for all types `T`.

use formality_core::test;

#[test]
#[allow(non_snake_case)]
fn PermDataMy_is_subtype_of_PermDataMy() {
    crate::assert_ok!({
        class Data { }

        class PermData[perm P] {
            data: P Data;
        }

        class Main {
            fn test(given self, data: PermData[given]) {
                let m: PermData[given] = data.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn PermDataMy_not_subtype_of_PermDataOur() {
    crate::assert_err!({
        class Data { }

        class PermData[perm P] {
            data: P Data;
        }

        class Main {
            fn test(given self, data: PermData[given]) {
                let m: PermData[shared] = data.give;
            }
        }
        }, expect_test::expect![[r#"
            src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }

            src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }

            src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: PermData[given]}, assumptions: {}, fresh: 0 } }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn PermDataMy_is_not_subtype_of_PermDataLeased() {
    crate::assert_err!({
        class Data { }

        class PermData[perm P] {
            data: P Data;
        }

        class Main {
            fn test(given self, data: PermData[given]) {
                let d = new Data();
                let m: PermData[mut[d]] = data.give;
            }
        }
        }, expect_test::expect![[r#"
            src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }

            src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }

            src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn PermDataMy_is_not_subtype_of_PermDataShared() {
    crate::assert_err!({
        class Data { }

        class PermData[perm P] {
            data: P Data;
        }

        class Main {
            fn test(given self, data: PermData[given]) {
                let d = new Data();
                let m: PermData[ref[d]] = data.give;
            }
        }
        }, expect_test::expect![[r#"
            src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }

            src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: ref [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }

            src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }

            src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: ref [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }

            src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, data: PermData[given]}, assumptions: {}, fresh: 0 } }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn unsound_upgrade() {
    crate::assert_err!({
        class Data {
            fn mutate[perm P](P self)
            where
                P is mut,
            { }
        }

        class Query {
            data: shared Data;
        }

        class Main {
            fn test(given self, q1: Query, q2: Query) {
                let a: mut[q1.data] Data = q1.data.mut;
                let b: mut[q1] Data = a.give;
                b.mut.mutate[mut[q1]]();
            }
        }
        }, expect_test::expect![[r#"
            src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }

            src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }

            src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_exists() {
    crate::assert_ok!({
        class Query {
        }

        class Main {
            fn test(given self, q1: Query, q2: Query) {
                let a: ref[q1] Query = q1.ref;
                let b: ref[q2] Query = q2.ref;
                let c: ref[a] ref[q1] Query = a.ref;
                let d: ref[b] ref[q2] Query = b.ref;
                let x: ref[a, b] Query = c.give;
                let y: ref[a, b] Query = d.give;
            }
        }
        });
}
