use formality_core::test;

#[test]
#[allow(non_snake_case)]
fn Cell_T_our_Cell_Data_to_our_Cell_our_Data() {
    crate::assert_ok!({
        class Data {}
        class Cell[ty T]
        {
            f: T;
        }
        class Main {
            fn test(given self, d1: shared Cell[Data]) -> shared Cell[shared Data] {
                d1.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn Cell_atomic_T_our_Cell_Data_to_our_Cell_our_Data() {
    // Since T is T is atomic, we can't convert `shared Cell[Data]` to `shared Cell[shared Data]`.
    crate::assert_err!({
        class Data {}
        class Cell[ty T]
        where
            T is atomic,
        {
            atomic f: T;
        }
        class Main {
            fn test(given self, d1: shared Cell[Data]) -> shared Cell[shared Data] {
                d1.give;
            }
        }
        }, expect_test::expect![[r#"src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn Cell_rel_T_our_Cell_Data_to_our_Cell_our_Data() {
    // Since T is T is relative, we can't convert `shared Cell[Data]` to `shared Cell[shared Data]`.
    crate::assert_err!({
        class Data {}
        class Cell[ty T]
        where
            T is relative,
        {
        }
        class Main {
            fn test(given self, d1: shared Cell[Data]) -> shared Cell[shared Data] {
                d1.give;
            }
        }
        }, expect_test::expect![[r#"src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Cell[Data]}, assumptions: {}, fresh: 0 } }"#]]);
}
