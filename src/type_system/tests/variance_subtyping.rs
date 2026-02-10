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
    // Since T is atomic(T), we can't convert `shared Cell[Data]` to `shared Cell[shared Data]`.
    crate::assert_err!({
        class Data {}
        class Cell[ty T]
        where
            atomic(T),
        {
            atomic f: T;
        }
        class Main {
            fn test(given self, d1: shared Cell[Data]) -> shared Cell[shared Data] {
                d1.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn Cell_rel_T_our_Cell_Data_to_our_Cell_our_Data() {
    // Since T is relative(T), we can't convert `shared Cell[Data]` to `shared Cell[shared Data]`.
    crate::assert_err!({
        class Data {}
        class Cell[ty T]
        where
            relative(T),
        {
        }
        class Main {
            fn test(given self, d1: shared Cell[Data]) -> shared Cell[shared Data] {
                d1.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}
