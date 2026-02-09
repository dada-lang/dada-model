use formality_core::test;

#[test]
#[allow(non_snake_case)]
fn pair_given_Data_given_Data_to_pair_given_Data_given_Data() {
    crate::assert_ok!("
        class Data { }
        class Main {
            fn test[perm P](given self, d1: (given Data, given Data)) -> (given Data, given Data) {
                d1.move;
            }
        }
        ");
}

#[test]
#[allow(non_snake_case)]
fn pair_our_Data_our_Data_to_pair_given_Data_given_Data() {
    crate::assert_err!("
        class Data { }
        class Main {
            fn test[perm P](given self, d1: (shared Data, shared Data)) -> (given Data, given Data) {
                d1.move;
            }
        }
        ", expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn our_pair_Data_Data_to_pair_Data_Data() {
    crate::assert_err!("
        class Data { }
        class Main {
            fn test[perm P](given self, d1: shared (Data, Data)) -> (Data, Data) {
                d1.move;
            }
        }
        ", expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn our_pair_Data_Data_to_given_pair_Data_Data() {
    crate::assert_err!("
        class Data { }
        class Main {
            fn test[perm P](given self, d1: shared (Data, Data)) -> given (Data, Data) {
                d1.move;
            }
        }
        ", expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn my_pair_Data_Data_share_to_our_pair_Data_Data() {
    crate::assert_ok!("
        class Data { }
        class Main {
            fn test[perm P](given self, d1: given (Data, Data)) -> shared (Data, Data) {
                d1.share;
            }
        }
        ");
}
