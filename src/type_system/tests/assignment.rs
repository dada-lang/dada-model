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
                mut(P),
            {
                pair.d1 = data.give;
                ();
            }
        }
        }, expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
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
                mut(P),
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
                copy(P),
            {
                pair.d1 = data.give;
                ();
            }
        }
        }, expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
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
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}
