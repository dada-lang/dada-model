use formality_core::test;

/// Pair is leased from P, but when you assign to its fields,
/// you must meet the full type as if it were owned (i.e., here, we need
/// to assign a `^` Data).
#[test]
fn assign_leased_to_field_of_lease_that_is_typed_as_given() {
    crate::assert_err!({
        struct Data { }
        struct Pair { d1: Data; d2: Data; }
        struct Main {
            fn test[perm P](^ self, pair: P Pair, data: P Data) -> ()
            where
                P is mut,
            {
                pair.d1 = data^;
                ();
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Pair { d1 : Data ; d2 : Data ; } struct Main { fn test [perm] (^ self pair : ^perm0_0 Pair, data : ^perm0_0 Data) -> () where ^perm0_0 is mut { pair . d1 = data ^ ; () ; } } }`"]);
}

/// Pair is leased from P, but when you assign to its fields,
/// you must meet the full type as if it were owned (i.e., here, we need
/// to assign a `^` Data).
#[test]
fn assign_owned_to_field_of_lease_that_is_typed_as_given() {
    crate::assert_ok!({
    struct Data { }
    struct Pair { d1: Data; d2: Data; }
    struct Main {
        fn test[perm P](^ self, pair: P Pair, data: ^ Data) -> ()
        where
            P is mut,
        {
            pair.d1 = data^;
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
        struct Data { }
        struct Pair { d1: Data; d2: Data; }
        struct Main {
            fn test[perm P](^ self, pair: P Pair, data: ^ Data) -> ()
            where
                P is shared,
            {
                pair.d1 = data^;
                ();
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Pair { d1 : Data ; d2 : Data ; } struct Main { fn test [perm] (^ self pair : ^perm0_0 Pair, data : ^ Data) -> () where ^perm0_0 is shared { pair . d1 = data ^ ; () ; } } }`"]);
}

/// Test that field is not assignable when using a perm var that is not shared.
#[test]
#[allow(non_snake_case)]
fn forall_P_assign_to_field_of_P_pair() {
    crate::assert_err!({
        struct Data { }
        struct Pair { d1: Data; d2: Data; }
        struct Main {
            fn test[perm P](^ self, pair: P Pair, data: ^ Data) -> () {
                pair.d1 = data^;
                ();
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Pair { d1 : Data ; d2 : Data ; } struct Main { fn test [perm] (^ self pair : ^perm0_0 Pair, data : ^ Data) -> () { pair . d1 = data ^ ; () ; } } }`"]);
}
