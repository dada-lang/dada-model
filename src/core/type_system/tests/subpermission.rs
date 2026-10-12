//! Tests for subpermissions.
//!
//! Perm P is a *subpermission* of perm Q when `P T` is a subtype of `Q T` for all types `T`.

use formality_core::test;

#[test]
#[allow(non_snake_case)]
fn PermDataMy_is_subtype_of_PermDataMy() {
    crate::assert_ok!({
    struct Data { }

    struct PermData[perm P] {
        data: P Data;
    }

    struct Main {
        fn test(given self, data: given PermData[given]) {
            let m: PermData[given] = data^;
        }
    }
    });
}

#[test]
#[allow(non_snake_case)]
fn PermDataMy_not_subtype_of_PermDataOur() {
    crate::assert_err!({
        struct Data { }

        struct PermData[perm P] {
            data: P Data;
        }

        struct Main {
            fn test(given self, data: given PermData[given]) {
                let m: PermData[shared] = data^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct PermData [perm] { data : ^perm0_0 Data ; } struct Main { fn test (given self data : given PermData[given]) -> () { let m : PermData[shared] = data ^ ; } } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn PermDataMy_is_not_subtype_of_PermDataLeased() {
    crate::assert_err!({
        struct Data { }

        struct PermData[perm P] {
            data: P Data;
        }

        struct Main {
            fn test(given self, data: given PermData[given]) {
                let d = new Data();
                let m: PermData[![d]] = data^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct PermData [perm] { data : ^perm0_0 Data ; } struct Main { fn test (given self data : given PermData[given]) -> () { let d = new Data () ; let m : PermData[! [d]] = data ^ ; } } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn PermDataMy_is_not_subtype_of_PermDataShared() {
    crate::assert_err!({
        struct Data { }

        struct PermData[perm P] {
            data: P Data;
        }

        struct Main {
            fn test(given self, data: given PermData[given]) {
                let d = new Data();
                let m: PermData[shared[d]] = data^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct PermData [perm] { data : ^perm0_0 Data ; } struct Main { fn test (given self data : given PermData[given]) -> () { let d = new Data () ; let m : PermData[shared [d]] = data ^ ; } } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn unsound_upgrade() {
    crate::assert_err!({
        struct Data {
            fn mutate[perm P](P self)
            where
                P is mut,
            { }
        }

        struct Query {
            data: shared Data;
        }

        struct Main {
            fn test(given self, q1: given Query, q2: given Query) {
                let a: ![q1.data] Data = q1.data!;
                let b: ![q1] Data = a^;
                b!.mutate[![q1]]();
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { fn mutate [perm] (^perm0_0 self) -> () where ^perm0_0 is mut { } } struct Query { data : shared Data ; } struct Main { fn test (given self q1 : given Query, q2 : given Query) -> () { let a : ! [q1 . data] Data = q1 . data ! ; let b : ! [q1] Data = a ^ ; b ! . mutate [! [q1]] () ; } } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn forall_exists() {
    crate::assert_ok!({
    struct Query {
    }

    struct Main {
        fn test(given self, q1: given Query, q2: given Query) {
            let a: shared[q1] Query = q1.share;
            let b: shared[q2] Query = q2.share;
            let c: shared[a] shared[q1] Query = a.share;
            let d: shared[b] shared[q2] Query = b.share;
            let x: shared[a, b] Query = c^;
            let y: shared[a, b] Query = d^;
        }
    }
    });
}
