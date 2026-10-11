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
        fn test(^ self, data: PermData[^]) {
            let m: PermData[^] = data^;
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
            fn test(^ self, data: PermData[^]) {
                let m: PermData[shared] = data^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { } class PermData [perm] { data : ^perm0_0 Data ; } class Main { fn test (^ self data : PermData[^]) -> () { let m : PermData[shared] = data ^ ; } } }`"]);
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
            fn test(^ self, data: PermData[^]) {
                let d = new Data();
                let m: PermData[![d]] = data^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { } class PermData [perm] { data : ^perm0_0 Data ; } class Main { fn test (^ self data : PermData[^]) -> () { let d = new Data () ; let m : PermData[! [d]] = data ^ ; } } }`"]);
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
            fn test(^ self, data: PermData[^]) {
                let d = new Data();
                let m: PermData[shared[d]] = data^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { } class PermData [perm] { data : ^perm0_0 Data ; } class Main { fn test (^ self data : PermData[^]) -> () { let d = new Data () ; let m : PermData[shared [d]] = data ^ ; } } }`"]);
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
            fn test(^ self, q1: Query, q2: Query) {
                let a: ![q1.data] Data = q1.data!;
                let b: ![q1] Data = a^;
                b!.mutate[![q1]]();
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { fn mutate [perm] (^perm0_0 self) -> () where ^perm0_0 is mut { } } class Query { data : shared Data ; } class Main { fn test (^ self q1 : Query, q2 : Query) -> () { let a : ! [q1 . data] Data = q1 . data ! ; let b : ! [q1] Data = a ^ ; b ! . mutate [! [q1]] () ; } } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn forall_exists() {
    crate::assert_ok!({
    class Query {
    }

    class Main {
        fn test(^ self, q1: Query, q2: Query) {
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
