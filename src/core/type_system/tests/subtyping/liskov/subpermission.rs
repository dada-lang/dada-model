//! # Subpermission
//!
//! All operations permitted by supertype must be permitted by the subtype.
//!
//! C1. This begins with edits on the data structure itself, so `shared Foo` cannot be a subtype of `given Foo`
//! since the latter permits field mutation.
//!
//! C2. This also includes restrictions on what can be done in the environment. So `shared[d1] Foo` cannot
//! be a subtype of `shared[d2] Foo` since the latter permits `d1` to be modified but the subtype does not.
//! (The latter also restricts edits to `d2`, but that's ok in the supertype, it can be more restrictive.)

use formality_core::test;

// C1. This begins with edits on the data structure itself, so `shared Foo` cannot be a subtype of `given Foo`
// since the latter permits field mutation.

#[test]
fn c1_given_subtype_of_our() {
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test(given self) {
                let m: given Data = new Data();
                let p: shared Data = m->;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test (given self) -> () { let m : given Data = new Data () ; let p : shared Data = m -> ; } } }`"]);
}

#[test]
fn c1_our_not_subtype_of_given() {
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test(given self) {
                let m: shared Data = new Data();
                let p: given Data = m->;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test (given self) -> () { let m : shared Data = new Data () ; let p : given Data = m -> ; } } }`"]);
}

#[test]
fn c1_given_subtype_of_shared() {
    // In this test, the data is given from `n` and hence has type `given Data`.
    // But the type indicates it is shared from `m`.
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test(given self) {
                let m: given Data = new Data();
                let n: given Data = new Data();
                let p: shared[m] Data = n->;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test (given self) -> () { let m : given Data = new Data () ; let n : given Data = new Data () ; let p : shared [m] Data = n -> ; } } }`"]);
}

#[test]
fn c1_our_subtype_of_shared() {
    // In this test, the data is given from `n` and hence has type `shared Data`.
    // But the type indicates it is shared from `m`.
    // This is less accurate than the ideal but allowed by subtyping.
    crate::assert_ok!({
    struct Data { }
    struct Main {
        fn test(given self) {
            let m: given Data = new Data();
            let n: shared Data = m->.share;
            let p: shared[m] Data = n->;
        }
    }
    });
}

#[test]
#[allow(non_snake_case)]
fn c1_given_not_subtype_of_P() {
    // given is not a subtype of generic permission `P` because it may be leased
    // (which would violate compatible layout rules).
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: P Data = n->;
            }
        }
        }, expect_test::expect![[r#"
            the rule "give place" at (expressions.rs) failed because
              no variable named `n`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn c1_given_subtype_of_P_where_P_shared() {
    // given IS a subtype of generic permission `P`
    // because it is declared as `shared` and hence is layout compatible.
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test[perm P](given self) where P is shared {
                let m: given Data = new Data();
                let p: P Data = m->;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test [perm] (given self) -> () where ^perm0_0 is shared { let m : given Data = new Data () ; let p : ^perm0_0 Data = m -> ; } } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn c1_newData_assignable_to_P_where_P_shared() {
    // given IS a subtype of generic permission `P`
    // because it is declared as `shared` and hence is layout compatible.
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test[perm P](given self) where P is shared {
                let m: P Data = new Data();
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test [perm] (given self) -> () where ^perm0_0 is shared { let m : ^perm0_0 Data = new Data () ; } } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn c1_our_not_subtype_of_P_where_P_copy() {
    // `shared` is a subtype of generic permission `P`
    // when it is declared as `copy`.
    crate::assert_ok!({
    struct Data { }
    struct Main {
        fn test[perm P](given self) where P is shared {
            let m: given Data = new Data();
            let o: shared Data = m->.share;
            let p: P Data = o->;
        }
    }
    });
}

#[test]
#[allow(non_snake_case)]
fn c1_P_not_subtype_of_given_where_P_shared() {
    // P is *not* a subtype of `given`, even though it is declared as `shared`.
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test[perm P](given self) where P is shared {
                let m: P Data = new Data();
                let p: given Data = n->;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test [perm] (given self) -> () where ^perm0_0 is shared { let m : ^perm0_0 Data = new Data () ; let p : given Data = n -> ; } } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn c1_P_not_subtype_of_our_where_P_shared() {
    // P is *not* a subtype of `shared`, even though it is declared as shared.
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test[perm P](given self) where P is shared {
                let m: P Data = new Data();
                let p: shared Data = n->;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test [perm] (given self) -> () where ^perm0_0 is shared { let m : ^perm0_0 Data = new Data () ; let p : shared Data = n -> ; } } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn c1_P_not_subtype_of_Q_where_PQ_shared() {
    // P is *not* a subtype of `shared`, even though it is declared as shared.
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test[perm P, perm Q](given self) where P is shared, Q is shared {
                let m: P Data = new Data();
                let p: Q Data = m->;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test [perm, perm] (given self) -> () where ^perm0_0 is shared, ^perm0_1 is shared { let m : ^perm0_0 Data = new Data () ; let p : ^perm0_1 Data = m -> ; } } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn c1_newData_assignable_to_shared() {
    // Variation of [`c1_given_subtype_of_shared`][] in which
    // `new Data()` is assigned to a `shared[m] Data` variable.
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test(given self) {
                let p: shared[m] Data = new Data();
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_place" at (types.rs) failed because
              no variable named `m`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn c1_given_not_subtype_of_leased() {
    // `given` is not a subtype of leased. This is actually because of the layout rules;
    // permissions-wise they would be compatible.
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test(given self) {
                let m: given Data = new Data();
                let p: ![m] Data = new Data();
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test (given self) -> () { let m : given Data = new Data () ; let p : ! [m] Data = new Data () ; } } }`"]);
}

#[test]
fn c1_leased_not_subtype_of_shared() {
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test(given self) {
                let m: given Data = new Data();
                let p: ![m] Data = m!;
                let q: shared[m] Data = p->;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test (given self) -> () { let m : given Data = new Data () ; let p : ! [m] Data = m ! ; let q : shared [m] Data = p -> ; } } }`"]);
}

#[test]
fn c1_shared_not_subtype_of_leased() {
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test(given self) {
                let m: given Data = new Data();
                let p: shared[m] Data = m.share;
                let q: ![m] Data = p->;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test (given self) -> () { let m : given Data = new Data () ; let p : shared [m] Data = m . share ; let q : ! [m] Data = p -> ; } } }`"]);
}

// C2. This also includes restrictions on what can be done in the environment. So `shared[d1] Foo` cannot
// be a subtype of `shared[d2] Foo` since the latter permits `d1` to be modified but the subtype does not.
// (The latter also restricts edits to `d2`, but that's ok in the supertype, it can be more restrictive.)

#[test]
#[allow(non_snake_case)]
fn c2_shared_m_subtype_of_shared_mn() {
    // `shared[m]` is a subtype of `shared[m, n]`: neither permit `m` to be modified.
    // The supertype `shared[m, n]` additionally prohibits `n` from being modified.
    crate::assert_ok!({
    struct Data { }
    struct Main {
        fn test(given self) {
            let m: given Data = new Data();
            let n: given Data = new Data();
            let p: shared[m] Data = m.share;
            let q: shared[m, n] Data = p->;
        }
    }
    });
}

#[test]
#[allow(non_snake_case)]
fn c2_leased_m_subtype_of_leased_mn() {
    // `![m]` is a subtype of `![m, n]`: neither permit `m` to be modified.
    // The supertype `![m, n]` additionally prohibits `n` from being modified.
    crate::assert_ok!({
    struct Data { }
    struct Main {
        fn test(given self) {
            let m: given Data = new Data();
            let n: given Data = new Data();
            let p: ![m] Data = m!;
            let q: ![m, n] Data = p->;
        }
    }
    });
}

#[test]
#[allow(non_snake_case)]
fn c2_leased_mn_not_subtype_of_leased_m() {
    // `![m, n]` is not a subtype of `![m]`: the supertype permits `n` to be modified.
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test(given self) {
                let m: given Data = new Data();
                let n: given Data = new Data();
                let p: ![m, n] Data = m!;
                let q: ![m] Data = p->;
            }
        }
        }, expect_test::expect![[r#"
            the rule "(mut::P) vs (mut::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(place_a)`
                place_b = m
                place_a = n"#]]);
}
