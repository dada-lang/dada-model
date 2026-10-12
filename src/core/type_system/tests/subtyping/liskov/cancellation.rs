//! # Liveness and cancellation
//!
//! When variables are dead, subtyping allows for *cancellation*, so e.g. if `d1` is dead,
//! then `shared[d1] ![d2] Foo` is a subtype of `![d2] Foo`. Cancellation only
//! applies when we have a shared/leased permission applies to a leased permission.
//!
//! Consideration to test:
//!
//! * C1. Cancellation can remove "relative" permissions like `shared` and `leased`, but not owned permissions
//!   like `given` or `shared` nor generic permissions (since in that case we do not know which variables they
//!   may refer to)
//! * C2. Cancellation can only occur if all variables in the permission are dead: so `shared[d1, d2]` can only
//!   be canceled if `d1` and `d2` are both dead.
//! * C3. Cancellation cannot convert a shared permission into a leased permission.
//! * C4. Subtyping must account for future cancellation. So e.g., `![d1, d2] Foo` cannot be a subtype of
//!   `![d1] ![d2] Foo` since, if `d1` later goes dead, the supertype could be upcast
//!   to `![d2] Foo` but the subtype could not. That would be unsound.

use formality_core::test;

// C1. Cancellation can remove "relative" permissions like `shared` and `leased`.

#[test]
fn c1_remove_relative_shared() {
    crate::assert_ok!({
    struct Data { }
    struct Main {
        fn test[perm P](given self) {
            let m: given Data = new Data();
            let p: shared[m] Data = m.share;
            let q: shared[p] shared[m] Data = p.share;
            let r: shared[m] Data = q^;
        }
    }
    });
}

#[test]
fn c1_remove_relative_leased() {
    crate::assert_ok!({
    struct Data { }
    struct Main {
        fn test[perm P](given self) {
            let m: given Data = new Data();
            let p: ![m] Data = m!;
            let q: ![p] Data = p!;
            let r: ![m] Data = q^;
        }
    }
    });
}

// C1. Cancellation and `given` permission are not very relevant.
//
// The `given given` type here is equivalent to `given` so this just becomes
// ownership transfer.

#[test]
fn c1_remove_given() {
    crate::assert_ok!({
    struct Data { }
    struct Main {
        fn test[perm P](given self) {
            let m: given Data = new Data();
            let p: given given Data = m^;
            let q: given Data = p^;
        }
    }
    });
}

// C1. Cancellation cannot remove owned permissions `shared`.

#[test]
fn c1_remove_our() {
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: shared given Data = m^;
                let q: given Data = p^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test [perm] (given self) -> () { let m : given Data = new Data () ; let p : shared given Data = m ^ ; let q : given Data = p ^ ; } } }`"]);
}

// C1. Cancellation cannot remove generic permissions `shared`.

#[test]
fn c1_remove_generic_permissions() {
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test[perm P](given self, p: P given Data) {
                let q: given Data = p^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test [perm] (given self p : ^perm0_0 given Data) -> () { let q : given Data = p ^ ; } } }`"]);
}

// C2. Cancellation can only occur if all variables in the permission are dead.

#[test]
fn c2_shared_shared_one_of_one_variables_dead() {
    crate::assert_ok!({
    struct Data { }
    struct Main {
        fn test[perm P](given self) {
            let m: given Data = new Data();
            let p: shared[m] Data = m.share;
            let q: shared[p] shared[m] Data = p.share;
            let r: shared[m] Data = q^;
        }
    }
    });
}

#[test]
fn c2_shared_shared_two_of_two_variables_dead() {
    crate::assert_ok!({
    struct Data { }
    struct Main {
        fn test[perm P](given self) {
            let m: given Data = new Data();
            let p: shared[m] Data = m.share;
            let q: shared[m] Data = m.share;
            let r: shared[p, q] shared[m] Data = p.share;
            let s: shared[m] Data = r^;
        }
    }
    });
}

#[test]
fn c2_shared_shared_one_of_two_variables_dead() {
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: shared[m] Data = m.share;
                let q: shared[m] Data = m.share;
                let r: shared[p, q] shared[m] Data = p.share;
                let s: shared[m] Data = r^;
                q^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test [perm] (given self) -> () { let m : given Data = new Data () ; let p : shared [m] Data = m . share ; let q : shared [m] Data = m . share ; let r : shared [p, q] shared [m] Data = p . share ; let s : shared [m] Data = r ^ ; q ^ ; } } }`"]);
}

#[test]
fn c2_leased_leased_one_of_one_variables_dead() {
    crate::assert_ok!({
    struct Data { }
    struct Main {
        fn test[perm P](given self) {
            let m: given Data = new Data();
            let p: ![m] Data = m!;
            let q: ![p] Data = p!;
            let r: ![m] Data = q^;
        }
    }
    });
}

#[test]
fn c2_leased_leased_two_of_two_variables_dead() {
    crate::assert_ok!({
    struct Data {}
    struct Pair {
        a: given Data;
        b: given Data;
    }
    struct Main {
        fn test[perm P](given self) {
            let m: given Pair = new Pair(new Data(), new Data());
            let p: ![m.a] Data = m.a!;
            let q: ![m.b] Data = m.b!;
            let r: ![p, q] Data = p!;
            let s: ![m] Data = r^;
        }
    }
    });
}

#[test]
fn c2_leased_leased_one_of_two_variables_dead() {
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: ![m] Data = m!;
                let q: ![m] Data = m!;
                let r: ![p, q] ![m] Data = p!;
                let s: ![m] Data = r^;
                q^;
            }
        }
        }, expect_test::expect![[r#"
            the rule "lease-mutation" at (accesses.rs) failed because
              condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
                accessed_place = m
                leased_place = m"#]]);
}

// C3. Cancellation cannot convert a shared permission into a leased permission.

#[test]
fn c3_shared_leased_one_of_one_variables_dead() {
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: ![m] Data = m!;
                let q: shared[p] ![m] Data = p.share;
                let r: ![m] Data = q^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test [perm] (given self) -> () { let m : given Data = new Data () ; let p : ! [m] Data = m ! ; let q : shared [p] ! [m] Data = p . share ; let r : ! [m] Data = q ^ ; } } }`"]);
}

#[test]
fn c3_shared_leased_two_of_two_variables_dead() {
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: ![m] Data = m.share;
                let q: ![m] Data = m.share;
                let r: shared[p, q] ![m] Data = p.share;
                let s: shared[m] Data = r^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test [perm] (given self) -> () { let m : given Data = new Data () ; let p : ! [m] Data = m . share ; let q : ! [m] Data = m . share ; let r : shared [p, q] ! [m] Data = p . share ; let s : shared [m] Data = r ^ ; } } }`"]);
}

#[test]
fn c3_shared_leased_one_of_two_variables_dead() {
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: shared[m] Data = m.share;
                let q: shared[m] Data = m.share;
                let r: shared[p, q] shared[m] Data = p.share;
                let s: shared[m] Data = r^;
                q^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test [perm] (given self) -> () { let m : given Data = new Data () ; let p : shared [m] Data = m . share ; let q : shared [m] Data = m . share ; let r : shared [p, q] shared [m] Data = p . share ; let s : shared [m] Data = r ^ ; q ^ ; } } }`"]);
}

// C4. Subtyping must account for future cancellation.

#[test]
fn c4_shared_d1d2d3_not_subtype_of_shared_d1_shared_d2d3() {
    // This is interesting. It fails because `shared[d1] shared[d2, d3]`
    // is equivalent to `shared[d2, d3]` and there is clearly no subtyping relation.
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test[perm P](given self) {
                let d1: given Data = new Data();
                let d2: given Data = new Data();
                let d3: given Data = new Data();
                let s1: shared[d1, d2, d3] Data = d1.share;
                let s2: shared[d1] shared[d2, d3] Data = s1^;
            }
        }
        }, expect_test::expect![[r#"
            the rule "(shared[place]::P) vs (shared[place]::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(place_a)`
                place_b = d2
                place_a = d1

            the rule "(shared[place]::P) vs (shared[place]::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(place_a)`
                place_b = d3
                place_a = d1"#]]);
}

#[test]
fn c4_leased_d1d2d3_subtype_of_leased_d1_leased_d2d3() {
    // This one fails because `![d1, d2, d3]` and `![d1] ![d2, d3]` are
    // different; the latter would require that `d1` contained data leased from `d2` or `d3`.
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test[perm P](given self) {
                let d1: given Data = new Data();
                let d2: given Data = new Data();
                let d3: given Data = new Data();
                let s1: ![d1, d2, d3] Data = d1!;
                let s2: ![d1] ![d2, d3] Data = s1^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test [perm] (given self) -> () { let d1 : given Data = new Data () ; let d2 : given Data = new Data () ; let d3 : given Data = new Data () ; let s1 : ! [d1, d2, d3] Data = d1 ! ; let s2 : ! [d1] ! [d2, d3] Data = s1 ^ ; } } }`"]);
}

#[test]
fn c4_leased_d1d2_leased_pair_not_subtype_of_leased_d2() {
    // This one fails because you after cancelling `d1` you don't get `d2`.
    crate::assert_err!({
        struct Pair {
            a: given Data;
            b: given Data;
        }
        struct Data { }
        struct Main {
            fn test[perm P](given self, pair: P Pair) where P is mut {
                let d1: ![pair.a] Data = pair.a!;
                let d2: ![pair.b] Data = pair.b!;
                let s1: ![d1, d2] Data = d1!;
                let s2: ![d2] Data = s1^;
                let _x = self^.consume(pair^, s2^);
            }

            fn consume[perm P](given self, pair: P Pair, from_b: ![pair.b] Data) where P is mut { (); }
        }
        }, expect_test::expect![[r#"
            the rule "(mut::P) vs (mut::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(place_a)`
                place_b = d2
                place_a = pair . a

            the rule "(mut::P) vs (mut::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(place_a)`
                place_b = d2
                place_a = d1"#]]);
}
