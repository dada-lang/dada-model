//! Tests for subtyping. These tests can be grouped into various categories.
//!
//! ## Liskov Substitution Principle (LSP)
//!
//! The "Liskov Substitution Principle" is that if T1 <: T2, then a value of type T1 can be
//! substituted for a value of type T2 and nothing can go wrong. The "liskov" directory
//! aims to systematically explore this area.
//!
//! ## Other stuff
//!
//! The other tests here need to be categorized. =)

use formality_core::test;

mod copy_types;
mod liskov;

#[test]
#[allow(non_snake_case)]
fn forall__P__give__from__given_d1__to__ref_to_shared_d2() {
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test[perm P](given self, d1: given Data, d2: P Data) -> shared[d2] Data {
                d1^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test [perm] (given self d1 : given Data, d2 : ^perm0_0 Data) -> shared [d2] Data { d1 ^ ; } } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn forall__P__give__from__shared_given_d1__to__ref_to_shared_d2() {
    crate::assert_ok!({
    struct Data { }
    struct Main {
        fn test[perm P](given self, d1: given Data, d2: P Data) -> shared[d2] Data {
            d1^.share;
        }
    }
    });
}

#[test]
#[allow(non_snake_case)]
fn forall_copy_P_give_from_shared_d2_P_to_shared_d2() {
    crate::assert_ok!({
    struct Data { }
    struct Main {
        fn test[perm P](given self, d1: given Data, d2: P Data) -> shared[d2] Data
        where
            P is shared,
        {
            d2.share;
        }
    }
    });
}

#[test]
#[allow(non_snake_case)]
fn forall_copy_P_give_from_shared_d2_P_to_P() {
    crate::assert_ok!({
    struct Data { }
    struct Main {
        fn test[perm P](given self, d1: given Data, d2: P Data) -> P Data
        where
            P is shared,
        {
            d2.share;
        }
    }
    });
}

#[test]
fn move_from_given_d1_to_our_d2() {
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test(given self, d1: given Data) -> shared Data {
                d1^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test (given self d1 : given Data) -> shared Data { d1 ^ ; } } }`"]);
}

#[test]
fn share_from_given_d1_to_our_d2() {
    crate::assert_ok!({
    struct Data { }
    struct Main {
        fn test(given self, d1: given Data) -> shared Data {
            d1^.share;
        }
    }
    });
}

#[test]
#[allow(non_snake_case)]
fn give_from_our_Data_to_shared_self() {
    crate::assert_ok!({
    struct Data { }
    struct Main {
        fn test(given self) -> shared[self] Data {
            let d: shared Data = new Data().share;
            d^;
        }
    }
    });
}

/// `shared` is a subtype of `copy(P)`.
#[test]
#[allow(non_snake_case)]
fn give_from_our_Data_to_copy_P() {
    crate::assert_ok!({
    struct Data { }
    struct Main {
        fn test[perm P](given self) -> P Data
        where
          P is shared
        {
            let d: shared Data = new Data().share;
            d^;
        }
    }
    });
}

/// `shared` is not a subtype of arbitrary P.
#[test]
#[allow(non_snake_case)]
fn give_from_our_Data_to_any_P() {
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test[perm P](given self) -> P Data
            {
                let d: shared Data = new Data();
                d^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test [perm] (given self) -> ^perm0_0 Data { let d : shared Data = new Data () ; d ^ ; } } }`"]);
}

/// `shared` is not a subtype of arbitrary P.
#[test]
#[allow(non_snake_case)]
fn give_from_our_Data_to_leased_P() {
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test[perm P](given self) -> P Data
            where
                P is mut,
            {
                let d: shared Data = new Data();
                d^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test [perm] (given self) -> ^perm0_0 Data where ^perm0_0 is mut { let d : shared Data = new Data () ; d ^ ; } } }`"]);
}

#[test]
fn share_from_given_d1_our_d2_to_given_from_d2() {
    crate::assert_ok!({
    struct Data { }
    struct Main {
        fn test(given self, d1: given Data, d2: shared Data) -> given[d2] Data {
            d1^.share;
        }
    }
    });
}

/// Return "given" from `d1` and give from `d1`.
/// It is indistinguishable as both of them are `shared` Data, so the result is `shared`.
#[test]
fn share_from_our_d1_our_d2_to_given_from_d1() {
    crate::assert_ok!({
    struct Data { }
    struct Main {
        fn test(given self, d1: shared Data, d2: shared Data) -> given[d1] Data {
            d1.share;
        }
    }
    });
}

/// Return "given" from `d2` even though we really give from `d1`.
/// It is indistinguishable as both of them are `shared` Data, so the result is `shared`.
#[test]
fn share_from_our_d1_our_d2_to_given_from_d2() {
    crate::assert_ok!({
    struct Data { }
    struct Main {
        fn test(given self, d1: shared Data, d2: shared Data) -> given[d2] Data {
            d1.share;
        }
    }
    });
}

/// Return "given" from `d2` even though we really give from `d1`.
/// It is indistinguishable as both of them are `shared` Data, so the result is `shared`.
#[test]
fn share_from_local_to_our() {
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test(given self, d1: shared Data, d2: shared Data) -> given[d2] Data {
                let d = new Data();
                d.share;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test (given self d1 : shared Data, d2 : shared Data) -> given [d2] Data { let d = new Data () ; d . share ; } } }`"]);
}

#[test]
fn provide_shared_from_d1_expect_shared_from_d1() {
    crate::assert_ok!({
    struct Data { }
    struct Main {
        fn test(given self, d1: given Data, d2: given Data) -> shared[d1] Data {
            d1.share;
        }
    }
    });
}

#[test]
fn provide_shared_from_d2_expect_shared_from_d1() {
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test(given self, d1: given Data, d2: given Data) -> shared[d1] Data {
                d2.share;
            }
        }
        }, expect_test::expect![[r#"
            the rule "(shared[place]::P) vs (shared[place]::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(place_a)`
                place_b = d1
                place_a = d2"#]]);
}

#[test]
fn provide_shared_from_d2_expect_shared_from_d1_or_d2() {
    crate::assert_ok!({
    struct Data { }
    struct Main {
        fn test(given self, d1: given Data, d2: given Data) -> shared[d1, d2] Data {
            d2.share;
        }
    }
    });
}

#[test]
fn provide_shared_from_d1_next_expect_shared_from_d1() {
    crate::assert_ok!({
    struct Data {
        next: given Data;
    }

    struct Main {
        fn test(given self, d1: given Data, d2: given Data) -> shared[d1] Data {
            d1.next.share;
        }
    }
    });
}

#[test]
fn provide_shared_from_d1_next_expect_shared_from_d2() {
    crate::assert_err!({
        struct Data {
            next: given Data;
        }

        struct Main {
            fn test(given self, d1: given Data, d2: given Data) -> shared[d2] Data {
                d1.next.share;
            }
        }
        }, expect_test::expect![[r#"
            the rule "(shared[place]::P) vs (shared[place]::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(place_a)`
                place_b = d2
                place_a = d1 . next"#]]);
}

#[test]
fn provide_shared_from_d1_expect_shared_from_d1_next() {
    crate::assert_err!({
        struct Data {
            next: given Data;
        }

        struct Main {
            fn test(given self, d1: given Data, d2: given Data) -> shared[d1.next] Data {
                d1.share;
            }
        }
        }, expect_test::expect![[r#"
            the rule "(shared[place]::P) vs (shared[place]::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(place_a)`
                place_b = d1 . next
                place_a = d1"#]]);
}

#[test]
fn provide_leased_from_d1_next_expect_shared_from_d1() {
    crate::assert_err!({
        struct Data {
            next: given Data;
        }

        struct Main {
            fn test(given self, d1: given Data, d2: given Data) -> shared[d1] Data {
                d1.next!;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { next : given Data ; } struct Main { fn test (given self d1 : given Data, d2 : given Data) -> shared [d1] Data { d1 . next ! ; } } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn shared_from_P_d1_to_given_from_P_d1() {
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test[perm P](given self, d1: P Data, d2: shared Data) -> given[d1] Data {
                d1.share;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test [perm] (given self d1 : ^perm0_0 Data, d2 : shared Data) -> given [d1] Data { d1 . share ; } } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn given_from_P_d1_to_given_from_P_d1() {
    crate::assert_ok!({
    struct Data { }
    struct Main {
        fn test[perm P](given self, d1: P Data, d2: shared Data) -> given[d1] Data {
            d1^;
        }
    }
    });
}

#[test]
#[allow(non_snake_case)]
fn given_from_P_d1_to_given_from_P_d2() {
    crate::assert_ok!({
    struct Data { }
    struct Main {
        fn test[perm P, perm Q](given self, d1: P Data, d2: P Data) -> given[d2] Data {
            d1^;
        }
    }
    });
}

#[test]
#[allow(non_snake_case)]
fn given_from_P_d1_to_given_from_Q_d2() {
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test[perm P, perm Q](given self, d1: P Data, d2: Q Data) -> given[d2] Data {
                d1^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn test [perm, perm] (given self d1 : ^perm0_0 Data, d2 : ^perm0_1 Data) -> given [d2] Data { d1 ^ ; } } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn shared_from_P_d1_to_shared_from_P_d1() {
    crate::assert_ok!({
    struct Data { }
    struct Main {
        fn test[perm P, perm Q](given self, d1: P Data, d2: P Data) -> shared[d1] Data {
            d1.share;
        }
    }
    });
}

#[test]
#[allow(non_snake_case)]
fn shared_from_P_d1_to_shared_from_P_d2() {
    // Interesting example: we declare `shared[d2]` but return `shared[d1]`.
    // Even though both of them have permission `P`, we give an error.
    // The distinction of which `P` we shared from is important: we are not going to be incrementing
    // the reference count, so if `d1` were dropped, which the type signature suggests would be ok,
    // then the data would be freed.
    crate::assert_err!({
        struct Data { }
        struct Main {
            fn test[perm P, perm Q](given self, d1: P Data, d2: P Data) -> shared[d2] Data {
                d1.share;
            }
        }
        }, expect_test::expect![[r#"
            the rule "(shared[place]::P) vs (shared[place]::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(place_a)`
                place_b = d2
                place_a = d1"#]]);
}

/// This case is wacky. The type of `data` is not really possible, as it indicates that data which was `![pair2]` was
/// shared from `pair1`, but `pair1` does not have any data leased from `pair2` in its type.
/// Currently we allow this to be upcast to `shared[pair1]` on the premise that is ok to lose history.
/// It seems to me that the type of `data` should (ideally) not be considered well-formed, but otherwise
/// this function is ok, it just could never actually be called.
#[test]
#[allow(non_snake_case)]
fn shared_pair1_leased_pair2_to_shared_pair1() {
    crate::assert_err!({
        struct Pair {
            d1: Data;
            d2: Data;
        }
        struct Data {
        }
        struct Main {
            fn test(given self, pair1: given Pair, pair2: given Pair, data: shared[pair1] ![pair2] Data) -> shared[pair1] Data {
                data^.share;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Pair { d1 : Data ; d2 : Data ; } struct Data { } struct Main { fn test (given self pair1 : given Pair, pair2 : given Pair, data : shared [pair1] ! [pair2] Data) -> shared [pair1] Data { data ^ . share ; } } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn our_leased_to_our() {
    crate::assert_err!({
        struct Pair {
            d1: Data;
            d2: Data;
        }
        struct Data {
        }
        struct Main {
            fn test(given self, pair: given Pair, data: shared ![pair] Data) -> shared Data {
                data^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Pair { d1 : Data ; d2 : Data ; } struct Data { } struct Main { fn test (given self pair : given Pair, data : shared ! [pair] Data) -> shared Data { data ^ ; } } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn our_leased_pair_to_our_leased_pair() {
    crate::assert_ok!({
    struct Pair {
        d1: Data;
        d2: Data;
    }
    struct Data {
    }
    struct Main {
        fn test(given self, pair: given Pair, data: shared ![pair] Data) -> shared ![pair] Data {
            data^;
        }
    }
    });
}

#[test]
#[allow(non_snake_case)]
fn our_leased_pair_d1_to_our_leased_pair() {
    crate::assert_ok!({
    struct Pair {
        d1: Data;
        d2: Data;
    }
    struct Data {
    }
    struct Main {
        fn test(given self, pair: given Pair, data: shared ![pair.d1] Data) -> shared ![pair] Data {
            data^;
        }
    }
    });
}

#[test]
#[allow(non_snake_case)]
fn shared_vec_given_Data_to_shared_vec_given_Data() {
    crate::assert_ok!({
    struct Vec[ty T] {
    }
    struct Data {
    }
    struct Main {
        fn test(given self, source: given Vec[given Data], data: shared[source] Vec[given Data]) -> shared[source] Vec[given Data] {
            data^;
        }
    }
    });
}

#[test]
#[allow(non_snake_case)]
fn shared_vec_given_Data_to_shared_vec_shared_Data() {
    crate::assert_ok!({
    struct Vec[ty T] {
    }
    struct Data {
    }
    struct Main {
        fn test(given self, source: given Vec[given Data], data: shared[source] Vec[given Data]) -> shared[source] Vec[shared[source] Data] {
            data^.share;
        }
    }
    });
}

#[test]
#[allow(non_snake_case)]
fn leased_vec_given_Data_to_leased_vec_given_Data() {
    crate::assert_ok!({
    struct Vec[ty T] {
    }
    struct Data {
    }
    struct Main {
        fn test(given self, source: given Vec[given Data], data: ![source] Vec[given Data]) -> ![source] Vec[given Data] {
            data^;
        }
    }
    });
}

#[test]
#[allow(non_snake_case)]
fn leased_vec_given_Data_to_leased_vec_leased_Data() {
    crate::assert_err!({
        struct Vec[ty T] {
        }
        struct Data {
        }
        struct Main {
            fn test(given self, source: given Vec[given Data], data: ![source] Vec[given Data]) -> ![source] Vec[![source] Data] {
                data^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Vec [ty] { } struct Data { } struct Main { fn test (given self source : given Vec[given Data], data : ! [source] Vec[given Data]) -> ! [source] Vec[! [source] Data] { data ^ ; } } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn leased_vec_leased_Data_to_leased_vec_given_Data() {
    crate::assert_err!({
        struct Vec[ty T] {
        }
        struct Data {
        }
        struct Main {
            fn test(given self, source: given Vec[given Data], data: ![source] Vec[![source] Data]) -> ![source] Vec[given Data] {
                data^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Vec [ty] { } struct Data { } struct Main { fn test (given self source : given Vec[given Data], data : ! [source] Vec[! [source] Data]) -> ! [source] Vec[given Data] { data ^ ; } } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn leased_vec_leased_Data_to_leased_vec_leased_Data() {
    crate::assert_ok!({
    struct Vec[ty T] {
    }
    struct Data {
    }
    struct Main {
        fn test(given self, source: given Vec[given Data], data: ![source] Vec[![source] Data]) -> ![source] Vec[![source] Data] {
            data^;
        }
    }
    });
}

#[test]
#[allow(non_snake_case)]
fn forall_P_vec_given_Data_to_P_vec_P_Data() {
    crate::assert_err!({
        struct Vec[ty T] {
        }
        struct Data {
        }
        struct Main {
            fn test[perm P](given self, source: given Vec[given Data], data: P Vec[Data]) -> P Vec[P Data] {
                data^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Vec [ty] { } struct Data { } struct Main { fn test [perm] (given self source : given Vec[given Data], data : ^perm0_0 Vec[Data]) -> ^perm0_0 Vec[^perm0_0 Data] { data ^ ; } } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn forall_shared_P_P_vec_given_Data_to_P_vec_P_Data() {
    crate::assert_ok!({
    struct Vec[ty T] {
    }
    struct Data {
    }
    struct Main {
        fn test[perm P](given self, source: given Vec[given Data], data: P Vec[Data]) -> P Vec[P Data]
        where
            P is shared,
        {
            data^;
        }
    }
    });
}

#[test]
#[allow(non_snake_case)]
fn our_vec_given_Data_to_our_vec_our_Data() {
    crate::assert_ok!({
    struct Vec[ty T] {
    }
    struct Data {
    }
    struct Main {
        fn test(given self, source: given Vec[given Data], data: shared Vec[Data]) -> shared Vec[shared Data]
        {
            data^;
        }
    }
    });
}

#[test]
#[allow(non_snake_case)]
fn our_vec_our_Data_to_our_vec_given_Data() {
    crate::assert_ok!({
    struct Vec[ty T] {
    }
    struct Data {
    }
    struct Main {
        fn test(given self, source: given Vec[given Data], data: shared Vec[shared Data]) -> shared Vec[given Data]
        {
            data^;
        }
    }
    });
}

#[test]
#[allow(non_snake_case)]
fn our_vec_shared_Data_to_shared_vec_given_Data() {
    crate::assert_ok!({
    struct Vec[ty T] {
    }
    struct Data {
    }
    struct Main {
        fn test(given self, source: given Vec[given Data], data: given Vec[shared[source] Data]) -> shared[source] Vec[given Data]
        {
            data^.share;
        }
    }
    });
}

#[test]
#[allow(non_snake_case)]
fn ordering_matters() {
    crate::assert_err!({
        struct Data { }
        struct Pair[ty D] {
          first: D;
          second: D;
        }
        struct Main {
            fn test[perm P, perm Q](given self, pair: P Pair[Q Data]) -> Q P Data {
                pair.first^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Pair [ty] { first : ^ty0_0 ; second : ^ty0_0 ; } struct Main { fn test [perm, perm] (given self pair : ^perm0_0 Pair[^perm0_1 Data]) -> ^perm0_1 ^perm0_0 Data { pair . first ^ ; } } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn pair_a_to_pair_generic() {
    // Here we upcast from `![pair.a] T` to `![pair] T`.
    // This is fine.
    crate::assert_ok!({
        struct Pair[ty T] {
          a: T;
          b: T;
        }

        struct Main {
          fn main[ty T](given self, pair: given Pair[T])
          where
            T is unique,
          {
            let p: ![pair] T = pair.a!;
          }
        }
    });
}

#[test]
#[allow(non_snake_case)]
fn pair_a_to_pair_monomorphized() {
    // Here we upcast from `![pair.a] T` to `![pair] P T`.
    // This is fine -- we lose precision on precisely what is borrowed,
    // but we remember the `P` (vs `Q`).
    crate::assert_ok!({
    struct Pair[ty A, ty B] {
      a: A;
      b: B;
    }

    struct Data { }

    struct Main {
      fn main[perm P, perm Q](given self, pair: given Pair[P Data, Q Data])
      where
        P is unique,
      {
        let p: ![pair] P Data = pair.a!;
      }
    }
    });
}

#[test]
#[allow(non_snake_case)]
fn pair_a_to_pair_bad() {
    // Here we upcast from `![pair.a] T` to `![pair] T`.
    // This is not allowed because it effectively 'forgets' the `P` perm.
    crate::assert_err!({
      struct Pair[ty T] {
        a: T;
        b: T;
      }

      struct Data { }

      struct Main {
        fn main[perm P](given self, pair: given Pair[P Data]) {
          let p: ![pair] Data = pair.a!;
        }
      }
      }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Pair [ty] { a : ^ty0_0 ; b : ^ty0_0 ; } struct Data { } struct Main { fn main [perm] (given self pair : given Pair[^perm0_0 Data]) -> () { let p : ! [pair] Data = pair . a ! ; } } }`"]);
}
