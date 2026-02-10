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

mod liskov;

#[test]
#[allow(non_snake_case)]
fn forall__P__give__from__given_d1__to__ref_to_shared_d2() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self, d1: given Data, d2: P Data) -> ref[d2] Data {
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
fn forall__P__give__from__shared_given_d1__to__ref_to_shared_d2() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self, d1: given Data, d2: P Data) -> ref[d2] Data {
                d1.share;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn forall_copy_P_give_from_shared_d2_P_to_shared_d2() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self, d1: given Data, d2: P Data) -> ref[d2] Data
            where
                copy(P),
            {
                d2.ref;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn forall_copy_P_give_from_shared_d2_P_to_P() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self, d1: given Data, d2: P Data) -> P Data
            where
                copy(P),
            {
                d2.ref;
            }
        }
        });
}

#[test]
fn move_from_given_d1_to_our_d2() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test(given self, d1: given Data) -> shared Data {
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
fn share_from_given_d1_to_our_d2() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test(given self, d1: given Data) -> shared Data {
                d1.share;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn give_from_our_Data_to_shared_self() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test(given self) -> ref[self] Data {
                let d: shared Data = new Data().share;
                d.give;
            }
        }
        });
}

/// `shared` is a subtype of `copy(P)`.
#[test]
#[allow(non_snake_case)]
fn give_from_our_Data_to_copy_P() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self) -> P Data
            where
              copy(P)
            {
                let d: shared Data = new Data().share;
                d.give;
            }
        }
        });
}

/// `shared` is not a subtype of arbitrary P.
#[test]
#[allow(non_snake_case)]
fn give_from_our_Data_to_any_P() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) -> P Data
            {
                let d: shared Data = new Data();
                d.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

/// `shared` is not a subtype of arbitrary P.
#[test]
#[allow(non_snake_case)]
fn give_from_our_Data_to_leased_P() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) -> P Data
            where
                mut(P),
            {
                let d: shared Data = new Data();
                d.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

#[test]
fn share_from_given_d1_our_d2_to_given_from_d2() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test(given self, d1: given Data, d2: shared Data) -> given_from[d2] Data {
                d1.share;
            }
        }
        });
}

/// Return "given" from `d1` and give from `d1`.
/// It is indistinguishable as both of them are `shared` Data, so the result is `shared`.
#[test]
fn share_from_our_d1_our_d2_to_given_from_d1() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test(given self, d1: shared Data, d2: shared Data) -> given_from[d1] Data {
                d1.ref;
            }
        }
        });
}

/// Return "given" from `d2` even though we really give from `d1`.
/// It is indistinguishable as both of them are `shared` Data, so the result is `shared`.
#[test]
fn share_from_our_d1_our_d2_to_given_from_d2() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test(given self, d1: shared Data, d2: shared Data) -> given_from[d2] Data {
                d1.ref;
            }
        }
        });
}

/// Return "given" from `d2` even though we really give from `d1`.
/// It is indistinguishable as both of them are `shared` Data, so the result is `shared`.
#[test]
fn share_from_local_to_our() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test(given self, d1: shared Data, d2: shared Data) -> given_from[d2] Data {
                let d = new Data();
                d.ref;
            }
        }
        }, expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

#[test]
fn provide_shared_from_d1_expect_shared_from_d1() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test(given self, d1: given Data, d2: given Data) -> ref[d1] Data {
                d1.ref;
            }
        }
        });
}

#[test]
fn provide_shared_from_d2_expect_shared_from_d1() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test(given self, d1: given Data, d2: given Data) -> ref[d1] Data {
                d2.ref;
            }
        }
        }, expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                place_b = d1
                &place_a = d2

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

#[test]
fn provide_shared_from_d2_expect_shared_from_d1_or_d2() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test(given self, d1: given Data, d2: given Data) -> ref[d1, d2] Data {
                d2.ref;
            }
        }
        });
}

#[test]
fn provide_shared_from_d1_next_expect_shared_from_d1() {
    crate::assert_ok!({
        class Data {
            next: given Data;
        }

        class Main {
            fn test(given self, d1: given Data, d2: given Data) -> ref[d1] Data {
                d1.next.ref;
            }
        }
        });
}

#[test]
fn provide_shared_from_d1_next_expect_shared_from_d2() {
    crate::assert_err!({
        class Data {
            next: given Data;
        }

        class Main {
            fn test(given self, d1: given Data, d2: given Data) -> ref[d2] Data {
                d1.next.ref;
            }
        }
        }, expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                place_b = d2
                &place_a = d1 . next

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

#[test]
fn provide_shared_from_d1_expect_shared_from_d1_next() {
    crate::assert_err!({
        class Data {
            next: given Data;
        }

        class Main {
            fn test(given self, d1: given Data, d2: given Data) -> ref[d1.next] Data {
                d1.ref;
            }
        }
        }, expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                place_b = d1 . next
                &place_a = d1

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

#[test]
fn provide_leased_from_d1_next_expect_shared_from_d1() {
    crate::assert_err!({
        class Data {
            next: given Data;
        }

        class Main {
            fn test(given self, d1: given Data, d2: given Data) -> ref[d1] Data {
                d1.next.mut;
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
fn shared_from_P_d1_to_given_from_P_d1() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self, d1: P Data, d2: shared Data) -> given_from[d1] Data {
                d1.ref;
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
fn given_from_P_d1_to_given_from_P_d1() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self, d1: P Data, d2: shared Data) -> given_from[d1] Data {
                d1.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn given_from_P_d1_to_given_from_P_d2() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P, perm Q](given self, d1: P Data, d2: P Data) -> given_from[d2] Data {
                d1.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn given_from_P_d1_to_given_from_Q_d2() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P, perm Q](given self, d1: P Data, d2: Q Data) -> given_from[d2] Data {
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
fn shared_from_P_d1_to_shared_from_P_d1() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P, perm Q](given self, d1: P Data, d2: P Data) -> ref[d1] Data {
                d1.ref;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn shared_from_P_d1_to_shared_from_P_d2() {
    // Interesting example: we declare `ref[d2]` but return `ref[d1]`.
    // Even though both of them have permission `P`, we give an error.
    // The distinction of which `P` we shared from is important: we are not going to be incrementing
    // the ref count, so if `d1` were dropped, which the type signature suggests would be ok,
    // then the data would be freed.
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P, perm Q](given self, d1: P Data, d2: P Data) -> ref[d2] Data {
                d1.ref;
            }
        }
        }, expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                place_b = d2
                &place_a = d1

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

/// This case is wacky. The type of `data` is not really possible, as it indicates that data which was `mut[pair2]` was
/// shared from `pair1`, but `pair1` does not have any data leased from `pair2` in its type.
/// Currently we allow this to be upcast to `ref[pair1]` on the premise that is ok to lose history.
/// It seems to me that the type of `data` should (ideally) not be considered well-formed, but otherwise
/// this function is ok, it just could never actually be called.
#[test]
#[allow(non_snake_case)]
fn shared_pair1_leased_pair2_to_shared_pair1() {
    crate::assert_err!({
        class Pair {
            d1: Data;
            d2: Data;
        }
        class Data {
        }
        class Main {
            fn test(given self, pair1: Pair, pair2: Pair, data: ref[pair1] mut[pair2] Data) -> ref[pair1] Data {
                data.share;
            }
        }
        }, expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn our_leased_to_our() {
    crate::assert_err!({
        class Pair {
            d1: Data;
            d2: Data;
        }
        class Data {
        }
        class Main {
            fn test(given self, pair: Pair, data: shared mut[pair] Data) -> shared Data {
                data.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn our_leased_pair_to_our_leased_pair() {
    crate::assert_ok!({
        class Pair {
            d1: Data;
            d2: Data;
        }
        class Data {
        }
        class Main {
            fn test(given self, pair: Pair, data: shared mut[pair] Data) -> shared mut[pair] Data {
                data.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn our_leased_pair_d1_to_our_leased_pair() {
    crate::assert_ok!({
        class Pair {
            d1: Data;
            d2: Data;
        }
        class Data {
        }
        class Main {
            fn test(given self, pair: Pair, data: shared mut[pair.d1] Data) -> shared mut[pair] Data {
                data.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn shared_vec_given_Data_to_shared_vec_given_Data() {
    crate::assert_ok!({
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(given self, source: given Vec[given Data], data: ref[source] Vec[given Data]) -> ref[source] Vec[given Data] {
                data.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn shared_vec_given_Data_to_shared_vec_shared_Data() {
    crate::assert_ok!({
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(given self, source: given Vec[given Data], data: ref[source] Vec[given Data]) -> ref[source] Vec[ref[source] Data] {
                data.share;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn leased_vec_given_Data_to_leased_vec_given_Data() {
    crate::assert_ok!({
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(given self, source: given Vec[given Data], data: mut[source] Vec[given Data]) -> mut[source] Vec[given Data] {
                data.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn leased_vec_given_Data_to_leased_vec_leased_Data() {
    crate::assert_err!({
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(given self, source: given Vec[given Data], data: mut[source] Vec[given Data]) -> mut[source] Vec[mut[source] Data] {
                data.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn leased_vec_leased_Data_to_leased_vec_given_Data() {
    crate::assert_err!({
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(given self, source: given Vec[given Data], data: mut[source] Vec[mut[source] Data]) -> mut[source] Vec[given Data] {
                data.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn leased_vec_leased_Data_to_leased_vec_leased_Data() {
    crate::assert_ok!({
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(given self, source: given Vec[given Data], data: mut[source] Vec[mut[source] Data]) -> mut[source] Vec[mut[source] Data] {
                data.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn forall_P_vec_given_Data_to_P_vec_P_Data() {
    crate::assert_err!({
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test[perm P](given self, source: given Vec[given Data], data: P Vec[Data]) -> P Vec[P Data] {
                data.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_shared_P_P_vec_given_Data_to_P_vec_P_Data() {
    crate::assert_ok!({
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test[perm P](given self, source: given Vec[given Data], data: P Vec[Data]) -> P Vec[P Data]
            where
                copy(P),
            {
                data.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn our_vec_given_Data_to_our_vec_our_Data() {
    crate::assert_ok!({
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(given self, source: given Vec[given Data], data: shared Vec[Data]) -> shared Vec[shared Data]
            {
                data.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn our_vec_our_Data_to_our_vec_given_Data() {
    crate::assert_ok!({
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(given self, source: given Vec[given Data], data: shared Vec[shared Data]) -> shared Vec[given Data]
            {
                data.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn our_vec_shared_Data_to_shared_vec_given_Data() {
    crate::assert_ok!({
        class Vec[ty T] {
        }
        class Data {
        }
        class Main {
            fn test(given self, source: given Vec[given Data], data: given Vec[ref[source] Data]) -> ref[source] Vec[given Data]
            {
                data.share;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn ordering_matters() {
    crate::assert_err!({
        class Data { }
        class Pair[ty D] {
          first: D;
          second: D;
        }
        class Main {
            fn test[perm P, perm Q](given self, pair: P Pair[Q Data]) -> Q P Data {
                pair.first.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn pair_a_to_pair_generic() {
    // Here we upcast from `mut[pair.a] T` to `mut[pair] T`.
    // This is fine.
    crate::assert_ok!({
        class Pair[ty T] {
          a: T;
          b: T;
        }

        class Main {
          fn main[ty T](given self, pair: given Pair[T]) {
            let p: mut[pair] T = pair.a.mut;
          }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn pair_a_to_pair_monomorphized() {
    // Here we upcast from `mut[pair.a] T` to `mut[pair] P T`.
    // This is fine -- we lose precision on precisely what is borrowed,
    // but we remember the `P` (vs `Q`).
    crate::assert_ok!({
      class Pair[ty A, ty B] {
        a: A;
        b: B;
      }

      class Data { }

      class Main {
        fn main[perm P, perm Q](given self, pair: given Pair[P Data, Q Data]) {
          let p: mut[pair] P Data = pair.a.mut;
        }
      }
      });
}

#[test]
#[allow(non_snake_case)]
fn pair_a_to_pair_bad() {
    // Here we upcast from `mut[pair.a] T` to `mut[pair] T`.
    // This is not allowed because it effectively 'forgets' the `P` perm.
    crate::assert_err!({
      class Pair[ty T] {
        a: T;
        b: T;
      }

      class Data { }

      class Main {
        fn main[perm P](given self, pair: given Pair[P Data]) {
          let p: mut[pair] Data = pair.a.mut;
        }
      }
      }, expect_test::expect![[r#"
          the rule "parameter" at (predicates.rs) failed because
            pattern `true` did not match value `false`

          the rule "parameter" at (predicates.rs) failed because
            pattern `true` did not match value `false`

          the rule "parameter" at (predicates.rs) failed because
            pattern `true` did not match value `false`"#]]);
}
