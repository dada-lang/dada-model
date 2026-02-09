use formality_core::test;

mod borrowck_loan_kills;

/// Check sharing a field from a leased value errs.
#[test]
#[allow(non_snake_case)]
fn share_field_of_leased_value() {
    crate::assert_err!("
                class Data { }

                class Foo {
                    i: Data;
                }

                class Main {
                    fn main(given self) {
                        let foo = new Foo(new Data());
                        let bar = foo.mut;
                        let i = foo.i.ref;
                        bar.move;
                        ();
                    }
                }
            ", expect_test::expect![[r#"
                the rule "lease-mutation" at (accesses.rs) failed because
                  condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
                    &accessed_place = foo . i
                    &leased_place = foo"#]])
}

/// Check sharing a field from a shared value is ok.
#[test]
#[allow(non_snake_case)]
fn share_field_of_shared_value() {
    crate::assert_ok!("
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn main(given self) {
                    let foo = new Foo(new Data());
                    let bar = foo.ref;
                    let i = foo.i.ref;
                    bar.move;
                    ();
                }
            }
        ")
}

/// Check leasing a field from a shared value is not ok.
#[test]
#[allow(non_snake_case)]
fn lease_field_of_shared_value() {
    crate::assert_err!("
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn main(given self) {
                    let foo = new Foo(new Data());
                    let bar = foo.ref;
                    let i = foo.i.mut;
                    bar.move;
                    ();
                }
            }
        ", expect_test::expect![[r#"
            the rule "share-mutation" at (accesses.rs) failed because
              condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
                &accessed_place = foo . i
                &shared_place = foo"#]])
}

/// Check giving a field from a shared value is not ok.
#[test]
#[allow(non_snake_case)]
fn give_field_of_shared_value() {
    crate::assert_err!("
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn main(given self) {
                    let foo = new Foo(new Data());
                    let bar = foo.ref;
                    let i = foo.i.move;
                    bar.move;
                    ();
                }
            }
        ", expect_test::expect![[r#"
            the rule "share-give" at (accesses.rs) failed because
              condition evaluted to false: `place_disjoint_from_or_prefix_of(&accessed_place, &shared_place)`
                &accessed_place = foo . i
                &shared_place = foo"#]])
}

/// Check sharing a field from a leased value errs.
#[test]
#[allow(non_snake_case)]
fn share_field_of_leased_value_after_explicit_give() {
    crate::assert_ok!("
                class Data { }

                class Foo {
                    i: Data;
                }

                class Main {
                    fn main(given self) {
                        let foo = new Foo(new Data());
                        let bar = foo.mut;
                        bar.move;
                        let i = foo.i.ref;
                        ();
                    }
                }
            ")
}

/// Check that we can permit accessing `foo.i` even though
/// it was leased since `bar` is dead.
#[test]
#[allow(non_snake_case)]
fn share_field_of_leased_value_without_explicit_give() {
    crate::assert_ok!("
                class Data { }

                class Foo {
                    i: Data;
                }

                class Main {
                    fn main(given self) {
                        let foo = new Foo(new Data());
                        let bar = foo.mut;
                        let i = foo.i.ref;
                        ();
                    }
                }
            ")
}

#[test]
fn share_field_of_leased_value_but_lease_variable_is_dead() {
    // Here, the variable `q` is dead, but its restrictions must
    // still be enforced because `r` is live.
    crate::assert_err!("
                class Data { }

                class Foo {
                    i: Data;
                }

                class Main {
                    fn main(given self) {
                        let p = new Foo(new Data());
                        let q = p.mut;
                        let r = q.ref;
                        let i = p.i.ref;
                        r.move;
                        ();
                    }
                }
            ", expect_test::expect![[r#"
                the rule "lease-mutation" at (accesses.rs) failed because
                  condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
                    &accessed_place = p . i
                    &leased_place = p"#]])
}

#[test]
fn share_field_of_leased_value_but_lease_variable_is_dead_explicit_ty() {
    // Here, the variable `q` is dead, but its restrictions must
    // still be enforced because `r` is live.
    crate::assert_err!("
                class Data { }

                class Foo {
                    i: Data;
                }

                class Main {
                    fn main(given self) {
                        let p: given Foo = new Foo(new Data());
                        let q: mut[p] Foo = p.mut;
                        let r: ref[q] Foo = q.ref;
                        let i: ref[p.i] Data = p.i.ref;
                        r.move;
                        ();
                    }
                }
            ", expect_test::expect![[r#"
                the rule "lease-mutation" at (accesses.rs) failed because
                  condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
                    &accessed_place = p . i
                    &leased_place = p"#]])
}

/// Test where we expect data leased from self and then try to use self.
/// Error.
#[test]
#[allow(non_snake_case)]
fn pair_method__leased_self__use_self() {
    crate::assert_err!("
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, data: mut[self] Data) {
                  self.a.mut;
                  data.move;
                  ();
                }
            }
        ", expect_test::expect![[r#"
            the rule "lease-mutation" at (accesses.rs) failed because
              condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
                &accessed_place = self . a
                &leased_place = self"#]])
}

/// Test that we cannot mutate fields of a shared class.
#[test]
#[allow(non_snake_case)]
fn mutate_field_of_shared_pair() {
    crate::assert_err!("
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, data: given Data) {
                  let me = self.ref;
                  me.a = data.move;
                  ();
                }
            }
        ", expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]])
}

/// Test that we cannot mutate fields of a shared class.
#[test]
#[allow(non_snake_case)]
fn mutate_field_of_our_pair() {
    crate::assert_err!("
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, pair: shared Pair, data: given Data) {
                  pair.a = data.move;
                  ();
                }
            }
        ", expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]])
}

/// Test that we can mutate fields of a leased class.
#[test]
#[allow(non_snake_case)]
fn mutate_field_of_leased_pair() {
    crate::assert_ok!("
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, data: given Data) {
                  let me = self.mut;
                  me.a = data.move;
                  ();
                }
            }
        ")
}

// Test that we can give from `shared` and go on using it
#[test]
#[allow(non_snake_case)]
fn give_our_then_use_later_and_return() {
    crate::assert_ok!("
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, data: shared Data) -> shared Data {
                  let d: shared Data = data.move;
                  let e: shared Data = data.move;
                  let f: shared Data = data.move;
                  d.move;
                }
            }
        ")
}

// Test that we can give from `shared` and go on using it
#[test]
#[allow(non_snake_case)]
fn give_shared_then_use_later_and_return() {
    crate::assert_ok!("
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, owner: given Data, data: ref[owner] Data) -> ref[owner] Data {
                  let d: ref[owner] Data = data.move;
                  let e: ref[owner] Data = data.move;
                  let f: ref[owner] Data = data.move;
                  d.move;
                }
            }
        ")
}

// Test that we can give from `shared` and go on using it
#[test]
#[allow(non_snake_case)]
fn take_given_and_shared_move_given_then_return_shared() {
    crate::assert_err!("
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, owner: given Data, data: ref[owner] Data) -> ref[owner] Data {
                  let d: ref[owner] Data = data.move;
                  let owner1: given Data = owner.move;
                  d.move;
                }
            }
        ", expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                place_b = owner
                &place_a = owner1

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]])
}

/// Interesting example from [conversation with Isaac][r]. In this example,
/// when `bar` calls `foo`, it takes a *locally leased* copy of `y` -- but since
/// `y` is stored into `x.value`, it escapes, and hence is no longer usable.
///
/// In Dada this is accepted because `leased(y) B R[Int]` can be converted to `B R[Int]`
/// so long as `y` is dead (as long as B is shared/leased).
///
/// [r]: https://gitlab.inf.ethz.ch/public-plf/borrowck-examples/-/blob/db0ece7ab20404935e4cf381471f425b41e6c009/tests/passing/reborrowing-escape-function.md
#[test]
fn escapes_ok() {
    crate::assert_ok!("
          class R[ty T] {
            value: T;
          }

          class Main {
            fn foo[perm A, perm B](given self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              leased(A),
              leased(B),
            {
              ();
            }

            fn bar[perm A, perm B](given self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              leased(A),
              leased(B),
            {
              self.move.foo[A, B](x.move, y.mut);
            }
          }
    ");

    // fn foo<'a, 'b>(x : &'a mut &'b mut i32, y : &'b mut i32) {
    //   () // For example: *x = y;
    // }

    // fn bar<'a, 'b>(u : &'a mut &'b mut i32, v : &'b mut i32) {
    //   foo(u, &mut *v);
    // }

    // fn main() {}
}

/// See `escapes_ok`, but here we use `y` again (and hence get an error).
#[test]
fn escapes_err_use_again() {
    crate::assert_err!("
          class R[ty T] {
            value: T;
          }

          class Main {
            fn foo[perm A, perm B](given self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              leased(A),
              leased(B),
            {
              ();
            }

            fn bar[perm A, perm B](given self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              leased(A),
              leased(B),
            {
              self.move.foo[A, B](x.move, y.mut);
              y.move;
            }
          }
    ", expect_test::expect![[r#"
        the rule "parameter" at (predicates.rs) failed because
          pattern `true` did not match value `false`"#]]);
}

/// See `escapes_ok`, but here we don't know that `B` is leased (and hence get an error).
/// In particular you can't convert e.g. `mut[y] given R[Int]`.
///
/// Equivalent in Rust would be
///
/// ```rust
/// fn foo(x: &mut T, y: T) { }
///
/// fn bar(x: &mut T, y: T) {
///     foo(x, &mut y);
/// }
/// ```
#[test]
fn escapes_err_not_leased() {
    crate::assert_err!("
          class R[ty T] {
            value: T;
          }

          class Main {
            fn foo[perm A, perm B](given self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              leased(A),
            {
              ();
            }

            fn bar[perm A, perm B](given self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              leased(A),
            {
              self.move.foo[A, B](x.move, y.mut);
            }
          }
    ", expect_test::expect![[r#"
        the rule "parameter" at (predicates.rs) failed because
          pattern `true` did not match value `false`

        the rule "parameter" at (predicates.rs) failed because
          pattern `true` did not match value `false`"#]]);
}

/// Check that a `ref[d1, d2]` in parameters prohibits writes to `d1`.
#[test]
fn shared_d1_in_parameters() {
    crate::assert_err!("
          class Pair[ty T] {
            value1: T;
            value2: T;
          }

          class Data { }

          class Main {
            fn main(given self) {
              let d1 = new Data();
              let d2 = new Data();
              let p = new Pair[ref[d1, d2] Data](d1.ref, d2.ref);
              d1 = new Data();
              let _keep_alive = p.move;
            }
          }
    ", expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
            &accessed_place = d1
            &shared_place = d1"#]]);
}

/// Check that a `ref[d1, d2]` in parameters prohibits writes to `d2`.
#[test]
fn shared_d2_in_parameters() {
    crate::assert_err!("
          class Pair[ty T] {
            value1: T;
            value2: T;
          }

          class Data { }

          class Main {
            fn main(given self) {
              let d1 = new Data();
              let d2 = new Data();
              let p = new Pair[ref[d1, d2] Data](d1.ref, d2.ref);
              d2 = new Data();
              let _keep_alive = p.move;
            }
          }
    ", expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
            &accessed_place = d2
            &shared_place = d2"#]]);
}

/// Check that a `mut[d1, d2]` in parameters prohibits reads from `d1`.
#[test]
fn leased_d1_in_parameters() {
    crate::assert_err!("
          class Pair[ty T] {
            value1: T;
            value2: T;
          }

          class Data { }

          class Main {
            fn main(given self) {
              let d1 = new Data();
              let d2 = new Data();
              let p = new Pair[mut[d1, d2] Data](d1.mut, d2.mut);
              d1.ref;
              let _keep_alive = p.move;
            }
          }
    ", expect_test::expect![[r#"
        the rule "lease-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
            &accessed_place = d1
            &leased_place = d1"#]]);
}
