use formality_core::test;

mod borrowck_loan_kills;

/// Check sharing a field from a leased value errs.
#[test]
#[allow(non_snake_case)]
fn share_field_of_leased_value() {
    crate::assert_err!({
                class Data { }

                class Foo {
                    i: Data;
                }

                class Main {
                    fn main(given self) {
                        let foo = new Foo(new Data());
                        let bar = foo.mut;
                        let i = foo.i.ref;
                        bar.give;
                        ();
                    }
                }
            }, expect_test::expect![[r#"
                the rule "lease-mutation" at (accesses.rs) failed because
                  condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
                    accessed_place = foo . i
                    leased_place = foo"#]])
}

/// Check sharing a field from a shared value is ok.
#[test]
#[allow(non_snake_case)]
fn share_field_of_shared_value() {
    crate::assert_ok!({
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn main(given self) {
                    let foo = new Foo(new Data());
                    let bar = foo.ref;
                    let i = foo.i.ref;
                    bar.give;
                    ();
                }
            }
        })
}

/// Check leasing a field from a shared value is not ok.
#[test]
#[allow(non_snake_case)]
fn lease_field_of_shared_value() {
    crate::assert_err!({
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn main(given self) {
                    let foo = new Foo(new Data());
                    let bar = foo.ref;
                    let i = foo.i.mut;
                    bar.give;
                    ();
                }
            }
        }, expect_test::expect![[r#"
            the rule "share-mutation" at (accesses.rs) failed because
              condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
                accessed_place = foo . i
                shared_place = foo"#]])
}

/// Check leasing a field from a shared value is not ok.
#[test]
#[allow(non_snake_case)]
fn ref_then_mut_errors() {
    crate::assert_err!({
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn main(given self) {
                    let foo = new Foo(new Data());
                    let bar = foo.ref;
                    let i = bar.i.mut;
                    ();
                }
            }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { } class Foo { i : Data ; } class Main { fn main (given self) -> () { let foo = new Foo (new Data ()) ; let bar = foo . ref ; let i = bar . i . mut ; () ; } } }`"])
}

/// Check giving a field from a shared value is not ok.
#[test]
#[allow(non_snake_case)]
fn give_field_of_shared_value() {
    crate::assert_err!({
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn main(given self) {
                    let foo = new Foo(new Data());
                    let bar = foo.ref;
                    let i = foo.i.give;
                    bar.give;
                    ();
                }
            }
        }, expect_test::expect![[r#"
            the rule "share-give" at (accesses.rs) failed because
              condition evaluted to false: `place_disjoint_from_or_prefix_of(accessed_place, shared_place)`
                accessed_place = foo . i
                shared_place = foo"#]])
}

/// Check sharing a field from a leased value errs.
#[test]
#[allow(non_snake_case)]
fn share_field_of_leased_value_after_explicit_give() {
    crate::assert_ok!({
                class Data { }

                class Foo {
                    i: Data;
                }

                class Main {
                    fn main(given self) {
                        let foo = new Foo(new Data());
                        let bar = foo.mut;
                        bar.give;
                        let i = foo.i.ref;
                        ();
                    }
                }
            })
}

/// Check that we can permit accessing `foo.i` even though
/// it was leased since `bar` is dead.
#[test]
#[allow(non_snake_case)]
fn share_field_of_leased_value_without_explicit_give() {
    crate::assert_ok!({
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
            })
}

#[test]
fn share_field_of_leased_value_but_lease_variable_is_dead() {
    // Here, the variable `q` is dead, but its restrictions must
    // still be enforced because `r` is live.
    crate::assert_err!({
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
                        r.give;
                        ();
                    }
                }
            }, expect_test::expect![[r#"
                the rule "lease-mutation" at (accesses.rs) failed because
                  condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
                    accessed_place = p . i
                    leased_place = p"#]])
}

#[test]
fn share_field_of_leased_value_but_lease_variable_is_dead_explicit_ty() {
    // Here, the variable `q` is dead, but its restrictions must
    // still be enforced because `r` is live.
    crate::assert_err!({
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
                        r.give;
                        ();
                    }
                }
            }, expect_test::expect![[r#"
                the rule "lease-mutation" at (accesses.rs) failed because
                  condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
                    accessed_place = p . i
                    leased_place = p"#]])
}

/// Test where we expect data leased from self and then try to use self.
/// Error.
#[test]
#[allow(non_snake_case)]
fn pair_method__leased_self__use_self() {
    crate::assert_err!({
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, data: mut[self] Data) {
                  self.a.mut;
                  data.give;
                  ();
                }
            }
        }, expect_test::expect![[r#"
            the rule "lease-mutation" at (accesses.rs) failed because
              condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
                accessed_place = self . a
                leased_place = self"#]])
}

/// Test that we cannot mutate fields of a shared class.
#[test]
#[allow(non_snake_case)]
fn mutate_field_of_shared_pair() {
    crate::assert_err!({
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, data: given Data) {
                  let me = self.ref;
                  me.a = data.give;
                  ();
                }
            }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { } class Pair { a : Data ; b : Data ; fn method (given self data : given Data) -> () { let me = self . ref ; me . a = data . give ; () ; } } }`"])
}

/// Test that we cannot mutate fields of a shared class.
#[test]
#[allow(non_snake_case)]
fn mutate_field_of_our_pair() {
    crate::assert_err!({
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, pair: shared Pair, data: given Data) {
                  pair.a = data.give;
                  ();
                }
            }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { } class Pair { a : Data ; b : Data ; fn method (given self pair : shared Pair, data : given Data) -> () { pair . a = data . give ; () ; } } }`"])
}

/// Test that we can mutate fields of a leased class.
#[test]
#[allow(non_snake_case)]
fn mutate_field_of_leased_pair() {
    crate::assert_ok!({
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, data: given Data) {
                  let me = self.mut;
                  me.a = data.give;
                  ();
                }
            }
        })
}

// Test that we can give from `shared` and go on using it
#[test]
#[allow(non_snake_case)]
fn give_our_then_use_later_and_return() {
    crate::assert_ok!({
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, data: shared Data) -> shared Data {
                  let d: shared Data = data.give;
                  let e: shared Data = data.give;
                  let f: shared Data = data.give;
                  d.give;
                }
            }
        })
}

// Test that we can give from `shared` and go on using it
#[test]
#[allow(non_snake_case)]
fn give_shared_then_use_later_and_return() {
    crate::assert_ok!({
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, owner: given Data, data: ref[owner] Data) -> ref[owner] Data {
                  let d: ref[owner] Data = data.give;
                  let e: ref[owner] Data = data.give;
                  let f: ref[owner] Data = data.give;
                  d.give;
                }
            }
        })
}

// Test that we can give from `shared` and go on using it
#[test]
#[allow(non_snake_case)]
fn take_given_and_shared_move_given_then_return_shared() {
    crate::assert_err!({
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, owner: given Data, data: ref[owner] Data) -> ref[owner] Data {
                  let d: ref[owner] Data = data.give;
                  let owner1: given Data = owner.give;
                  d.give;
                }
            }
        }, expect_test::expect![[r#"
            the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(place_a)`
                place_b = owner
                place_a = owner1"#]])
}

/// Interesting example from [conversation with Isaac][r]. In this example,
/// when `bar` calls `foo`, it takes a *locally leased* copy of `y` -- but since
/// `y` is stored into `x.value`, it escapes, and hence is no longer usable.
///
/// In Dada this is accepted because `mut(y) B R[Int]` can be converted to `B R[Int]`
/// so long as `y` is dead (as long as B is shared/leased).
///
/// [r]: https://gitlab.inf.ethz.ch/public-plf/borrowck-examples/-/blob/db0ece7ab20404935e4cf381471f425b41e6c009/tests/passing/reborrowing-escape-function.md
#[test]
fn escapes_ok() {
    crate::assert_ok!({
          class R[ty T] {
            value: T;
          }

          class Main {
            fn foo[perm A, perm B](given self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              A is mut,
              B is mut,
            {
              ();
            }

            fn bar[perm A, perm B](given self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              A is mut,
              B is mut,
            {
              self.give.foo[A, B](x.give, y.mut);
            }
          }
    });

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
    crate::assert_err!({
          class R[ty T] {
            value: T;
          }

          class Main {
            fn foo[perm A, perm B](given self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              A is mut,
              B is mut,
            {
              ();
            }

            fn bar[perm A, perm B](given self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              A is mut,
              B is mut,
            {
              self.give.foo[A, B](x.give, y.mut);
              y.give;
            }
          }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class R [ty] { value : ^ty0_0 ; } class Main { fn foo [perm, perm] (given self x : ^perm0_0 R[^perm0_1 R[Int]], y : ^perm0_1 R[Int]) -> () where ^perm0_0 is mut, ^perm0_1 is mut { () ; } fn bar [perm, perm] (given self x : ^perm0_0 R[^perm0_1 R[Int]], y : ^perm0_1 R[Int]) -> () where ^perm0_0 is mut, ^perm0_1 is mut { self . give . foo [^perm0_0, ^perm0_1] (x . give, y . mut) ; y . give ; } } }`"]);
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
    crate::assert_err!({
          class R[ty T] {
            value: T;
          }

          class Main {
            fn foo[perm A, perm B](given self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              A is mut,
            {
              ();
            }

            fn bar[perm A, perm B](given self, x: A R[B R[Int]], y: B R[Int]) -> ()
            where
              A is mut,
            {
              self.give.foo[A, B](x.give, y.mut);
            }
          }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class R [ty] { value : ^ty0_0 ; } class Main { fn foo [perm, perm] (given self x : ^perm0_0 R[^perm0_1 R[Int]], y : ^perm0_1 R[Int]) -> () where ^perm0_0 is mut { () ; } fn bar [perm, perm] (given self x : ^perm0_0 R[^perm0_1 R[Int]], y : ^perm0_1 R[Int]) -> () where ^perm0_0 is mut { self . give . foo [^perm0_0, ^perm0_1] (x . give, y . mut) ; } } }`"]);
}

/// Check that a `ref[d1, d2]` in parameters prohibits writes to `d1`.
#[test]
fn shared_d1_in_parameters() {
    crate::assert_err!({
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
              let _keep_alive = p.give;
            }
          }
    }, expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
            accessed_place = d1
            shared_place = d1"#]]);
}

/// Check that a `ref[d1, d2]` in parameters prohibits writes to `d2`.
#[test]
fn shared_d2_in_parameters() {
    crate::assert_err!({
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
              let _keep_alive = p.give;
            }
          }
    }, expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
            accessed_place = d2
            shared_place = d2"#]]);
}

/// Check that a `mut[d1, d2]` in parameters prohibits reads from `d1`.
#[test]
fn leased_d1_in_parameters() {
    crate::assert_err!({
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
              let _keep_alive = p.give;
            }
          }
    }, expect_test::expect![[r#"
        the rule "lease-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
            accessed_place = d1
            leased_place = d1"#]]);
}

/// `ref` of a `mut` should NOT satisfy `P is mut`.
/// A ref strips mutability — `ref[d] mut[a] Data` is not mut.
///
/// FIXME: this currently PASSES (type-checks successfully) because
/// `prove_is_mut` uses OR composition, so the inner `mut` satisfies
/// the predicate even though the outer `ref` should strip it.
/// The compose rule needs fixing: for Mut, one side must be Move
/// and the other Mut (not just "either side is Mut").
/// Once fixed, change this back to `assert_err!`.
#[test]
#[allow(non_snake_case)]
fn ref_of_mut_is_not_mut() {
    // FIXME: should be assert_err! — see comment above
    crate::assert_ok!({
        class Data { }

        class Foo {
            d: Data;

            fn needs_mut[perm P](P self) -> ()
            where P is mut,
            {
                ();
            }
        }

        class Main {
            fn main(given self) {
                let foo = new Foo(new Data());
                let m = foo.mut;
                m.ref.needs_mut[ref[m] mut[foo]]();
            }
        }
    });
}
