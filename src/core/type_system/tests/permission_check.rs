use formality_core::test;

mod borrowck_loan_kills;

/// Check sharing a field from a leased value errs.
#[test]
#[allow(non_snake_case)]
fn share_field_of_leased_value() {
    crate::assert_err!({
                struct Data { }

                struct Foo {
                    i: Data;
                }

                struct Main {
                    fn main(given self) {
                        let foo = new Foo(new Data());
                        let bar = foo!;
                        let i = foo.i.share;
                        bar^;
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
        struct Data { }

        struct Foo {
            i: Data;
        }

        struct Main {
            fn main(given self) {
                let foo = new Foo(new Data());
                let bar = foo.share;
                let i = foo.i.share;
                bar^;
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
            struct Data { }

            struct Foo {
                i: Data;
            }

            struct Main {
                fn main(given self) {
                    let foo = new Foo(new Data());
                    let bar = foo.share;
                    let i = foo.i!;
                    bar^;
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
            struct Data { }

            struct Foo {
                i: Data;
            }

            struct Main {
                fn main(given self) {
                    let foo = new Foo(new Data());
                    let bar = foo.share;
                    let i = bar.i!;
                    ();
                }
            }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Foo { i : Data ; } struct Main { fn main (given self) -> () { let foo = new Foo (new Data ()) ; let bar = foo . share ; let i = bar . i ! ; () ; } } }`"])
}

/// Check giving a field from a shared value is not ok.
#[test]
#[allow(non_snake_case)]
fn give_field_of_shared_value() {
    crate::assert_err!({
            struct Data { }

            struct Foo {
                i: Data;
            }

            struct Main {
                fn main(given self) {
                    let foo = new Foo(new Data());
                    let bar = foo.share;
                    let i = foo.i^;
                    bar^;
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
        struct Data { }

        struct Foo {
            i: Data;
        }

        struct Main {
            fn main(given self) {
                let foo = new Foo(new Data());
                let bar = foo!;
                bar^;
                let i = foo.i.share;
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
        struct Data { }

        struct Foo {
            i: Data;
        }

        struct Main {
            fn main(given self) {
                let foo = new Foo(new Data());
                let bar = foo!;
                let i = foo.i.share;
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
                struct Data { }

                struct Foo {
                    i: Data;
                }

                struct Main {
                    fn main(given self) {
                        let p = new Foo(new Data());
                        let q = p!;
                        let r = q.share;
                        let i = p.i.share;
                        r^;
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
                struct Data { }

                struct Foo {
                    i: Data;
                }

                struct Main {
                    fn main(given self) {
                        let p: given Foo = new Foo(new Data());
                        let q: ![p] Foo = p!;
                        let r: shared[q] Foo = q.share;
                        let i: shared[p.i] Data = p.i.share;
                        r^;
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
            struct Data {}

            struct Pair {
                a: Data;
                b: Data;

                fn method(given self, data: ![self] Data) {
                  self.a!;
                  data^;
                  ();
                }
            }
        }, expect_test::expect![[r#"
            the rule "lease-mutation" at (accesses.rs) failed because
              condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
                accessed_place = self . a
                leased_place = self"#]])
}

/// Test that we cannot mutate fields of a shared struct.
#[test]
#[allow(non_snake_case)]
fn mutate_field_of_shared_pair() {
    crate::assert_err!({
            struct Data {}

            struct Pair {
                a: Data;
                b: Data;

                fn method(given self, data: given Data) {
                  let me = self.share;
                  me.a = data^;
                  ();
                }
            }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Pair { a : Data ; b : Data ; fn method (given self data : given Data) -> () { let me = self . share ; me . a = data ^ ; () ; } } }`"])
}

/// Test that we cannot mutate fields of a shared struct.
#[test]
#[allow(non_snake_case)]
fn mutate_field_of_our_pair() {
    crate::assert_err!({
            struct Data {}

            struct Pair {
                a: Data;
                b: Data;

                fn method(given self, pair: shared Pair, data: given Data) {
                  pair.a = data^;
                  ();
                }
            }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Pair { a : Data ; b : Data ; fn method (given self pair : shared Pair, data : given Data) -> () { pair . a = data ^ ; () ; } } }`"])
}

/// Test that we can mutate fields of a leased class.
#[test]
#[allow(non_snake_case)]
fn mutate_field_of_leased_pair() {
    crate::assert_ok!({
        struct Data {}

        struct Pair {
            a: Data;
            b: Data;

            fn method(given self, data: given Data) {
              let me = self!;
              me.a = data^;
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
        struct Data {}

        struct Pair {
            a: Data;
            b: Data;

            fn method(given self, data: shared Data) -> shared Data {
              let d: shared Data = data^;
              let e: shared Data = data^;
              let f: shared Data = data^;
              d^;
            }
        }
    })
}

// Test that we can give from `shared` and go on using it
#[test]
#[allow(non_snake_case)]
fn give_shared_then_use_later_and_return() {
    crate::assert_ok!({
        struct Data {}

        struct Pair {
            a: Data;
            b: Data;

            fn method(given self, owner: given Data, data: shared[owner] Data) -> shared[owner] Data {
              let d: shared[owner] Data = data^;
              let e: shared[owner] Data = data^;
              let f: shared[owner] Data = data^;
              d^;
            }
        }
    })
}

// Test that we can give from `shared` and go on using it
#[test]
#[allow(non_snake_case)]
fn take_given_and_shared_move_given_then_return_shared() {
    crate::assert_err!({
            struct Data {}

            struct Pair {
                a: Data;
                b: Data;

                fn method(given self, owner: given Data, data: shared[owner] Data) -> shared[owner] Data {
                  let d: shared[owner] Data = data^;
                  let owner1: given Data = owner^;
                  d^;
                }
            }
        }, expect_test::expect![[r#"
            the rule "(shared[place]::P) vs (shared[place]::P)" at (redperms.rs) failed because
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
          struct R[ty T] {
            value: T;
          }

          struct Main {
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
              self^.foo[A, B](x^, y!);
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
          struct R[ty T] {
            value: T;
          }

          struct Main {
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
              self^.foo[A, B](x^, y!);
              y^;
            }
          }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct R [ty] { value : ^ty0_0 ; } struct Main { fn foo [perm, perm] (given self x : ^perm0_0 R[^perm0_1 R[Int]], y : ^perm0_1 R[Int]) -> () where ^perm0_0 is mut, ^perm0_1 is mut { () ; } fn bar [perm, perm] (given self x : ^perm0_0 R[^perm0_1 R[Int]], y : ^perm0_1 R[Int]) -> () where ^perm0_0 is mut, ^perm0_1 is mut { self ^ . foo [^perm0_0, ^perm0_1] (x ^, y !) ; y ^ ; } } }`"]);
}

/// See `escapes_ok`, but here we don't know that `B` is leased (and hence get an error).
/// In particular you can't convert e.g. `![y] ^ R[Int]`.
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
          struct R[ty T] {
            value: T;
          }

          struct Main {
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
              self^.foo[A, B](x^, y!);
            }
          }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct R [ty] { value : ^ty0_0 ; } struct Main { fn foo [perm, perm] (given self x : ^perm0_0 R[^perm0_1 R[Int]], y : ^perm0_1 R[Int]) -> () where ^perm0_0 is mut { () ; } fn bar [perm, perm] (given self x : ^perm0_0 R[^perm0_1 R[Int]], y : ^perm0_1 R[Int]) -> () where ^perm0_0 is mut { self ^ . foo [^perm0_0, ^perm0_1] (x ^, y !) ; } } }`"]);
}

/// Check that a `shared[d1, d2]` in parameters prohibits writes to `d1`.
#[test]
fn shared_d1_in_parameters() {
    crate::assert_err!({
          struct Pair[ty T] {
            value1: T;
            value2: T;
          }

          struct Data { }

          struct Main {
            fn main(given self) {
              let d1 = new Data();
              let d2 = new Data();
              let p = new Pair[shared[d1, d2] Data](d1.share, d2.share);
              d1 = new Data();
              let _keep_alive = p^;
            }
          }
    }, expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
            accessed_place = d1
            shared_place = d1"#]]);
}

/// Check that a `shared[d1, d2]` in parameters prohibits writes to `d2`.
#[test]
fn shared_d2_in_parameters() {
    crate::assert_err!({
          struct Pair[ty T] {
            value1: T;
            value2: T;
          }

          struct Data { }

          struct Main {
            fn main(given self) {
              let d1 = new Data();
              let d2 = new Data();
              let p = new Pair[shared[d1, d2] Data](d1.share, d2.share);
              d2 = new Data();
              let _keep_alive = p^;
            }
          }
    }, expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
            accessed_place = d2
            shared_place = d2"#]]);
}

/// Check that a `![d1, d2]` in parameters prohibits reads from `d1`.
#[test]
fn leased_d1_in_parameters() {
    crate::assert_err!({
          struct Pair[ty T] {
            value1: T;
            value2: T;
          }

          struct Data { }

          struct Main {
            fn main(given self) {
              let d1 = new Data();
              let d2 = new Data();
              let p = new Pair[![d1, d2] Data](d1!, d2!);
              d1.share;
              let _keep_alive = p^;
            }
          }
    }, expect_test::expect![[r#"
        the rule "lease-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
            accessed_place = d1
            leased_place = d1"#]]);
}

/// `share` of a `mut` should NOT satisfy `P is mut`.
/// A place sharing strips mutability — `shared[d] ![a] Data` is not mut.
#[test]
#[allow(non_snake_case)]
fn ref_of_mut_is_not_mut() {
    crate::assert_err!({
        struct Data { }

        struct Foo {
            d: Data;

            fn needs_mut[perm P](P self) -> ()
            where P is mut,
            {
                ();
            }
        }

        struct Main {
            fn main(given self) {
                let foo = new Foo(new Data());
                let m = foo!;
                m.share.needs_mut[shared[m] ![foo]]();
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Foo { d : Data ; fn needs_mut [perm] (^perm0_0 self) -> () where ^perm0_0 is mut { () ; } } struct Main { fn main (given self) -> () { let foo = new Foo (new Data ()) ; let m = foo ! ; m . share . needs_mut [shared [m] ! [foo]] () ; } } }`"]);
}
