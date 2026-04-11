#[test]
fn struct_is_copy() {
    // A shared class with all-copy fields is itself copy.
    // Giving it twice should work — the source is NOT uninitialized.
    crate::assert_interpret!(
        {
            shared class Pair {
                x: Int;
                y: Int;
            }
            class Main {
                fn main(given self) -> Pair {
                    let p = new Pair(1, 2);
                    let a = p.give;
                    p.give;
                }
            }
        },
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_p = new Pair (1, 2) ;
            Output: Trace:   _1_p = Pair { x: 1, y: 2 }
            Output: Trace:   let _1_a = _1_p . give ;
            Output: Trace:   _1_a = Pair { x: 1, y: 2 }
            Output: Trace:   _1_p . give ;
            Output: Trace: exit Main.main => Pair { x: 1, y: 2 }
            Result: Ok: Pair { x: 1, y: 2 }
            Alloc 0x08: [Int(1), Int(2)]"#]])
    );
}

#[test]
fn class_give_moves() {
    // A regular class is move. Giving it produces an Owned copy.
    // Contrast with struct_is_copy where the source stays usable.
    crate::assert_interpret!(
        {
            class Data {
                x: Int;
            }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    d.give;
                }
            }
        },
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   _1_d . give ;
            Output: Trace: exit Main.main => Data { x: 42 }
            Result: Ok: Data { x: 42 }
            Alloc 0x05: [Int(42)]"#]])
    );
}

// Path flag accumulation — accessing a field through a ref
// object should produce a value with the ref permission.
// The method returns P Inner where P = ref[o], and since
// Inner has a non-copy field (x: Int in a regular class),
// the result carries the ref permission.
#[test]
fn ref_method_field_is_ref() {
    crate::assert_interpret!(
        {
            class Inner {
                x: Int;
            }
            class Outer {
                inner: Inner;

                fn get_inner[perm P](P self) -> P Inner {
                    self.inner.give;
                }
            }
            class Main {
                fn main(given self) -> Int {
                    let o = new Outer(new Inner(99));
                    let i = o.ref.get_inner[ref[o]]();
                    print(i.give);
                    o.give;
                    0;
                }
            }
        },
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_o = new Outer (new Inner (99)) ;
            Output: Trace:   _1_o = Outer { inner: Inner { x: 99 } }
            Output: Trace:   let _1_i = _1_o . ref . get_inner [ref [_1_o]] () ;
            Output: Trace:   enter Outer.get_inner
            Output: Trace:     _2_self . inner . give ;
            Output: Trace:   exit Outer.get_inner => ref [_1_o] Inner { x: 99 }
            Output: Trace:   _1_i = ref [_1_o] Inner { x: 99 }
            Output: Trace:   print(_1_i . give) ;
            Output: ----->   ref [_1_o] Inner { x: 99 }
            Output: Trace:   _1_o . give ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x0d: [Int(0)]"#]])
    );
}
