#[test]
fn struct_is_copy() {
    // A struct (shared class) with all-copy fields is itself copy.
    // Giving it twice should work — the source is NOT uninitialized.
    crate::assert_interpret!(
        {
            struct class Pair {
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
        expect_test::expect![[r#"
            Result: Pair { x: 1, y: 2 }
            Alloc 0x08: [Int(1), Int(2)]"#]]
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
        expect_test::expect![[r#"
            Result: Data { flag: Given, x: 42 }
            Alloc 0x05: [Flags(Given), Int(42)]"#]]
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
        expect_test::expect![[r#"
            Output: ref [o] Inner { flag: Borrowed, x: 99 }
            Result: 0
            Alloc 0x0d: [Int(0)]"#]]
    );
}
