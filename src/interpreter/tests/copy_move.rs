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
        return "Pair { flag: Shared, x: 1, y: 2 }"
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
        return "Data { flag: Owned, x: 42 }"
    );
}

// TODO: path flag accumulation — accessing a field through a ref/shared
// object should produce a value with the effective flag (Ref or Shared).
// Currently blocked on type checker not accepting `ref self` methods
// (ref without places) or `.share` field access patterns.
// Need help writing programs the type checker accepts for these cases.
#[test]
#[ignore]
fn ref_method_field_is_ref() {
    crate::assert_interpret!(
        {
            class Inner {
                x: Int;
            }
            class Outer {
                inner: Inner;

                fn get_inner(ref self) -> Inner {
                    self.inner.give;
                }
            }
            class Main {
                fn main(given self) -> Inner {
                    let o = new Outer(new Inner(99));
                    o.ref.get_inner();
                }
            }
        },
        return "Inner { flag: Ref, x: 99 }"
    );
}
