/// Sharing an outer class whose field has Flags::Borrowed should leave that
/// field untouched (no-op, per spec). Without the fix, `convert_to_shared`
/// recurses past the Borrowed field into its sub-fields and incorrectly
/// flips their Given flags to Shared.
#[test]
fn share_skips_borrowed_subfield() {
    // Outer { mid: Mid { inner: Inner { x: Int } } }
    // After `m.ref`, Mid's flags word is Borrowed.
    // Constructing Outer from that borrowed Mid buries Flags::Borrowed inside Outer.
    // Sharing Outer should flip Outer→Shared but leave Mid's content unchanged.
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; }
            class Mid { inner: Inner; }
            class Outer { mid: Mid; }
            class Main {
                fn main(given self) -> shared Outer {
                    let i = new Inner(42);
                    let m = new Mid(i.give);
                    let r = m.ref;
                    let o = new Outer(r.give);
                    o.give.share;
                }
            }
        },
        expect_test::expect![[r#"
            Result: Outer { flag: Shared, mid: Mid { flag: Borrowed, inner: Inner { flag: Given, x: 42 } } }
            Alloc 0x0d: [Flags(Shared), Flags(Borrowed), Flags(Given), Int(42)]"#]]
    );
}

#[test]
fn share_class() {
    // Using .share on a regular class flips its flag to Shared.
    // Return type is shared Data since .share produces shared permission.
    crate::assert_interpret!(
        {
            class Data {
                x: Int;
            }
            class Main {
                fn main(given self) -> shared Data {
                    let d = new Data(42);
                    d.give.share;
                }
            }
        },
        expect_test::expect![[r#"
            Result: Data { flag: Shared, x: 42 }
            Alloc 0x05: [Flags(Shared), Int(42)]"#]]
    );
}
