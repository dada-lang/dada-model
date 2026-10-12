/// Sharing an outer class whose field has Flags::SharedPlace should leave that
/// field untouched (no-op, per spec). Without the fix, `convert_to_shared`
/// recurses past the SharedPlace field into its sub-fields and incorrectly
/// flips their Given flags to Shared.
#[test]
fn share_skips_borrowed_subfield() {
    // Outer { mid: Mid { inner: Inner { x: Int } } }
    // After `m.share`, Mid's flags word is SharedPlace.
    // Constructing Outer from that borrowed Mid buries Flags::SharedPlace inside Outer.
    // Sharing Outer should flip Outer→Shared but leave Mid's content unchanged.
    crate::assert_interpret_only!(
        {
            struct Inner { x: Int; }
            struct Mid { inner: Inner; }
            struct Outer { mid: Mid; }
            struct Main {
                fn main(given self) -> shared Outer {
                    let i = new Inner(42);
                    let m = new Mid(i->);
                    let r = m.share;
                    let o = new Outer(r->);
                    o->.share;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_i = new Inner (42) ;
            Output: Trace:   _1_i = Inner { x: 42 }
            Output: Trace:   let _1_m = new Mid (_1_i ->) ;
            Output: Trace:   _1_m = Mid { inner: Inner { x: 42 } }
            Output: Trace:   let _1_r = _1_m . share ;
            Output: Trace:   _1_r = shared [_1_m] Mid { inner: Inner { x: 42 } }
            Output: Trace:   let _1_o = new Outer (_1_r ->) ;
            Output: Trace:   _1_o = Outer { mid: Mid { inner: Inner { x: 42 } } }
            Output: Trace:   _1_o -> . share ;
            Output: Trace: exit Main.main => shared Outer { mid: Mid { inner: Inner { x: 42 } } }
            Result: Ok: shared Outer { mid: Mid { inner: Inner { x: 42 } } }
            Alloc 0x0d: [Int(42)]"#]]
    );
}

#[test]
fn share_class() {
    // Using .share on a regular class flips its flag to Shared.
    // Return type is shared Data since .share produces shared permission.
    crate::assert_interpret!(
        {
            struct Data {
                x: Int;
            }
            struct Main {
                fn main(given self) -> shared Data {
                    let d = new Data(42);
                    d->.share;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   _1_d -> . share ;
            Output: Trace: exit Main.main => shared Data { x: 42 }
            Result: Ok: shared Data { x: 42 }
            Alloc 0x05: [Int(42)]"#]]
    );
}
