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
    crate::assert_interpret!(
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
        type: error(expect_test::expect![[r#"src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Outer, i: Inner, m: Mid, r: ref [m] Mid}, assumptions: {}, fresh: 1 } }"#]]), interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_i = new Inner (42) ;
            Output: Trace:   _1_i = Inner { x: 42 }
            Output: Trace:   let _1_m = new Mid (_1_i . give) ;
            Output: Trace:   _1_m = Mid { inner: Inner { x: 42 } }
            Output: Trace:   let _1_r = _1_m . ref ;
            Output: Trace:   _1_r = ref [_1_m] Mid { inner: Inner { x: 42 } }
            Output: Trace:   let _1_o = new Outer (_1_r . give) ;
            Output: Trace:   _1_o = Outer { mid: Mid { inner: Inner { x: 42 } } }
            Output: Trace:   _1_o . give . share ;
            Output: Trace: exit Main.main => shared Outer { mid: Mid { inner: Inner { x: 42 } } }
            Result: Ok: shared Outer { mid: Mid { inner: Inner { x: 42 } } }
            Alloc 0x0d: [Int(42)]"#]])
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
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   _1_d . give . share ;
            Output: Trace: exit Main.main => shared Data { x: 42 }
            Result: Ok: shared Data { x: 42 }
            Alloc 0x05: [Int(42)]"#]])
    );
}
