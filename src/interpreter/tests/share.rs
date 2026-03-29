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
