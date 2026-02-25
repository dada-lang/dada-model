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
