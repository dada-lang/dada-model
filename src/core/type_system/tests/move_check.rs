use formality_core::test;

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn give_same_field_twice() {
    crate::assert_err!({
        struct Data { }

        struct Foo {
            i: Data;
        }

        struct Main {
            fn main(given self) -> Int {
                let foo = new Foo(new Data());
                foo.i^;
                foo.i^;
            }
        }
    }, expect_test::expect![[r#"
        the rule "give" at (expressions.rs) failed because
          condition evaluted to false: `!live_after.is_live(place)`
            live_after = LivePlaces { accessed: {foo . i}, traversed: {} }
            place = foo . i"#]])
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn give_field_of_moved_variable() {
    crate::assert_err!({
            struct Data { }

            struct Foo {
                i: Data;
            }

            struct Main {
                fn main(given self) -> Int {
                    let foo = new Foo(new Data());
                    foo^;
                    foo.i^;
                }
            }
        }, expect_test::expect![[r#"
            the rule "give" at (expressions.rs) failed because
              condition evaluted to false: `!live_after.is_live(place)`
                live_after = LivePlaces { accessed: {foo . i}, traversed: {} }
                place = foo"#]])
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn give_variable_with_moved_field() {
    crate::assert_err!({
            struct Data { }

            struct Foo {
                i: Data;
            }

            struct Main {
                fn main(given self) -> Int {
                    let foo = new Foo(new Data());
                    foo.i^;
                    foo^;
                }
            }
        }, expect_test::expect![[r#"
            the rule "give" at (expressions.rs) failed because
              condition evaluted to false: `!live_after.is_live(place)`
                live_after = LivePlaces { accessed: {foo}, traversed: {} }
                place = foo . i"#]])
}

/// Check giving a shared value twice (giving a shared value doesn't consume it).
#[test]
#[allow(non_snake_case)]
fn give_ref_twice() {
    crate::assert_ok!({
        struct Data { }

        struct Foo {
            i: Data;
        }

        struct Main {
            fn main(given self) {
                let foo = new Foo(new Data());
                let bar = foo.share;
                bar^;
                bar^;
                ();
            }
        }
    })
}

/// Check giving a leased value twice errors.
#[test]
#[allow(non_snake_case)]
fn give_leased_value() {
    crate::assert_err!({
              struct Data { }

              struct Foo {
                  i: Data;
              }

              struct Main {
                  fn main(given self) {
                      let foo = new Foo(new Data());
                      let bar = foo!;
                      bar^;
                      bar^;
                      ();
                  }
              }
          }, expect_test::expect![[r#"
              the rule "give" at (expressions.rs) failed because
                condition evaluted to false: `!live_after.is_live(place)`
                  live_after = LivePlaces { accessed: {bar}, traversed: {} }
                  place = bar"#]])
}
