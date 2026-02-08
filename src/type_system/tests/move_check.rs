use formality_core::test;

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn give_same_field_twice() {
    crate::assert_err!("
        class Data { }

        class Foo {
            i: Data;
        }

        class Main {
            fn main(my self) -> Int {
                let foo = new Foo(new Data());
                foo.i.move;
                foo.i.move;
            }
        }
    ", expect_test::expect![[r#"
        the rule "parameter" at (predicates.rs) failed because
          pattern `true` did not match value `false`

        the rule "move" at (expressions.rs) failed because
          condition evaluted to false: `!live_after.is_live(&place)`
            live_after = LivePlaces { accessed: {foo . i}, traversed: {} }
            &place = foo . i"#]])
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn give_field_of_moved_variable() {
    crate::assert_err!("
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn main(my self) -> Int {
                    let foo = new Foo(new Data());
                    foo.move;
                    foo.i.move;
                }
            }
        ", expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "move" at (expressions.rs) failed because
              condition evaluted to false: `!live_after.is_live(&place)`
                live_after = LivePlaces { accessed: {foo . i}, traversed: {} }
                &place = foo"#]])
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn give_variable_with_moved_field() {
    crate::assert_err!("
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn main(my self) -> Int {
                    let foo = new Foo(new Data());
                    foo.i.move;
                    foo.move;
                }
            }
        ", expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "move" at (expressions.rs) failed because
              condition evaluted to false: `!live_after.is_live(&place)`
                live_after = LivePlaces { accessed: {foo}, traversed: {} }
                &place = foo . i"#]])
}

/// Check giving a shared value twice (giving a shared value doesn't consume it).
#[test]
#[allow(non_snake_case)]
fn give_shared_value() {
    crate::assert_ok!("
        class Data { }

        class Foo {
            i: Data;
        }

        class Main {
            fn main(my self) {
                let foo = new Foo(new Data());
                let bar = foo.ref;
                bar.move;
                bar.move;
                ();
            }
        }
    ")
}

/// Check giving a leased value twice errors.
#[test]
#[allow(non_snake_case)]
fn give_leased_value() {
    crate::assert_err!("
              class Data { }

              class Foo {
                  i: Data;
              }

              class Main {
                  fn main(my self) {
                      let foo = new Foo(new Data());
                      let bar = foo.mut;
                      bar.move;
                      bar.move;
                      ();
                  }
              }
          ", expect_test::expect![[r#"
              the rule "parameter" at (predicates.rs) failed because
                pattern `true` did not match value `false`

              the rule "move" at (expressions.rs) failed because
                condition evaluted to false: `!live_after.is_live(&place)`
                  live_after = LivePlaces { accessed: {bar}, traversed: {} }
                  &place = bar"#]])
}
