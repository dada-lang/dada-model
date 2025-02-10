use formality_core::test;
use formality_core::test_util::ResultTestExt;

use crate::{dada_lang::term, type_system::check_program};

#[test]
fn give_int_value_twice() {
    check_program(&term(
        "
                class Foo {
                    i: Int;
                }

                class Main {
                    fn main(my self, foo: my Foo) {
                        foo.i.give;
                        foo.i.give;
                        ();
                    }
                }
            ",
    ))
    .assert_ok(expect_test::expect![["()"]])
}
