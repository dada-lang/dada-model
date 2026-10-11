use formality_core::test;

/// Check we are able to type check an empty method.
#[test]
fn empty_method() {
    crate::assert_ok!({
    class TheClass {
        fn empty_method(^ self) {}
    }
    });
}

/// Check that empty blocks return unit (and that is not assignable to Int)
#[test]
fn bad_int_return_value() {
    crate::assert_err!({
            class TheClass {
                fn empty_method(^ self) -> Int {}
            }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class TheClass { fn empty_method (^ self) -> Int { } } }`"])
}

/// Check that empty blocks return unit (and that is not assignable to Int)
#[test]
fn bad_int_ascription() {
    crate::assert_err!({
            class TheClass {
                fn empty_method(^ self) {
                    let x: Int = ();
                }
            }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class TheClass { fn empty_method (^ self) -> () { let x : Int = () ; } } }`"])
}

/// Check returning an integer with return type of Int.
#[test]
fn good_int_return_value() {
    crate::assert_ok!({
        class TheClass {
            fn empty_method(^ self) -> Int {
                22;
            }
        }
    });
}

/// Check returning an instance of a class.
#[test]
#[allow(non_snake_case)]
fn return_instance_of_Foo() {
    crate::assert_ok!({
        class Foo { }

        class TheClass {
            fn empty_method(^ self) -> Foo {
                new Foo();
            }
        }
    });
}

/// Check returning an instance of a class.
#[test]
#[allow(non_snake_case)]
fn return_from_variable() {
    crate::assert_ok!({
        class Foo { }

        class TheClass {
            fn empty_method(^ self) -> Foo {
                let foo = new Foo();
                foo^;
            }
        }
    });
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn return_shared_not_give() {
    crate::assert_err!({
            class Foo { }
    
            class TheClass {
                fn empty_method(^ self) -> Foo {
                    let foo = new Foo();
                    foo.share;
                }
            }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Foo { } class TheClass { fn empty_method (^ self) -> Foo { let foo = new Foo () ; foo . share ; } } }`"])
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn return_int_field_from_class_with_int_field() {
    crate::assert_ok!({
        class Foo {
            i: Int;
        }

        class TheClass {
            fn empty_method(^ self) -> Int {
                let foo = new Foo(22);
                foo.i^;
            }
        }
    });
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn return_modified_int_field_from_class_with_int_field() {
    crate::assert_ok!({
        class Foo {
            i: Int;
        }

        class TheClass {
            fn empty_method(^ self) -> Int {
                let foo = new Foo(22);
                foo.i = foo.i^ + 1;
                foo.i^;
            }
        }
    });
}
