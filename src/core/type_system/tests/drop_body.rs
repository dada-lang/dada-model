use formality_core::test;

/// A class with a drop body that accesses self via place sharing should type-check.
#[test]
fn drop_body_prints_field() {
    crate::assert_ok!({
        class Foo {
            x: Int;

            drop {
                print(self.x.share);
            }
        }
    });
}

/// A given class with a drop body gets `self: ^ Class` — can move fields.
#[test]
fn given_class_drop_body_can_move() {
    crate::assert_ok!({
        class Foo {
            x: Int;

            drop {
                let v = self.x^;
            }
        }
    });
}

/// Structs reject nonempty destructor bodies.
#[test]
fn share_class_drop_body_cannot_move_field() {
    crate::assert_err!({
        struct Foo {
            x: Int;

            drop {
                let v = self.x^;
                self.x = 42;
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Foo { x : Int ; drop { let v = self . x ^ ; self . x = 42 ; } } }`"]);
}

/// Shared structs also reject nonempty destructor bodies.
#[test]
fn shared_struct_cannot_have_destructor() {
    crate::assert_err!({
        shared struct Pt {
            x: Int;
            y: Int;

            drop {
                print(self.x.share);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: shared struct Pt { x : Int ; y : Int ; drop { print(self . x . share) ; } } }`"]);
}

/// An empty drop body should be fine.
#[test]
fn empty_drop_body() {
    crate::assert_ok!({
        struct Foo {
            x: Int;

            drop {}
        }
    });
}

/// Drop body can access class-level generic type parameters.
#[test]
fn drop_body_accesses_class_generics() {
    let input = "class Wrapper[ty T] { len: Int; drop { print(self.len.share); } }";
    crate::assert_ok!(input);
}

/// Even a destructor that only leases a field is forbidden on a struct.
#[test]
fn share_class_drop_body_cannot_mut_field() {
    crate::assert_err!({
        struct Foo {
            x: Int;

            drop {
                let v = self.x!;
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Foo { x : Int ; drop { let v = self . x ! ; } } }`"]);
}

/// Array index projection does not type-check as a place expression.
/// Array elements are accessed only through intrinsics.
#[test]
fn array_index_not_accessible_place() {
    crate::assert_err!({
        struct TheClass {
            fn go(^ self, a: ^ Array[Int]) -> () {
                let x = a[0]^;
            }
        }
    }, expect_test::expect![[r#"
        the rule "give place" at (expressions.rs) failed because
          index projections are not supported in places"#]]);
}
