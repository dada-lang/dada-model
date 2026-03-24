use formality_core::test;

/// A class with a drop body that accesses self via ref should type-check.
#[test]
fn drop_body_prints_field() {
    crate::assert_ok!({
        class Foo {
            x: Int;

            drop {
                print(self.x.ref);
            }
        }
    });
}

/// A given class with a drop body gets `self: given Class` — can move fields.
#[test]
fn given_class_drop_body_can_move() {
    crate::assert_ok!({
        given class Foo {
            x: Int;

            drop {
                let v = self.x.give;
            }
        }
    });
}

/// A default (share) class drop body gets `self: P Class` where `P is ref`.
/// Moving a field out of `ref self` should fail.
#[test]
fn share_class_drop_body_cannot_move_field() {
    crate::assert_err!({
        class Foo {
            x: Int;

            drop {
                let v = self.x.give;
                self.x = 42;
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Foo { x : Int ; drop { let v = self . x . give ; self . x = 42 ; } } }`"]);
}

/// A shared class drop body gets `self: P Class` where `P is ref`.
#[test]
fn shared_class_drop_body_ref_self() {
    crate::assert_ok!({
        shared class Pt {
            x: Int;
            y: Int;

            drop {
                print(self.x.ref);
            }
        }
    });
}

/// An empty drop body should be fine.
#[test]
fn empty_drop_body() {
    crate::assert_ok!({
        class Foo {
            x: Int;

            drop {}
        }
    });
}

/// Drop body can access class-level generic type parameters.
#[test]
fn drop_body_accesses_class_generics() {
    let input = "class Wrapper[ty T] { len: Int; drop { print(self.len.ref); } }";
    crate::assert_ok!(input);
}

/// A share class drop body cannot get mut access to fields.
#[test]
fn share_class_drop_body_cannot_mut_field() {
    crate::assert_err!({
        class Foo {
            x: Int;

            drop {
                let v = self.x.mut;
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Foo { x : Int ; drop { let v = self . x . mut ; } } }`"]);
}

/// Array index projection does not type-check as a place expression.
/// Array elements are accessed only through intrinsics.
#[test]
fn array_index_not_accessible_place() {
    crate::assert_err!({
        class TheClass {
            fn go(given self, a: given Array[Int]) -> () {
                let x = a[0].give;
            }
        }
    }, expect_test::expect![[r#"
        the rule "give place" at (expressions.rs) failed because
          index projections are not supported in places"#]]);
}
