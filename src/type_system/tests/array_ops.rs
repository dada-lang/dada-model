use formality_core::test;

// =============================================================================
// ArrayNew
// =============================================================================

/// array_new[Int](5) should type-check and produce Array[Int]
#[test]
fn array_new_int() {
    crate::assert_ok!({
        class TheClass {
            fn go(given self) -> Array[Int] {
                array_new[Int](5);
            }
        }
    });
}

/// array_new[Data](3) should type-check and produce Array[Data]
#[test]
#[allow(non_snake_case)]
fn array_new_class() {
    crate::assert_ok!({
        class Data {
            x: Int;
        }

        class TheClass {
            fn go(given self) -> Array[Data] {
                array_new[Data](3);
            }
        }
    });
}

/// array_new requires an Int length argument — passing a class should fail
#[test]
fn array_new_bad_length_type() {
    crate::assert_err!({
        class Data {
            x: Int;
        }

        class TheClass {
            fn go(given self) -> Array[Int] {
                let d = new Data(1);
                array_new[Int](d.give);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { x : Int ; } class TheClass { fn go (given self) -> Array[Int] { let d = new Data (1) ; array_new [Int](d . give) ; } } }`"]);
}

/// array_new with two type parameters should fail
#[test]
fn array_new_two_type_params() {
    crate::assert_err!({
        class Data {
            x: Int;
        }

        class TheClass {
            fn go(given self) -> () {
                array_new[Int, Data](5);
            }
        }
    }, expect_test::expect![[r#"
        the rule "array_new" at (expressions.rs) failed because
          Array requires exactly one type parameter, got [Int, Data]"#]]);
}

/// array_new with a perm parameter instead of a type should fail
#[test]
fn array_new_perm_param() {
    crate::assert_err!({
        class TheClass {
            fn go(given self) -> () {
                array_new[shared](5);
            }
        }
    }, expect_test::expect![[r#"
        the rule "array_new" at (expressions.rs) failed because
          Array requires exactly one type parameter, got [shared]"#]]);
}

// =============================================================================
// ArrayCapacity
// =============================================================================

/// array_capacity on a given array should work
#[test]
fn array_capacity_given() {
    crate::assert_ok!({
        class TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                array_capacity[Int](a.give);
            }
        }
    });
}

/// array_capacity on a shared array should work
#[test]
fn array_capacity_shared() {
    crate::assert_ok!({
        class TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                let b = a.give.share;
                array_capacity[Int](b.give);
            }
        }
    });
}

/// array_capacity on a ref (borrowed) array should work
#[test]
fn array_capacity_ref() {
    crate::assert_ok!({
        class TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                array_capacity[Int](a.ref);
            }
        }
    });
}

/// array_capacity on a mut array should work
#[test]
fn array_capacity_mut() {
    crate::assert_ok!({
        class TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                array_capacity[Int](a.mut);
            }
        }
    });
}

/// array_capacity with wrong type parameter should fail
#[test]
fn array_capacity_wrong_type_param() {
    crate::assert_err!({
        class Data {
            x: Int;
        }

        class TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                array_capacity[Data](a.give);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { x : Int ; } class TheClass { fn go (given self) -> Int { let a = array_new [Int](5) ; array_capacity [Data](a . give) ; } } }`"]);
}

/// array_capacity on a non-array should fail
#[test]
fn array_capacity_not_an_array() {
    crate::assert_err!({
        class TheClass {
            fn go(given self) -> Int {
                array_capacity[Int](22);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class TheClass { fn go (given self) -> Int { array_capacity [Int](22) ; } } }`"]);
}

// =============================================================================
// ArrayInitialize
// =============================================================================

/// array_initialize on a given array with Int elements
#[test]
fn array_initialize_given_int() {
    crate::assert_ok!({
        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_initialize[Int](a.mut, 0, 42);
            }
        }
    });
}

/// array_initialize on a given array with class elements
#[test]
#[allow(non_snake_case)]
fn array_initialize_given_class() {
    crate::assert_ok!({
        class Data {
            x: Int;
        }

        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Data](3);
                let d = new Data(10);
                array_initialize[Data](a.mut, 0, d.give);
            }
        }
    });
}

/// array_initialize on a shared array should work
#[test]
fn array_initialize_shared() {
    // array_initialize requires mut; shared array's mut lease isn't truly mutable
    crate::assert_err!({
        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                let b = a.give.share;
                array_initialize[Int](b.mut, 0, 42);
            }
        }
    }, expect_test::expect![[r#"
        the rule "compose rhs-copy" at (predicates.rs) failed because
          pattern `true` did not match value `false`

        the rule "isnt known to be copy" at (predicates.rs) failed because
          pattern `false` did not match value `true`"#]]);
}

/// array_initialize on a ref array should fail — requires mut
#[test]
fn array_initialize_ref() {
    crate::assert_err!({
        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_initialize[Int](a.ref, 0, 42);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class TheClass { fn go (given self) -> () { let a = array_new [Int](5) ; array_initialize [Int](a . ref , 0 , 42) ; } } }`"]);
}

/// FIXME: this should fail — ref should strip mutability, but currently
/// prove_is_mut succeeds on ref[array_mut] where array_mut: mut[a] Array[Int].
/// Needs investigation into how RefFrom/Compose propagates the Mut predicate.
#[test]
fn array_initialize_ref_of_mut() {
    crate::assert_ok!({
        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                let array_mut = a.mut;
                array_initialize[Int](array_mut.ref, 0, 42);
            }
        }
    });
}

/// array_initialize on a mut array should work
#[test]
fn array_initialize_mut() {
    crate::assert_ok!({
        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_initialize[Int](a.mut, 0, 42);
            }
        }
    });
}

/// array_initialize with wrong type parameter should fail
#[test]
fn array_initialize_wrong_type_param() {
    crate::assert_err!({
        class Data {
            x: Int;
        }

        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_initialize[Data](a.mut, 0, 42);
            }
        }
    }, expect_test::expect![[r#"
        the rule "shared-class copy" at (predicates.rs) failed because
          pattern `true` did not match value `false`

        the rule "mt owned" at (predicates.rs) failed because
          pattern `true` did not match value `false`"#]]);
}

/// array_initialize with wrong value type should fail
#[test]
fn array_initialize_wrong_value_type() {
    crate::assert_err!({
        class Data {
            x: Int;
        }

        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                let d = new Data(10);
                array_initialize[Int](a.mut, 0, d.give);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { x : Int ; } class TheClass { fn go (given self) -> () { let a = array_new [Int](5) ; let d = new Data (10) ; array_initialize [Int](a . mut , 0 , d . give) ; } } }`"]);
}

/// array_initialize on a non-array should fail
#[test]
fn array_initialize_not_an_array() {
    crate::assert_err!({
        class TheClass {
            fn go(given self) -> () {
                array_initialize[Int](22, 0, 42);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class TheClass { fn go (given self) -> () { array_initialize [Int](22 , 0 , 42) ; } } }`"]);
}

/// array_initialize with non-Int index should fail
#[test]
fn array_initialize_bad_index_type() {
    crate::assert_err!({
        class Data {
            x: Int;
        }

        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                let d = new Data(10);
                array_initialize[Int](a.mut, d.give, 42);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { x : Int ; } class TheClass { fn go (given self) -> () { let a = array_new [Int](5) ; let d = new Data (10) ; array_initialize [Int](a . mut , d . give , 42) ; } } }`"]);
}

// =============================================================================
// ArrayGive
// =============================================================================

/// array_give on a given Array[Int] returns Int
#[test]
fn array_give_given_int() {
    crate::assert_ok!({
        class TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                array_initialize[Int](a.mut, 0, 42);
                array_give[Int](a.give, 0);
            }
        }
    });
}

/// array_give on a given Array[Data] returns Data
#[test]
#[allow(non_snake_case)]
fn array_give_given_class() {
    crate::assert_ok!({
        class Data {
            x: Int;
        }

        class TheClass {
            fn go(given self) -> Data {
                let a = array_new[Data](3);
                let d = new Data(10);
                array_initialize[Data](a.mut, 0, d.give);
                array_give[Data](a.give, 0);
            }
        }
    });
}

/// array_give on a shared array should work
#[test]
fn array_give_shared() {
    crate::assert_ok!({
        class TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                array_initialize[Int](a.mut, 0, 42);
                let b = a.give.share;
                array_give[Int](b.give, 0);
            }
        }
    });
}

/// array_give on a ref array should work
#[test]
fn array_give_ref() {
    crate::assert_ok!({
        class TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                array_initialize[Int](a.mut, 0, 42);
                array_give[Int](a.ref, 0);
            }
        }
    });
}

/// array_give on a mut array should work
#[test]
fn array_give_mut() {
    crate::assert_ok!({
        class TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                array_initialize[Int](a.mut, 0, 42);
                array_give[Int](a.mut, 0);
            }
        }
    });
}

/// array_give with wrong type parameter should fail
#[test]
fn array_give_wrong_type_param() {
    crate::assert_err!({
        class Data {
            x: Int;
        }

        class TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                array_initialize[Int](a.mut, 0, 42);
                array_give[Data](a.give, 0);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { x : Int ; } class TheClass { fn go (given self) -> Int { let a = array_new [Int](5) ; array_initialize [Int](a . mut , 0 , 42) ; array_give [Data](a . give , 0) ; } } }`"]);
}

/// array_give on a non-array should fail
#[test]
fn array_give_not_an_array() {
    crate::assert_err!({
        class TheClass {
            fn go(given self) -> Int {
                array_give[Int](22, 0);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class TheClass { fn go (given self) -> Int { array_give [Int](22 , 0) ; } } }`"]);
}

/// array_give with non-Int index should fail
#[test]
fn array_give_bad_index_type() {
    crate::assert_err!({
        class Data {
            x: Int;
        }

        class TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                array_initialize[Int](a.mut, 0, 42);
                let d = new Data(10);
                array_give[Int](a.give, d.give);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { x : Int ; } class TheClass { fn go (given self) -> Int { let a = array_new [Int](5) ; array_initialize [Int](a . mut , 0 , 42) ; let d = new Data (10) ; array_give [Int](a . give , d . give) ; } } }`"]);
}

/// array_give return type should be the element type, not Int — using it where Data expected should work
#[test]
#[allow(non_snake_case)]
fn array_give_returns_element_type() {
    crate::assert_err!({
        class Data {
            x: Int;
        }

        class TheClass {
            fn go(given self) -> Data {
                let a = array_new[Int](5);
                array_initialize[Int](a.mut, 0, 42);
                array_give[Int](a.give, 0);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { x : Int ; } class TheClass { fn go (given self) -> Data { let a = array_new [Int](5) ; array_initialize [Int](a . mut , 0 , 42) ; array_give [Int](a . give , 0) ; } } }`"]);
}

// =============================================================================
// ArrayDrop
// =============================================================================

/// array_drop on a given array should fail — requires mut
#[test]
fn array_drop_given() {
    crate::assert_err!({
        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_initialize[Int](a.mut, 0, 42);
                array_drop[Int](a.give, 0);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class TheClass { fn go (given self) -> () { let a = array_new [Int](5) ; array_initialize [Int](a . mut , 0 , 42) ; array_drop [Int](a . give , 0) ; } } }`"]);
}

/// array_drop on a given Array[Data] should fail — requires mut
#[test]
#[allow(non_snake_case)]
fn array_drop_given_class() {
    crate::assert_err!({
        class Data {
            x: Int;
        }

        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Data](3);
                let d = new Data(10);
                array_initialize[Data](a.mut, 0, d.give);
                array_drop[Data](a.give, 0);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { x : Int ; } class TheClass { fn go (given self) -> () { let a = array_new [Data](3) ; let d = new Data (10) ; array_initialize [Data](a . mut , 0 , d . give) ; array_drop [Data](a . give , 0) ; } } }`"]);
}

/// array_drop on a shared array should fail — requires mut
#[test]
fn array_drop_shared() {
    crate::assert_err!({
        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_initialize[Int](a.mut, 0, 42);
                let b = a.give.share;
                array_drop[Int](b.mut, 0);
            }
        }
    }, expect_test::expect![[r#"
        the rule "compose rhs-copy" at (predicates.rs) failed because
          pattern `true` did not match value `false`

        the rule "isnt known to be copy" at (predicates.rs) failed because
          pattern `false` did not match value `true`"#]]);
}

/// array_drop on a ref array should fail — requires mut
#[test]
fn array_drop_ref() {
    crate::assert_err!({
        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_initialize[Int](a.mut, 0, 42);
                array_drop[Int](a.ref, 0);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class TheClass { fn go (given self) -> () { let a = array_new [Int](5) ; array_initialize [Int](a . mut , 0 , 42) ; array_drop [Int](a . ref , 0) ; } } }`"]);
}

/// array_drop on a mut array should work
#[test]
fn array_drop_mut() {
    crate::assert_ok!({
        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_initialize[Int](a.mut, 0, 42);
                array_drop[Int](a.mut, 0);
            }
        }
    });
}

/// array_drop with wrong type parameter should fail
#[test]
fn array_drop_wrong_type_param() {
    crate::assert_err!({
        class Data {
            x: Int;
        }

        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_initialize[Int](a.mut, 0, 42);
                array_drop[Data](a.mut, 0);
            }
        }
    }, expect_test::expect![[r#"
        the rule "shared-class copy" at (predicates.rs) failed because
          pattern `true` did not match value `false`

        the rule "mt owned" at (predicates.rs) failed because
          pattern `true` did not match value `false`"#]]);
}

/// array_drop on a non-array should fail
#[test]
fn array_drop_not_an_array() {
    crate::assert_err!({
        class TheClass {
            fn go(given self) -> () {
                array_drop[Int](22, 0);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class TheClass { fn go (given self) -> () { array_drop [Int](22 , 0) ; } } }`"]);
}

/// array_drop with non-Int index should fail
#[test]
fn array_drop_bad_index_type() {
    crate::assert_err!({
        class Data {
            x: Int;
        }

        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_initialize[Int](a.mut, 0, 42);
                let d = new Data(10);
                array_drop[Int](a.mut, d.give);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { x : Int ; } class TheClass { fn go (given self) -> () { let a = array_new [Int](5) ; array_initialize [Int](a . mut , 0 , 42) ; let d = new Data (10) ; array_drop [Int](a . mut , d . give) ; } } }`"]);
}

/// array_drop returns unit, not the element type
#[test]
fn array_drop_returns_unit() {
    crate::assert_err!({
        class TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                array_initialize[Int](a.mut, 0, 42);
                array_drop[Int](a.mut, 0);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class TheClass { fn go (given self) -> Int { let a = array_new [Int](5) ; array_initialize [Int](a . mut , 0 , 42) ; array_drop [Int](a . mut , 0) ; } } }`"]);
}
