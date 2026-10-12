use formality_core::test;

// =============================================================================
// ArrayNew
// =============================================================================

/// array_new[Int](5) should type-check and produce Array[Int]
#[test]
fn array_new_int() {
    crate::assert_ok!({
        struct TheClass {
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
        struct Data {
            x: Int;
        }

        struct TheClass {
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
        struct Data {
            x: Int;
        }

        struct TheClass {
            fn go(given self) -> Array[Int] {
                let d = new Data(1);
                array_new[Int](d^);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { x : Int ; } struct TheClass { fn go (given self) -> Array[Int] { let d = new Data (1) ; array_new [Int](d ^) ; } } }`"]);
}

/// array_new with two type parameters should fail
#[test]
fn array_new_two_type_params() {
    crate::assert_err!({
        struct Data {
            x: Int;
        }

        struct TheClass {
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
        struct TheClass {
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
        struct TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                array_capacity[Int, given](a^);
            }
        }
    });
}

/// array_capacity on a shared array should work
#[test]
fn array_capacity_shared() {
    crate::assert_ok!({
        struct TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                let b = a^.share;
                array_capacity[Int, shared](b^);
            }
        }
    });
}

/// array_capacity on a place sharing (borrowed) array should work
#[test]
fn array_capacity_ref() {
    crate::assert_ok!({
        struct TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                array_capacity[Int, shared[a]](a.share);
            }
        }
    });
}

/// array_capacity on a mut array should work
#[test]
fn array_capacity_mut() {
    crate::assert_ok!({
        struct TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                array_capacity[Int, ![a]](a!);
            }
        }
    });
}

/// array_capacity with wrong type parameter should fail
#[test]
fn array_capacity_wrong_type_param() {
    crate::assert_err!({
        struct Data {
            x: Int;
        }

        struct TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                array_capacity[Data, given](a^);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { x : Int ; } struct TheClass { fn go (given self) -> Int { let a = array_new [Int](5) ; array_capacity [Data, given](a ^) ; } } }`"]);
}

/// array_capacity on a non-array should fail
#[test]
fn array_capacity_not_an_array() {
    crate::assert_err!({
        struct TheClass {
            fn go(given self) -> Int {
                array_capacity[Int, given](22);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct TheClass { fn go (given self) -> Int { array_capacity [Int, given](22) ; } } }`"]);
}

// =============================================================================
// ArrayWrite
// =============================================================================

/// array_write on a given array with Int elements
#[test]
fn array_write_given_int() {
    crate::assert_ok!({
        struct TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_write[Int, ![a]](a!, 0, 42);
            }
        }
    });
}

/// array_write on a given array with class elements
#[test]
#[allow(non_snake_case)]
fn array_write_given_class() {
    crate::assert_ok!({
        struct Data {
            x: Int;
        }

        struct TheClass {
            fn go(given self) -> () {
                let a = array_new[Data](3);
                let d = new Data(10);
                array_write[Data, ![a]](a!, 0, d^);
            }
        }
    });
}

/// array_write on a shared array should work
#[test]
fn array_write_shared() {
    // array_write requires mut; shared array's mut lease isn't truly mutable
    crate::assert_err!({
        struct TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                let b = a^.share;
                array_write[Int, ![b]](b!, 0, 42);
            }
        }
    }, expect_test::expect![[r#"
        the rule "isnt shared" at (predicates.rs) failed because
          condition evaluted to false: `!prove_is_shared(env, p).is_proven()`"#]]);
}

/// array_write on a place sharing array should fail — requires mut
#[test]
fn array_write_ref() {
    crate::assert_err!({
        struct TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_write[Int, shared[a]](a.share, 0, 42);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct TheClass { fn go (given self) -> () { let a = array_new [Int](5) ; array_write [Int, shared [a]](a . share , 0 , 42) ; } } }`"]);
}

/// place sharing strips mutability — place sharing of mut should not satisfy prove_is_mut
#[test]
fn array_write_ref_of_mut() {
    crate::assert_err!({
        struct TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                let array_mut = a!;
                array_write[Int, shared[array_mut]](array_mut.share, 0, 42);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct TheClass { fn go (given self) -> () { let a = array_new [Int](5) ; let array_mut = a ! ; array_write [Int, shared [array_mut]](array_mut . share , 0 , 42) ; } } }`"]);
}

/// array_write on a mut array should work
#[test]
fn array_write_mut() {
    crate::assert_ok!({
        struct TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_write[Int, ![a]](a!, 0, 42);
            }
        }
    });
}

/// array_write with wrong type parameter should fail
#[test]
fn array_write_wrong_type_param() {
    crate::assert_err!({
        struct Data {
            x: Int;
        }

        struct TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_write[Data, ![a]](a!, 0, 42);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { x : Int ; } struct TheClass { fn go (given self) -> () { let a = array_new [Int](5) ; array_write [Data, ! [a]](a ! , 0 , 42) ; } } }`"]);
}

/// array_write with wrong value type should fail
#[test]
fn array_write_wrong_value_type() {
    crate::assert_err!({
        struct Data {
            x: Int;
        }

        struct TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                let d = new Data(10);
                array_write[Int, ![a]](a!, 0, d^);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { x : Int ; } struct TheClass { fn go (given self) -> () { let a = array_new [Int](5) ; let d = new Data (10) ; array_write [Int, ! [a]](a ! , 0 , d ^) ; } } }`"]);
}

/// array_write on a non-array should fail
#[test]
fn array_write_not_an_array() {
    crate::assert_err!({
        struct TheClass {
            fn go(given self) -> () {
                array_write[Int, given](22, 0, 42);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct TheClass { fn go (given self) -> () { array_write [Int, given](22 , 0 , 42) ; } } }`"]);
}

/// array_write with non-Int index should fail
#[test]
fn array_write_bad_index_type() {
    crate::assert_err!({
        struct Data {
            x: Int;
        }

        struct TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                let d = new Data(10);
                array_write[Int, ![a]](a!, d^, 42);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { x : Int ; } struct TheClass { fn go (given self) -> () { let a = array_new [Int](5) ; let d = new Data (10) ; array_write [Int, ! [a]](a ! , d ^ , 42) ; } } }`"]);
}

// =============================================================================
// ArrayGive
// =============================================================================

/// array_give on a ^ Array[Int] returns Int
#[test]
fn array_give_given_int() {
    crate::assert_ok!({
        struct TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                array_write[Int, ![a]](a!, 0, 42);
                array_give[Int, given, given](a^, 0);
            }
        }
    });
}

/// array_give on a ^ Array[Data] returns Data
#[test]
#[allow(non_snake_case)]
fn array_give_given_class() {
    crate::assert_ok!({
        struct Data {
            x: Int;
        }

        struct TheClass {
            fn go(given self) -> Data {
                let a = array_new[Data](3);
                let d = new Data(10);
                array_write[Data, ![a]](a!, 0, d^);
                array_give[Data, given, given](a^, 0);
            }
        }
    });
}

/// array_give on a shared array should work
#[test]
fn array_give_shared() {
    crate::assert_ok!({
        struct TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                array_write[Int, ![a]](a!, 0, 42);
                let b = a^.share;
                array_give[Int, given, shared](b^, 0);
            }
        }
    });
}

/// array_give on a place sharing array should work
#[test]
fn array_give_ref() {
    crate::assert_ok!({
        struct TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                array_write[Int, ![a]](a!, 0, 42);
                array_give[Int, given, shared[a]](a.share, 0);
            }
        }
    });
}

/// array_give on a mut array should work
#[test]
fn array_give_mut() {
    crate::assert_ok!({
        struct TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                array_write[Int, ![a]](a!, 0, 42);
                array_give[Int, given, ![a]](a!, 0);
            }
        }
    });
}

/// array_give with wrong type parameter should fail
#[test]
fn array_give_wrong_type_param() {
    crate::assert_err!({
        struct Data {
            x: Int;
        }

        struct TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                array_write[Int, ![a]](a!, 0, 42);
                array_give[Data, given, given](a^, 0);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { x : Int ; } struct TheClass { fn go (given self) -> Int { let a = array_new [Int](5) ; array_write [Int, ! [a]](a ! , 0 , 42) ; array_give [Data, given, given](a ^ , 0) ; } } }`"]);
}

/// array_give on a non-array should fail
#[test]
fn array_give_not_an_array() {
    crate::assert_err!({
        struct TheClass {
            fn go(given self) -> Int {
                array_give[Int, given, given](22, 0);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct TheClass { fn go (given self) -> Int { array_give [Int, given, given](22 , 0) ; } } }`"]);
}

/// array_give with non-Int index should fail
#[test]
fn array_give_bad_index_type() {
    crate::assert_err!({
        struct Data {
            x: Int;
        }

        struct TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                array_write[Int, ![a]](a!, 0, 42);
                let d = new Data(10);
                array_give[Int, given, given](a^, d^);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { x : Int ; } struct TheClass { fn go (given self) -> Int { let a = array_new [Int](5) ; array_write [Int, ! [a]](a ! , 0 , 42) ; let d = new Data (10) ; array_give [Int, given, given](a ^ , d ^) ; } } }`"]);
}

/// array_give return type should be the element type, not Int — using it where Data expected should work
#[test]
#[allow(non_snake_case)]
fn array_give_returns_element_type() {
    crate::assert_err!({
        struct Data {
            x: Int;
        }

        struct TheClass {
            fn go(given self) -> Data {
                let a = array_new[Int](5);
                array_write[Int, ![a]](a!, 0, 42);
                array_give[Int, given, given](a^, 0);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { x : Int ; } struct TheClass { fn go (given self) -> Data { let a = array_new [Int](5) ; array_write [Int, ! [a]](a ! , 0 , 42) ; array_give [Int, given, given](a ^ , 0) ; } } }`"]);
}

// =============================================================================
// ArrayDrop
// =============================================================================

/// array_drop on a given array should work (A is shared is satisfied by ^)
#[test]
fn array_drop_given() {
    crate::assert_ok!({
        struct TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_write[Int, ![a]](a!, 0, 42);
                array_drop[Int, given, given](a^, 0, 1);
            }
        }
    });
}

/// array_drop on a ^ Array[Data] should work
#[test]
#[allow(non_snake_case)]
fn array_drop_given_class() {
    crate::assert_ok!({
        struct Data {
            x: Int;
        }

        struct TheClass {
            fn go(given self) -> () {
                let a = array_new[Data](3);
                let d = new Data(10);
                array_write[Data, ![a]](a!, 0, d^);
                array_drop[Data, given, given](a^, 0, 1);
            }
        }
    });
}

/// array_drop on a shared array should fail — requires mut
#[test]
fn array_drop_shared() {
    crate::assert_err!({
        struct TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_write[Int, ![a]](a!, 0, 42);
                let b = a^.share;
                array_drop[Int, given, ![b]](b!, 0, 1);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct TheClass { fn go (given self) -> () { let a = array_new [Int](5) ; array_write [Int, ! [a]](a ! , 0 , 42) ; let b = a ^ . share ; array_drop [Int, given, ! [b]](b ! , 0 , 1) ; } } }`"]);
}

/// array_drop on a place sharing array should work (A is shared is satisfied)
#[test]
fn array_drop_ref() {
    crate::assert_ok!({
        struct TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_write[Int, ![a]](a!, 0, 42);
                array_drop[Int, given, shared[a]](a.share, 0, 1);
            }
        }
    });
}

/// array_drop on a mut array should work
#[test]
fn array_drop_mut() {
    crate::assert_ok!({
        struct TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_write[Int, ![a]](a!, 0, 42);
                array_drop[Int, given, ![a]](a!, 0, 1);
            }
        }
    });
}

/// array_drop with wrong type parameter should fail
#[test]
fn array_drop_wrong_type_param() {
    crate::assert_err!({
        struct Data {
            x: Int;
        }

        struct TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_write[Int, ![a]](a!, 0, 42);
                array_drop[Data, given, ![a]](a!, 0, 1);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { x : Int ; } struct TheClass { fn go (given self) -> () { let a = array_new [Int](5) ; array_write [Int, ! [a]](a ! , 0 , 42) ; array_drop [Data, given, ! [a]](a ! , 0 , 1) ; } } }`"]);
}

/// array_drop on a non-array should fail
#[test]
fn array_drop_not_an_array() {
    crate::assert_err!({
        struct TheClass {
            fn go(given self) -> () {
                array_drop[Int, given, given](22, 0, 1);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct TheClass { fn go (given self) -> () { array_drop [Int, given, given](22 , 0 , 1) ; } } }`"]);
}

/// array_drop with non-Int index should fail
#[test]
fn array_drop_bad_index_type() {
    crate::assert_err!({
        struct Data {
            x: Int;
        }

        struct TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_write[Int, ![a]](a!, 0, 42);
                let d = new Data(10);
                array_drop[Int, given, ![a]](a!, d^, d^ + 1);
            }
        }
    }, expect_test::expect![[r#"
        the rule "give" at (expressions.rs) failed because
          condition evaluted to false: `!live_after.is_live(place)`
            live_after = LivePlaces { accessed: {d}, traversed: {} }
            place = d"#]]);
}

/// array_drop returns unit, not the element type
#[test]
fn array_drop_returns_unit() {
    crate::assert_err!({
        struct TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                array_write[Int, ![a]](a!, 0, 42);
                array_drop[Int, given, ![a]](a!, 0, 1);
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct TheClass { fn go (given self) -> Int { let a = array_new [Int](5) ; array_write [Int, ! [a]](a ! , 0 , 42) ; array_drop [Int, given, ! [a]](a ! , 0 , 1) ; } } }`"]);
}
