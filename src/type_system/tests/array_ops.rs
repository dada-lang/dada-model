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
    }, expect_test::expect![[r#"src/type_system/subtypes.rs:38:1: no applicable rules for sub { a: Data, b: Int, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, d: Data}, assumptions: {}, fresh: 0 } }"#]]);
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
                array_capacity[Int, given](a.give);
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
                array_capacity[Int, shared](b.give);
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
                array_capacity[Int, ref[a]](a.ref);
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
                array_capacity[Int, mut[a]](a.mut);
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
                array_capacity[Data, given](a.give);
            }
        }
    }, expect_test::expect![[r#"
        src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, a: Array[Int]}, assumptions: {}, fresh: 0 } }

        src/type_system/subtypes.rs:38:1: no applicable rules for sub { a: given Int, b: given Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, a: Array[Int]}, assumptions: {}, fresh: 0 } }

        src/type_system/subtypes.rs:38:1: no applicable rules for sub { a: Int, b: Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, a: Array[Int]}, assumptions: {}, fresh: 0 } }"#]]);
}

/// array_capacity on a non-array should fail
#[test]
fn array_capacity_not_an_array() {
    crate::assert_err!({
        class TheClass {
            fn go(given self) -> Int {
                array_capacity[Int, given](22);
            }
        }
    }, expect_test::expect![[r#"src/type_system/subtypes.rs:38:1: no applicable rules for sub { a: Int, b: given Array[Int], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 } }"#]]);
}

// =============================================================================
// ArrayWrite
// =============================================================================

/// array_write on a given array with Int elements
#[test]
fn array_write_given_int() {
    crate::assert_ok!({
        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_write[Int, mut[a]](a.mut, 0, 42);
            }
        }
    });
}

/// array_write on a given array with class elements
#[test]
#[allow(non_snake_case)]
fn array_write_given_class() {
    crate::assert_ok!({
        class Data {
            x: Int;
        }

        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Data](3);
                let d = new Data(10);
                array_write[Data, mut[a]](a.mut, 0, d.give);
            }
        }
    });
}

/// array_write on a shared array should work
#[test]
fn array_write_shared() {
    // array_write requires mut; shared array's mut lease isn't truly mutable
    crate::assert_err!({
        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                let b = a.give.share;
                array_write[Int, mut[b]](b.mut, 0, 42);
            }
        }
    }, expect_test::expect![[r#"
        src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, a: Array[Int], b: shared Array[Int]}, assumptions: {}, fresh: 0 } }

        src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, a: Array[Int], b: shared Array[Int]}, assumptions: {}, fresh: 0 } }

        the rule "isnt copy" at (predicates.rs) failed because
          condition evaluated to false: `!prove_is_copy(env, p).is_proven()`"#]]);
}

/// array_write on a ref array should fail — requires mut
#[test]
fn array_write_ref() {
    crate::assert_err!({
        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_write[Int, ref[a]](a.ref, 0, 42);
            }
        }
    }, expect_test::expect![[r#"src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: ref [a], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, a: Array[Int]}, assumptions: {}, fresh: 0 } }"#]]);
}

/// ref strips mutability — ref of mut should not satisfy prove_is_mut
#[test]
fn array_write_ref_of_mut() {
    crate::assert_err!({
        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                let array_mut = a.mut;
                array_write[Int, ref[array_mut]](array_mut.ref, 0, 42);
            }
        }
    }, expect_test::expect![[r#"src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: ref [array_mut], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, a: Array[Int], array_mut: mut [a] Array[Int]}, assumptions: {}, fresh: 0 } }"#]]);
}

/// array_write on a mut array should work
#[test]
fn array_write_mut() {
    crate::assert_ok!({
        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_write[Int, mut[a]](a.mut, 0, 42);
            }
        }
    });
}

/// array_write with wrong type parameter should fail
#[test]
fn array_write_wrong_type_param() {
    crate::assert_err!({
        class Data {
            x: Int;
        }

        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_write[Data, mut[a]](a.mut, 0, 42);
            }
        }
    }, expect_test::expect![[r#"
        src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: mut [a], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, a: Array[Int]}, assumptions: {}, fresh: 0 } }

        src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Array[Int], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, a: Array[Int]}, assumptions: {}, fresh: 0 } }

        src/type_system/subtypes.rs:38:1: no applicable rules for sub { a: Int, b: Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, a: Array[Int]}, assumptions: {}, fresh: 0 } }"#]]);
}

/// array_write with wrong value type should fail
#[test]
fn array_write_wrong_value_type() {
    crate::assert_err!({
        class Data {
            x: Int;
        }

        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                let d = new Data(10);
                array_write[Int, mut[a]](a.mut, 0, d.give);
            }
        }
    }, expect_test::expect![[r#"src/type_system/subtypes.rs:38:1: no applicable rules for sub { a: Data, b: Int, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, a: Array[Int], d: Data}, assumptions: {}, fresh: 0 } }"#]]);
}

/// array_write on a non-array should fail
#[test]
fn array_write_not_an_array() {
    crate::assert_err!({
        class TheClass {
            fn go(given self) -> () {
                array_write[Int, given](22, 0, 42);
            }
        }
    }, expect_test::expect![[r#"src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 } }"#]]);
}

/// array_write with non-Int index should fail
#[test]
fn array_write_bad_index_type() {
    crate::assert_err!({
        class Data {
            x: Int;
        }

        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                let d = new Data(10);
                array_write[Int, mut[a]](a.mut, d.give, 42);
            }
        }
    }, expect_test::expect![[r#"src/type_system/subtypes.rs:38:1: no applicable rules for sub { a: Data, b: Int, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, a: Array[Int], d: Data}, assumptions: {}, fresh: 0 } }"#]]);
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
                array_write[Int, mut[a]](a.mut, 0, 42);
                array_give[Int, given, given](a.give, 0);
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
                array_write[Data, mut[a]](a.mut, 0, d.give);
                array_give[Data, given, given](a.give, 0);
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
                array_write[Int, mut[a]](a.mut, 0, 42);
                let b = a.give.share;
                array_give[Int, given, shared](b.give, 0);
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
                array_write[Int, mut[a]](a.mut, 0, 42);
                array_give[Int, given, ref[a]](a.ref, 0);
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
                array_write[Int, mut[a]](a.mut, 0, 42);
                array_give[Int, given, mut[a]](a.mut, 0);
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
                array_write[Int, mut[a]](a.mut, 0, 42);
                array_give[Data, given, given](a.give, 0);
            }
        }
    }, expect_test::expect![[r#"
        src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, a: Array[Int]}, assumptions: {}, fresh: 0 } }

        src/type_system/subtypes.rs:38:1: no applicable rules for sub { a: given Int, b: given Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, a: Array[Int]}, assumptions: {}, fresh: 0 } }

        src/type_system/subtypes.rs:38:1: no applicable rules for sub { a: Int, b: Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, a: Array[Int]}, assumptions: {}, fresh: 0 } }"#]]);
}

/// array_give on a non-array should fail
#[test]
fn array_give_not_an_array() {
    crate::assert_err!({
        class TheClass {
            fn go(given self) -> Int {
                array_give[Int, given, given](22, 0);
            }
        }
    }, expect_test::expect![[r#"src/type_system/subtypes.rs:38:1: no applicable rules for sub { a: Int, b: given Array[Int], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 } }"#]]);
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
                array_write[Int, mut[a]](a.mut, 0, 42);
                let d = new Data(10);
                array_give[Int, given, given](a.give, d.give);
            }
        }
    }, expect_test::expect![[r#"src/type_system/subtypes.rs:38:1: no applicable rules for sub { a: Data, b: Int, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, a: Array[Int], d: Data}, assumptions: {}, fresh: 0 } }"#]]);
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
                array_write[Int, mut[a]](a.mut, 0, 42);
                array_give[Int, given, given](a.give, 0);
            }
        }
    }, expect_test::expect![[r#"src/type_system/subtypes.rs:38:1: no applicable rules for sub { a: Int, b: Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 } }"#]]);
}

// =============================================================================
// ArrayDrop
// =============================================================================

/// array_drop on a given array should work (A is ref is satisfied by given)
#[test]
fn array_drop_given() {
    crate::assert_ok!({
        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_write[Int, mut[a]](a.mut, 0, 42);
                array_drop[Int, given, given](a.give, 0, 1);
            }
        }
    });
}

/// array_drop on a given Array[Data] should work
#[test]
#[allow(non_snake_case)]
fn array_drop_given_class() {
    crate::assert_ok!({
        class Data {
            x: Int;
        }

        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Data](3);
                let d = new Data(10);
                array_write[Data, mut[a]](a.mut, 0, d.give);
                array_drop[Data, given, given](a.give, 0, 1);
            }
        }
    });
}

/// array_drop on a shared array should fail — requires mut
#[test]
fn array_drop_shared() {
    crate::assert_err!({
        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_write[Int, mut[a]](a.mut, 0, 42);
                let b = a.give.share;
                array_drop[Int, given, mut[b]](b.mut, 0, 1);
            }
        }
    }, expect_test::expect![[r#"
        src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, a: Array[Int], b: shared Array[Int]}, assumptions: {}, fresh: 0 } }

        src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, a: Array[Int], b: shared Array[Int]}, assumptions: {}, fresh: 0 } }

        src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, a: Array[Int], b: shared Array[Int]}, assumptions: {}, fresh: 0 } }"#]]);
}

/// array_drop on a ref array should work (A is ref is satisfied)
#[test]
fn array_drop_ref() {
    crate::assert_ok!({
        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_write[Int, mut[a]](a.mut, 0, 42);
                array_drop[Int, given, ref[a]](a.ref, 0, 1);
            }
        }
    });
}

/// array_drop on a mut array should work
#[test]
fn array_drop_mut() {
    crate::assert_ok!({
        class TheClass {
            fn go(given self) -> () {
                let a = array_new[Int](5);
                array_write[Int, mut[a]](a.mut, 0, 42);
                array_drop[Int, given, mut[a]](a.mut, 0, 1);
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
                array_write[Int, mut[a]](a.mut, 0, 42);
                array_drop[Data, given, mut[a]](a.mut, 0, 1);
            }
        }
    }, expect_test::expect![[r#"
        src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: mut [a], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, a: Array[Int]}, assumptions: {}, fresh: 0 } }

        src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Array[Int], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, a: Array[Int]}, assumptions: {}, fresh: 0 } }

        src/type_system/subtypes.rs:38:1: no applicable rules for sub { a: Int, b: Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, a: Array[Int]}, assumptions: {}, fresh: 0 } }"#]]);
}

/// array_drop on a non-array should fail
#[test]
fn array_drop_not_an_array() {
    crate::assert_err!({
        class TheClass {
            fn go(given self) -> () {
                array_drop[Int, given, given](22, 0, 1);
            }
        }
    }, expect_test::expect![[r#"src/type_system/subtypes.rs:38:1: no applicable rules for sub { a: Int, b: given Array[Int], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 } }"#]]);
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
                array_write[Int, mut[a]](a.mut, 0, 42);
                let d = new Data(10);
                array_drop[Int, given, mut[a]](a.mut, d.give, d.give + 1);
            }
        }
    }, expect_test::expect![[r#"
        src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, a: Array[Int], d: Data}, assumptions: {}, fresh: 0 } }

        the rule "give" at (expressions.rs) failed because
          condition evaluated to false: `!live_after.is_live(place)`
            live_after = LivePlaces { accessed: {d}, traversed: {} }
            place = d"#]]);
}

/// array_drop returns unit, not the element type
#[test]
fn array_drop_returns_unit() {
    crate::assert_err!({
        class TheClass {
            fn go(given self) -> Int {
                let a = array_new[Int](5);
                array_write[Int, mut[a]](a.mut, 0, 42);
                array_drop[Int, given, mut[a]](a.mut, 0, 1);
            }
        }
    }, expect_test::expect![[r#"src/type_system/subtypes.rs:38:1: no applicable rules for sub { a: (), b: Int, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 } }"#]]);
}
