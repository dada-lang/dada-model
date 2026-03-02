// Tests for Array[T] operations: ArrayNew, ArrayCapacity, ArrayGive, ArrayDrop, ArrayInitialize.
//
// All tests use assert_interpret_only! since the type checker's Array rules
// are simplified stubs — the real typing (e.g., ArrayGive returning given[array] T)
// is deferred.
//
// Arrays that need to be used multiple times must be shared first:
// `let a = array_new[Int](3).share;` — shared arrays can be given repeatedly
// without uninitializing the source.

// ---------------------------------------------------------------
// Class with Array field — ownership transfer correctness
// ---------------------------------------------------------------

#[test]
fn class_with_array_field_new() {
    // A class holding a Given Array[Int] field. Constructing it must NOT
    // drop the array temp after the bitwise copy into the class — that
    // would free the backing allocation and leave the field dangling.
    // Before the fix, `free(fv)` after `instantiate_class` decremented
    // the refcount to 0 and freed the allocation; now `uninitialize` is
    // used instead.
    crate::assert_interpret_only!(
        {
            class Wrapper {
                field: Array[Int];
            }
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](3);
                    let w = new Wrapper(a.give);
                    array_capacity[Int](w.field.give);
                }
            }
        },
        expect_test::expect![[r#"
            Result: 3
            Alloc 0x0a: [Int(3)]"#]]
    );
}

#[test]
fn reassign_drops_old_array() {
    // Reassigning a variable that holds an Array should drop (decrement
    // refcount of) the old array before installing the new one.
    // If the old array were leaked the refcount would never reach zero
    // and its allocation would still appear in the heap snapshot.
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2).share;
                    array_initialize[Int](a.give, 0, 1);
                    array_initialize[Int](a.give, 1, 2);
                    // Replace a with a fresh array — old array must be dropped.
                    a = array_new[Int](4).share;
                    array_capacity[Int](a.give);
                }
            }
        },
        expect_test::expect![[r#"
            Result: 4
            Alloc 0x13: [Int(4)]"#]]
    );
}

// ---------------------------------------------------------------
// Basic array creation and capacity
// ---------------------------------------------------------------

#[test]
fn array_new_and_capacity() {
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](3);
                    array_capacity[Int](a.give);
                }
            }
        },
        expect_test::expect![[r#"
            Result: 3
            Alloc 0x07: [Int(3)]"#]]
    );
}

#[test]
fn array_size_of() {
    // Array[T] is two words: Word::Flags + Word::Pointer
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    size_of[Array[Int]]();
                }
            }
        },
        expect_test::expect![[r#"
            Result: 2
            Alloc 0x02: [Int(2)]"#]]
    );
}

// ---------------------------------------------------------------
// Initialize and get — Int elements
// ---------------------------------------------------------------

#[test]
fn array_initialize_and_get_int() {
    // Share the array so we can pass it to multiple operations.
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](3).share;
                    array_initialize[Int](a.give, 0, 10);
                    array_initialize[Int](a.give, 1, 20);
                    array_initialize[Int](a.give, 2, 30);
                    print(array_give[Int](a.give, 0));
                    print(array_give[Int](a.give, 1));
                    array_give[Int](a.give, 2);
                }
            }
        },
        expect_test::expect![[r#"
            Output: 10
            Output: 20
            Result: 30
            Alloc 0x1c: [Int(30)]"#]]
    );
}

// ---------------------------------------------------------------
// Initialize and get — class elements
// ---------------------------------------------------------------

#[test]
fn array_initialize_and_get_class() {
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let a = array_new[Data](2).share;
                    array_initialize[Data](a.give, 0, new Data(42));
                    array_initialize[Data](a.give, 1, new Data(99));
                    print(array_give[Data](a.give, 0));
                    array_give[Data](a.give, 1);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Data { flag: Given, x: 42 }
            Result: Data { flag: Given, x: 99 }
            Alloc 0x16: [Flags(Given), Int(99)]"#]]
    );
}

// ---------------------------------------------------------------
// Error cases: uninitialized access
// ---------------------------------------------------------------

#[test]
fn array_give_uninitialized_faults() {
    crate::assert_interpret_fault!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](3);
                    array_give[Int](a.give, 0);
                }
            }
        },
        "element is uninitialized"
    );
}

#[test]
fn array_give_int_is_copy() {
    // Int is a copy type — giving it doesn't uninitialize the source.
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2).share;
                    array_initialize[Int](a.give, 0, 42);
                    let x = array_give[Int](a.give, 0);
                    array_give[Int](a.give, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Result: 42
            Alloc 0x10: [Int(42)]"#]]
    );
}

#[test]
fn array_give_class_moves_out() {
    // Class elements have flags — giving moves out and uninitializes the source.
    crate::assert_interpret_fault!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let a = array_new[Data](2).share;
                    array_initialize[Data](a.give, 0, new Data(42));
                    let x = array_give[Data](a.give, 0);
                    array_give[Data](a.give, 0);
                }
            }
        },
        "element is uninitialized"
    );
}

// ---------------------------------------------------------------
// Error cases: out of bounds
// ---------------------------------------------------------------

#[test]
fn array_give_out_of_bounds() {
    crate::assert_interpret_fault!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_give[Int](a.give, 5);
                }
            }
        },
        "out of bounds"
    );
}

#[test]
fn array_initialize_out_of_bounds() {
    crate::assert_interpret_fault!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_initialize[Int](a.give, 3, 42);
                    0;
                }
            }
        },
        "out of bounds"
    );
}

// ---------------------------------------------------------------
// Double initialize
// ---------------------------------------------------------------

#[test]
fn array_initialize_already_initialized_faults() {
    crate::assert_interpret_fault!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2).share;
                    array_initialize[Int](a.give, 0, 10);
                    array_initialize[Int](a.give, 0, 20);
                    0;
                }
            }
        },
        "already initialized"
    );
}

// ---------------------------------------------------------------
// ArrayDrop
// ---------------------------------------------------------------

#[test]
fn array_drop_element() {
    // Drop an element, then getting it should fault.
    crate::assert_interpret_fault!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2).share;
                    array_initialize[Int](a.give, 0, 42);
                    array_drop[Int](a.give, 0);
                    array_give[Int](a.give, 0);
                }
            }
        },
        "element is uninitialized"
    );
}

#[test]
fn array_drop_class_element() {
    // Drop a class element — should recursively drop.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Data](1).share;
                    array_initialize[Data](a.give, 0, new Data(42));
                    array_drop[Data](a.give, 0);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Result: 0
            Alloc 0x0e: [Int(0)]"#]]
    );
}

// ---------------------------------------------------------------
// Array give and share
// ---------------------------------------------------------------

#[test]
fn array_give() {
    // Giving a Given array moves it — new owner can access elements.
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](1);
                    let b = a.give;
                    array_capacity[Int](b.give);
                }
            }
        },
        expect_test::expect![[r#"
            Result: 1
            Alloc 0x09: [Int(1)]"#]]
    );
}

#[test]
fn array_give_then_get() {
    // Give the array to a new variable, then use the new variable.
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2).share;
                    array_initialize[Int](a.give, 0, 10);
                    array_initialize[Int](a.give, 1, 20);
                    let b = a.give;
                    array_give[Int](b.give, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Result: 10
            Alloc 0x12: [Int(10)]"#]]
    );
}

#[test]
fn array_give_uninitializes_source() {
    crate::assert_interpret_fault!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](1);
                    let b = a.give;
                    array_capacity[Int](a.give);
                }
            }
        },
        "uninitialized"
    );
}

#[test]
fn array_share() {
    // Sharing an array sets its flags to Shared.
    // A shared array can be given multiple times.
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2).share;
                    array_initialize[Int](a.give, 0, 10);
                    array_initialize[Int](a.give, 1, 20);
                    let x = array_give[Int](a.give, 0);
                    let y = array_give[Int](a.give, 1);
                    x.give + y.give;
                }
            }
        },
        expect_test::expect![[r#"
            Result: 30
            Alloc 0x18: [Int(30)]"#]]
    );
}

// ---------------------------------------------------------------
// Refcount lifecycle
// ---------------------------------------------------------------

#[test]
fn shared_array_survives_after_original_dropped() {
    // Share an array to two variables, drop one, the other still works.
    // The refcount goes: 1 (new) → shared → 2 (give to b) → 1 (a dropped) → use b.
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2).share;
                    array_initialize[Int](a.give, 0, 10);
                    array_initialize[Int](a.give, 1, 20);
                    let b = a.give;
                    a.drop;
                    array_give[Int](b.give, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Result: 10
            Alloc 0x13: [Int(10)]"#]]
    );
}

#[test]
fn refcount_reaches_zero_frees_allocation() {
    // When the last reference is dropped, the backing allocation is freed.
    // The heap snapshot should show only the result Int — no array allocation.
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2).share;
                    array_initialize[Int](a.give, 0, 10);
                    array_initialize[Int](a.give, 1, 20);
                    let b = a.give;
                    a.drop;
                    b.drop;
                    42;
                }
            }
        },
        expect_test::expect![[r#"
            Result: 42
            Alloc 0x12: [Int(42)]"#]]
    );
}

#[test]
fn nested_array_in_class_field() {
    // A class with an Array[Int] field — dropping the class
    // recursively drops the array (decrements refcount to 0).
    crate::assert_interpret_only!(
        {
            class Wrapper {
                items: Array[Int];
            }
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](1);
                    array_initialize[Int](a.ref, 0, 99);
                    let w = new Wrapper(a.give);
                    w.drop;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Result: 0
            Alloc 0x0e: [Int(0)]"#]]
    );
}

// ---------------------------------------------------------------
// Element type variations
// ---------------------------------------------------------------

#[test]
fn array_of_shared_class_elements() {
    // shared class elements have no flags word per element.
    crate::assert_interpret_only!(
        {
            shared class Pt { x: Int; y: Int; }
            class Main {
                fn main(given self) -> Pt {
                    let a = array_new[Pt](2).share;
                    array_initialize[Pt](a.give, 0, new Pt(1, 2));
                    array_initialize[Pt](a.give, 1, new Pt(3, 4));
                    print(array_give[Pt](a.give, 0));
                    array_give[Pt](a.give, 1);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Pt { x: 1, y: 2 }
            Result: Pt { x: 3, y: 4 }
            Alloc 0x18: [Int(3), Int(4)]"#]]
    );
}

#[test]
fn array_of_class_recursive_drop() {
    // Array of class with a nested field — dropping the array
    // should recursively drop each class element's fields.
    crate::assert_interpret_only!(
        {
            class Inner { value: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Outer](2).share;
                    array_initialize[Outer](a.give, 0, new Outer(new Inner(1)));
                    array_initialize[Outer](a.give, 1, new Outer(new Inner(2)));
                    a.drop;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Result: 0
            Alloc 0x13: [Int(0)]"#]]
    );
}

// ---------------------------------------------------------------
// ArrayDrop paths
// ---------------------------------------------------------------

#[test]
fn array_drop_out_of_bounds() {
    crate::assert_interpret_fault!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_drop[Int](a.give, 5);
                    0;
                }
            }
        },
        "out of bounds"
    );
}

#[test]
fn array_drop_uninitialized_faults() {
    crate::assert_interpret_fault!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_drop[Int](a.give, 0);
                    0;
                }
            }
        },
        "uninitialized"
    );
}

// ---------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------

#[test]
fn array_new_zero_length() {
    // Zero-length array: capacity is 0, any access is out of bounds.
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](0);
                    array_capacity[Int](a.give);
                }
            }
        },
        expect_test::expect![[r#"
            Result: 0
            Alloc 0x07: [Int(0)]"#]]
    );
}

#[test]
fn array_zero_length_access_faults() {
    crate::assert_interpret_fault!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](0);
                    array_give[Int](a.give, 0);
                }
            }
        },
        "out of bounds"
    );
}

// ---------------------------------------------------------------
// Given array operations
// ---------------------------------------------------------------

#[test]
fn given_array_give_moves() {
    // A Given array (not shared) — giving it moves the whole array.
    // The original becomes uninitialized.
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_initialize[Int](a.ref, 0, 10);
                    array_initialize[Int](a.ref, 1, 20);
                    let b = a.give;
                    array_give[Int](b.give, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Result: 10
            Alloc 0x12: [Int(10)]"#]]
    );
}

#[test]
fn given_array_double_give_faults() {
    // A Given array can only be given once — second give faults.
    crate::assert_interpret_fault!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](1);
                    let b = a.give;
                    let c = a.give;
                    0;
                }
            }
        },
        "uninitialized"
    );
}

// ---------------------------------------------------------------
// convert_to_shared on array inside class
// ---------------------------------------------------------------

#[test]
fn share_class_containing_array() {
    // Sharing a class that contains an Array field should
    // set the class's flags to Shared. The array inside keeps
    // its runtime flags — share semantics are enforced by the type system.
    crate::assert_interpret_only!(
        {
            class Container {
                items: Array[Int];
            }
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_initialize[Int](a.ref, 0, 1);
                    array_initialize[Int](a.ref, 1, 2);
                    let c = new Container(a.give);
                    let s = c.give.share;
                    print(s.give);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: shared Container { flag: Shared, items: Array { flag: Given, 1, 2 } }
            Result: 0
            Alloc 0x15: [Int(0)]"#]]
    );
}

// ---------------------------------------------------------------
// Display
// ---------------------------------------------------------------

#[test]
fn array_display() {
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](3).share;
                    array_initialize[Int](a.give, 0, 10);
                    array_initialize[Int](a.give, 1, 20);
                    array_initialize[Int](a.give, 2, 30);
                    print(a.give);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: shared Array { flag: Shared, 10, 20, 30 }
            Result: 0
            Alloc 0x14: [Int(0)]"#]]
    );
}
