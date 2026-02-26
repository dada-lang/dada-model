// Tests for Array[T] operations: ArrayNew, ArrayCapacity, ArrayGet, ArrayDrop, ArrayInitialize.
//
// All tests use assert_interpret_only! since the type checker's Array rules
// are simplified stubs — the real typing (e.g., ArrayGet returning given[array] T)
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
                    print(array_get[Int](a.give, 0));
                    print(array_get[Int](a.give, 1));
                    array_get[Int](a.give, 2);
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
                    print(array_get[Data](a.give, 0));
                    array_get[Data](a.give, 1);
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
fn array_get_uninitialized_faults() {
    crate::assert_interpret_fault!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](3);
                    array_get[Int](a.give, 0);
                }
            }
        },
        "element is uninitialized"
    );
}

#[test]
fn array_get_after_get_faults() {
    // Getting an element moves it out — getting again should fault.
    crate::assert_interpret_fault!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2).share;
                    array_initialize[Int](a.give, 0, 42);
                    let x = array_get[Int](a.give, 0);
                    array_get[Int](a.give, 0);
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
fn array_get_out_of_bounds() {
    crate::assert_interpret_fault!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_get[Int](a.give, 5);
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
                    array_get[Int](a.give, 0);
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
                    array_get[Int](b.give, 0);
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
                    let x = array_get[Int](a.give, 0);
                    let y = array_get[Int](a.give, 1);
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
