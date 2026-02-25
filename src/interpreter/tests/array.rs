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
        return "3"
    );
}

#[test]
fn array_size_of() {
    // Array[T] is a single word (Word::Array with embedded flags)
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    size_of[Array[Int]]();
                }
            }
        },
        return "1"
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
        print "10",
        print "20",
        return "30"
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
        print "Data { flag: Given, x: 42 }",
        return "Data { flag: Given, x: 99 }"
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
        return "0"
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
        return "1"
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
        return "10"
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
        return "30"
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
        print "Array { flag: Shared, 10, 20, 30 }",
        return "0"
    );
}
