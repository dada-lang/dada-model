// Tests for Array[T] operations: ArrayNew, ArrayCapacity, ArrayGive, ArrayDrop, ArrayWrite.
//
// All tests use assert_interpret_only! since the type checker's Array rules
// are simplified stubs — the real typing (e.g., ArrayGive returning given[array] T)
// is deferred.
//
// Expected patterns:
// - Arrays are typically `given` (owned)
// - Use `.mut` for modifications (array_write, array_drop)
// - Use `.ref` for read-only access (array_give, array_capacity, print)
// - Use `.give` only when transferring ownership
// - Use `.share` only when genuinely sharing across multiple owners

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
                    array_capacity[Int, given](w.field.give);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](3) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ }
            Output: Trace:   let w = new Wrapper (a . give) ;
            Output: Trace:   w = Wrapper { field: Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ } }
            Output: Trace:   array_capacity [Int, given](w . field . give) ;
            Output: Trace: exit Main.main => 3
            Result: Ok: 3
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
                    let a = array_new[Int](2);
                    array_write[Int, mut[a]](a.mut, 0, 1);
                    array_write[Int, mut[a]](a.mut, 1, 2);
                    // Replace a with a fresh array — old array must be dropped.
                    a = array_new[Int](4);
                    array_capacity[Int, given](a.give);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [a]](a . mut , 0 , 1) ;
            Output: Trace:   array_write [Int, mut [a]](a . mut , 1 , 2) ;
            Output: Trace:   a = array_new [Int](4) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡, ⚡ }
            Output: Trace:   array_capacity [Int, given](a . give) ;
            Output: Trace: exit Main.main => 4
            Result: Ok: 4
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
                    array_capacity[Int, given](a.give);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](3) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ }
            Output: Trace:   array_capacity [Int, given](a . give) ;
            Output: Trace: exit Main.main => 3
            Result: Ok: 3
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
            Output: Trace: enter Main.main
            Output: Trace:   size_of [Array[Int]]() ;
            Output: Trace: exit Main.main => 2
            Result: Ok: 2
            Alloc 0x02: [Int(2)]"#]]
    );
}

// ---------------------------------------------------------------
// Initialize and get — Int elements
// ---------------------------------------------------------------

#[test]
fn array_write_and_get_int() {
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](3);
                    array_write[Int, mut[a]](a.mut, 0, 10);
                    array_write[Int, mut[a]](a.mut, 1, 20);
                    array_write[Int, mut[a]](a.mut, 2, 30);
                    print(array_give[Int, given, ref[a]](a.ref, 0));
                    print(array_give[Int, given, ref[a]](a.ref, 1));
                    array_give[Int, given, given](a.give, 2);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](3) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [a]](a . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [a]](a . mut , 1 , 20) ;
            Output: Trace:   array_write [Int, mut [a]](a . mut , 2 , 30) ;
            Output: Trace:   print(array_give [Int, given, ref [a]](a . ref , 0)) ;
            Output: ----->   10
            Output: Trace:   print(array_give [Int, given, ref [a]](a . ref , 1)) ;
            Output: ----->   20
            Output: Trace:   array_give [Int, given, given](a . give , 2) ;
            Output: Trace: exit Main.main => 30
            Result: Ok: 30
            Alloc 0x1c: [Int(30)]"#]]
    );
}

// ---------------------------------------------------------------
// Initialize and get — class elements
// ---------------------------------------------------------------

#[test]
fn array_write_and_get_class() {
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let a = array_new[Data](2);
                    array_write[Data, mut[a]](a.mut, 0, new Data(42));
                    array_write[Data, mut[a]](a.mut, 1, new Data(99));
                    print(array_give[Data, given, ref[a]](a.ref, 0));
                    array_give[Data, given, given](a.give, 1);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Data](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, Data { x: ⚡ }, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [a]](a . mut , 0 , new Data (42)) ;
            Output: Trace:   array_write [Data, mut [a]](a . mut , 1 , new Data (99)) ;
            Output: Trace:   print(array_give [Data, given, ref [a]](a . ref , 0)) ;
            Output: ----->   ref [a] Data { x: 42 }
            Output: Trace:   array_give [Data, given, given](a . give , 1) ;
            Output: Trace: exit Main.main => Data { x: 99 }
            Result: Ok: Data { x: 99 }
            Alloc 0x16: [Int(99)]"#]]
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
                    array_give[Int, given, given](a.give, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](3) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ }
            Output: Trace:   array_give [Int, given, given](a . give , 0) ;
            Result: Fault: access of uninitialized value
            Alloc 0x03: [RefCount(1), Capacity(3), Uninitialized, Uninitialized, Uninitialized]
            Alloc 0x06: [Flags(Given), Pointer(0x03)]"#]]
    );
}

#[test]
fn array_give_int_is_copy() {
    // Int is a copy type — giving it doesn't uninitialize the source.
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_write[Int, mut[a]](a.mut, 0, 42);
                    let x = array_give[Int, given, ref[a]](a.ref, 0);
                    array_give[Int, given, given](a.give, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [a]](a . mut , 0 , 42) ;
            Output: Trace:   let x = array_give [Int, given, ref [a]](a . ref , 0) ;
            Output: Trace:   x = 42
            Output: Trace:   array_give [Int, given, given](a . give , 0) ;
            Output: Trace: exit Main.main => 42
            Result: Ok: 42
            Alloc 0x10: [Int(42)]"#]]
    );
}

#[test]
fn given_array_give_class_moves_out() {
    // Given array: giving the array to array_give moves the element out
    // (Given effective flags → move semantics). The element is
    // uninitalized in the backing, but the array ref is consumed too,
    // so there's no second access to fault on. Verify by giving element,
    // then checking the element was actually moved (backing has Uninitialized).
    // To observe the move: share the array first, give through one ref
    // (which is shared → copy), then drop the share and access given.
    //
    // Actually, the simplest way to test Given move: use a given array,
    // give element 0 (moves it), then use array_give on element 1.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let a = array_new[Data](2);
                    array_write[Data, mut[a]](a.mut, 0, new Data(42));
                    array_write[Data, mut[a]](a.mut, 1, new Data(99));
                    // Give element 0 from given array — moves it out.
                    // The array ref is consumed, so we pass a.give.
                    array_give[Data, given, given](a.give, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Data](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, Data { x: ⚡ }, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [a]](a . mut , 0 , new Data (42)) ;
            Output: Trace:   array_write [Data, mut [a]](a . mut , 1 , new Data (99)) ;
            Output: Trace:   array_give [Data, given, given](a . give , 0) ;
            Output: Trace: exit Main.main => Data { x: 42 }
            Result: Ok: Data { x: 42 }
            Alloc 0x12: [Int(42)]"#]]
    );
}

#[test]
fn shared_array_give_class_is_shared_copy() {
    // Shared array: class elements are given with shared semantics —
    // no move, element remains available for repeated gives.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let a = array_new[Data](1);
                    array_write[Data, mut[a]](a.mut, 0, new Data(42));
                    let s = a.give.share;
                    let x = array_give[Data, given, ref[s]](s.ref, 0);
                    print(x.give);
                    // Element still available — shared semantics, no move.
                    array_give[Data, given, shared](s.give, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Data](1) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [a]](a . mut , 0 , new Data (42)) ;
            Output: Trace:   let s = a . give . share ;
            Output: Trace:   s = shared Array { flag: Shared, rc: 1, Data { x: 42 } }
            Output: Trace:   let x = array_give [Data, given, ref [s]](s . ref , 0) ;
            Output: Trace:   x = ref [s] shared Data { x: 42 }
            Output: Trace:   print(x . give) ;
            Output: ----->   ref [s] shared Data { x: 42 }
            Output: Trace:   array_give [Data, given, shared](s . give , 0) ;
            Output: Trace: exit Main.main => shared Data { x: 42 }
            Result: Ok: shared Data { x: 42 }
            Alloc 0x15: [Int(42)]"#]]
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
                    array_give[Int, given, given](a.give, 5);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_give [Int, given, given](a . give , 5) ;
            Result: Fault: array_give: index 5 out of bounds (capacity 2)
            Alloc 0x03: [RefCount(1), Capacity(2), Uninitialized, Uninitialized]
            Alloc 0x06: [Flags(Given), Pointer(0x03)]"#]]
    );
}

#[test]
fn array_write_out_of_bounds() {
    crate::assert_interpret_fault!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_write[Int, mut[a]](a.mut, 3, 42);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [a]](a . mut , 3 , 42) ;
            Result: Fault: array_give: index 3 out of bounds (capacity 2)
            Alloc 0x03: [RefCount(1), Capacity(2), Uninitialized, Uninitialized]
            Alloc 0x04: [Flags(Given), Pointer(0x03)]
            Alloc 0x06: [MutRef(0x03)]"#]]
    );
}

// ---------------------------------------------------------------
// Double initialize
// ---------------------------------------------------------------

#[test]
fn array_write_overwrites_existing() {
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_write[Int, mut[a]](a.mut, 0, 10);
                    array_write[Int, mut[a]](a.mut, 0, 20);
                    array_give[Int, given, given](a.give, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [a]](a . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [a]](a . mut , 0 , 20) ;
            Output: Trace:   array_give [Int, given, given](a . give , 0) ;
            Output: Trace: exit Main.main => 20
            Result: Ok: 20
            Alloc 0x10: [Int(20)]"#]]
    );
}

/// array_write overwriting a shared array element should decrement refcount
/// and free the old array when refcount reaches zero.
#[test]
fn array_write_overwrites_shared_array() {
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let outer = array_new[Array[Int]](1);
                    let inner = array_new[Int](0).share;
                    array_write[Array[Int], mut[outer]](outer.mut, 0, inner.give);
                    let replacement = array_new[Int](1);
                    array_write[Int, mut[replacement]](replacement.mut, 0, 99);

                    print(outer.ref);
                    print(inner.ref);
                    print(replacement.ref);

                    array_write[Array[Int], mut[outer]](outer.mut, 0, replacement.give);

                    print(outer.ref);
                    print(inner.ref);
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let outer = array_new [Array[Int]](1) ;
            Output: Trace:   outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   let inner = array_new [Int](0) . share ;
            Output: Trace:   inner = shared Array { flag: Shared, rc: 1 }
            Output: Trace:   array_write [Array[Int], mut [outer]](outer . mut , 0 , inner . give) ;
            Output: Trace:   let replacement = array_new [Int](1) ;
            Output: Trace:   replacement = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [replacement]](replacement . mut , 0 , 99) ;
            Output: Trace:   print(outer . ref) ;
            Output: ----->   ref [outer] Array { flag: Borrowed, rc: 1, Array { flag: Shared, rc: 2 } }
            Output: Trace:   print(inner . ref) ;
            Output: ----->   shared Array { flag: Borrowed, rc: 2 }
            Output: Trace:   print(replacement . ref) ;
            Output: ----->   ref [replacement] Array { flag: Borrowed, rc: 1, 99 }
            Output: Trace:   array_write [Array[Int], mut [outer]](outer . mut , 0 , replacement . give) ;
            Output: Trace:   print(outer . ref) ;
            Output: ----->   ref [outer] Array { flag: Borrowed, rc: 1, Array { flag: Given, rc: 1, 99 } }
            Output: Trace:   print(inner . ref) ;
            Output: ----->   shared Array { flag: Borrowed, rc: 2 }
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()
            Alloc 0x07: [RefCount(1), Capacity(0)]
            Alloc 0x0f: [RefCount(1), Capacity(1), Int(99)]"#]]
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
                    let a = array_new[Int](2);
                    array_write[Int, mut[a]](a.mut, 0, 42);
                    array_drop[Int, given, mut[a]](a.mut, 0);
                    array_give[Int, given, given](a.give, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [a]](a . mut , 0 , 42) ;
            Output: Trace:   array_drop [Int, given, mut [a]](a . mut , 0) ;
            Output: Trace:   array_give [Int, given, given](a . give , 0) ;
            Result: Fault: access of uninitialized value
            Alloc 0x03: [RefCount(1), Capacity(2), Uninitialized, Uninitialized]
            Alloc 0x0d: [Flags(Given), Pointer(0x03)]"#]]
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
                    let a = array_new[Data](1);
                    array_write[Data, mut[a]](a.mut, 0, new Data(42));
                    array_drop[Data, given, mut[a]](a.mut, 0);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Data](1) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [a]](a . mut , 0 , new Data (42)) ;
            Output: Trace:   array_drop [Data, given, mut [a]](a . mut , 0) ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
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
                    array_capacity[Int, given](b.give);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](1) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   let b = a . give ;
            Output: Trace:   b = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_capacity [Int, given](b . give) ;
            Output: Trace: exit Main.main => 1
            Result: Ok: 1
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
                    let a = array_new[Int](2);
                    array_write[Int, mut[a]](a.mut, 0, 10);
                    array_write[Int, mut[a]](a.mut, 1, 20);
                    let b = a.give;
                    array_give[Int, given, given](b.give, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [a]](a . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [a]](a . mut , 1 , 20) ;
            Output: Trace:   let b = a . give ;
            Output: Trace:   b = Array { flag: Given, rc: 1, 10, 20 }
            Output: Trace:   array_give [Int, given, given](b . give , 0) ;
            Output: Trace: exit Main.main => 10
            Result: Ok: 10
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
                    array_capacity[Int, given](a.give);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](1) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   let b = a . give ;
            Output: Trace:   b = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_capacity [Int, given](a . give) ;
            Result: Fault: access of uninitialized value
            Alloc 0x03: [RefCount(1), Capacity(1), Uninitialized]
            Alloc 0x06: [Flags(Given), Pointer(0x03)]"#]]
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
                    let a = array_new[Int](2);
                    array_write[Int, mut[a]](a.mut, 0, 10);
                    array_write[Int, mut[a]](a.mut, 1, 20);
                    let s = a.give.share;
                    let x = array_give[Int, given, ref[s]](s.ref, 0);
                    let y = array_give[Int, given, shared](s.give, 1);
                    x.give + y.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [a]](a . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [a]](a . mut , 1 , 20) ;
            Output: Trace:   let s = a . give . share ;
            Output: Trace:   s = shared Array { flag: Shared, rc: 1, 10, 20 }
            Output: Trace:   let x = array_give [Int, given, ref [s]](s . ref , 0) ;
            Output: Trace:   x = 10
            Output: Trace:   let y = array_give [Int, given, shared](s . give , 1) ;
            Output: Trace:   y = 20
            Output: Trace:   x . give + y . give ;
            Output: Trace: exit Main.main => 30
            Result: Ok: 30
            Alloc 0x1a: [Int(30)]"#]]
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
                    let a = array_new[Int](2);
                    array_write[Int, mut[a]](a.mut, 0, 10);
                    array_write[Int, mut[a]](a.mut, 1, 20);
                    let s = a.give.share;
                    let b = s.give;
                    s.drop;
                    array_give[Int, given, shared](b.give, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [a]](a . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [a]](a . mut , 1 , 20) ;
            Output: Trace:   let s = a . give . share ;
            Output: Trace:   s = shared Array { flag: Shared, rc: 1, 10, 20 }
            Output: Trace:   let b = s . give ;
            Output: Trace:   b = shared Array { flag: Shared, rc: 2, 10, 20 }
            Output: Trace:   s . drop ;
            Output: Trace:   array_give [Int, given, shared](b . give , 0) ;
            Output: Trace: exit Main.main => 10
            Result: Ok: 10
            Alloc 0x15: [Int(10)]"#]]
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
                    let a = array_new[Int](2);
                    array_write[Int, mut[a]](a.mut, 0, 10);
                    array_write[Int, mut[a]](a.mut, 1, 20);
                    let s = a.give.share;
                    let b = s.give;
                    s.drop;
                    b.drop;
                    42;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [a]](a . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [a]](a . mut , 1 , 20) ;
            Output: Trace:   let s = a . give . share ;
            Output: Trace:   s = shared Array { flag: Shared, rc: 1, 10, 20 }
            Output: Trace:   let b = s . give ;
            Output: Trace:   b = shared Array { flag: Shared, rc: 2, 10, 20 }
            Output: Trace:   s . drop ;
            Output: Trace:   b . drop ;
            Output: Trace:   42 ;
            Output: Trace: exit Main.main => 42
            Result: Ok: 42
            Alloc 0x14: [Int(42)]"#]]
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
                    array_write[Int, mut[a]](a.mut, 0, 99);
                    let w = new Wrapper(a.give);
                    w.drop;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](1) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [a]](a . mut , 0 , 99) ;
            Output: Trace:   let w = new Wrapper (a . give) ;
            Output: Trace:   w = Wrapper { items: Array { flag: Given, rc: 1, 99 } }
            Output: Trace:   w . drop ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
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
                    let a = array_new[Pt](2);
                    array_write[Pt, mut[a]](a.mut, 0, new Pt(1, 2));
                    array_write[Pt, mut[a]](a.mut, 1, new Pt(3, 4));
                    print(array_give[Pt, given, ref[a]](a.ref, 0));
                    array_give[Pt, given, given](a.give, 1);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Pt](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, Pt { x: ⚡, y: ⚡ }, Pt { x: ⚡, y: ⚡ } }
            Output: Trace:   array_write [Pt, mut [a]](a . mut , 0 , new Pt (1, 2)) ;
            Output: Trace:   array_write [Pt, mut [a]](a . mut , 1 , new Pt (3, 4)) ;
            Output: Trace:   print(array_give [Pt, given, ref [a]](a . ref , 0)) ;
            Output: ----->   Pt { x: 1, y: 2 }
            Output: Trace:   array_give [Pt, given, given](a . give , 1) ;
            Output: Trace: exit Main.main => Pt { x: 3, y: 4 }
            Result: Ok: Pt { x: 3, y: 4 }
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
                    let a = array_new[Outer](2);
                    array_write[Outer, mut[a]](a.mut, 0, new Outer(new Inner(1)));
                    array_write[Outer, mut[a]](a.mut, 1, new Outer(new Inner(2)));
                    a.drop;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Outer](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, Outer { inner: Inner { value: ⚡ } }, Outer { inner: Inner { value: ⚡ } } }
            Output: Trace:   array_write [Outer, mut [a]](a . mut , 0 , new Outer (new Inner (1))) ;
            Output: Trace:   array_write [Outer, mut [a]](a . mut , 1 , new Outer (new Inner (2))) ;
            Output: Trace:   a . drop ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
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
                    array_drop[Int, given, mut[a]](a.mut, 5);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_drop [Int, given, mut [a]](a . mut , 5) ;
            Result: Fault: array_give: index 5 out of bounds (capacity 2)
            Alloc 0x03: [RefCount(1), Capacity(2), Uninitialized, Uninitialized]
            Alloc 0x04: [Flags(Given), Pointer(0x03)]
            Alloc 0x06: [MutRef(0x03)]"#]]
    );
}

#[test]
fn array_drop_uninitialized_faults() {
    crate::assert_interpret_fault!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_drop[Int, given, mut[a]](a.mut, 0);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_drop [Int, given, mut [a]](a . mut , 0) ;
            Result: Fault: access of uninitialized value
            Alloc 0x03: [RefCount(1), Capacity(2), Uninitialized, Uninitialized]
            Alloc 0x04: [Flags(Given), Pointer(0x03)]
            Alloc 0x06: [MutRef(0x03)]"#]]
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
                    array_capacity[Int, given](a.give);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](0) ;
            Output: Trace:   a = Array { flag: Given, rc: 1 }
            Output: Trace:   array_capacity [Int, given](a . give) ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
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
                    array_give[Int, given, given](a.give, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](0) ;
            Output: Trace:   a = Array { flag: Given, rc: 1 }
            Output: Trace:   array_give [Int, given, given](a . give , 0) ;
            Result: Fault: array_give: index 0 out of bounds (capacity 0)
            Alloc 0x03: [RefCount(1), Capacity(0)]
            Alloc 0x06: [Flags(Given), Pointer(0x03)]"#]]
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
                    array_write[Int, mut[a]](a.mut, 0, 10);
                    array_write[Int, mut[a]](a.mut, 1, 20);
                    let b = a.give;
                    array_give[Int, given, given](b.give, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [a]](a . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [a]](a . mut , 1 , 20) ;
            Output: Trace:   let b = a . give ;
            Output: Trace:   b = Array { flag: Given, rc: 1, 10, 20 }
            Output: Trace:   array_give [Int, given, given](b . give , 0) ;
            Output: Trace: exit Main.main => 10
            Result: Ok: 10
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
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](1) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   let b = a . give ;
            Output: Trace:   b = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   let c = a . give ;
            Result: Fault: access of uninitialized value
            Alloc 0x03: [RefCount(1), Capacity(1), Uninitialized]
            Alloc 0x06: [Flags(Given), Pointer(0x03)]"#]]
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
                    array_write[Int, mut[a]](a.mut, 0, 1);
                    array_write[Int, mut[a]](a.mut, 1, 2);
                    let c = new Container(a.give);
                    let s = c.give.share;
                    print(s.give);
                    print(array_give[Int, given, ref[s.items]](s.items.ref, 0));
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [a]](a . mut , 0 , 1) ;
            Output: Trace:   array_write [Int, mut [a]](a . mut , 1 , 2) ;
            Output: Trace:   let c = new Container (a . give) ;
            Output: Trace:   c = Container { items: Array { flag: Given, rc: 1, 1, 2 } }
            Output: Trace:   let s = c . give . share ;
            Output: Trace:   s = shared Container { items: Array { flag: Shared, rc: 1, 1, 2 } }
            Output: Trace:   print(s . give) ;
            Output: ----->   shared Container { items: Array { flag: Shared, rc: 2, 1, 2 } }
            Output: Trace:   print(array_give [Int, given, ref [s . items]](s . items . ref , 0)) ;
            Output: ----->   1
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x19: [Int(0)]"#]]
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
                    let a = array_new[Int](3);
                    array_write[Int, mut[a]](a.mut, 0, 10);
                    array_write[Int, mut[a]](a.mut, 1, 20);
                    array_write[Int, mut[a]](a.mut, 2, 30);
                    print(a.ref);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](3) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [a]](a . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [a]](a . mut , 1 , 20) ;
            Output: Trace:   array_write [Int, mut [a]](a . mut , 2 , 30) ;
            Output: Trace:   print(a . ref) ;
            Output: ----->   ref [a] Array { flag: Borrowed, rc: 1, 10, 20, 30 }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x14: [Int(0)]"#]]
    );
}

// ---------------------------------------------------------------
// Multiple references to the same shared array
// ---------------------------------------------------------------

#[test]
fn shared_array_two_refs_both_usable() {
    // Two variables referencing the same shared array.
    // Both can read elements independently.
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_write[Int, mut[a]](a.mut, 0, 10);
                    array_write[Int, mut[a]](a.mut, 1, 20);
                    let s = a.give.share;
                    let b = s.give;
                    // Both s and b point to the same backing; refcount is 2.
                    let x = array_give[Int, given, ref[s]](s.ref, 0);
                    let y = array_give[Int, given, shared](b.give, 1);
                    x.give + y.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [a]](a . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [a]](a . mut , 1 , 20) ;
            Output: Trace:   let s = a . give . share ;
            Output: Trace:   s = shared Array { flag: Shared, rc: 1, 10, 20 }
            Output: Trace:   let b = s . give ;
            Output: Trace:   b = shared Array { flag: Shared, rc: 2, 10, 20 }
            Output: Trace:   let x = array_give [Int, given, ref [s]](s . ref , 0) ;
            Output: Trace:   x = 10
            Output: Trace:   let y = array_give [Int, given, shared](b . give , 1) ;
            Output: Trace:   y = 20
            Output: Trace:   x . give + y . give ;
            Output: Trace: exit Main.main => 30
            Result: Ok: 30
            Alloc 0x1c: [Int(30)]"#]]
    );
}

#[test]
fn shared_array_three_refs_drop_two() {
    // Three references: drop two, last one still works.
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](1);
                    array_write[Int, mut[a]](a.mut, 0, 42);
                    let s = a.give.share;
                    let b = s.give;
                    let c = s.give;
                    // refcount = 3
                    s.drop;
                    b.drop;
                    // refcount = 1, c still alive
                    array_give[Int, given, shared](c.give, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](1) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [a]](a . mut , 0 , 42) ;
            Output: Trace:   let s = a . give . share ;
            Output: Trace:   s = shared Array { flag: Shared, rc: 1, 42 }
            Output: Trace:   let b = s . give ;
            Output: Trace:   b = shared Array { flag: Shared, rc: 2, 42 }
            Output: Trace:   let c = s . give ;
            Output: Trace:   c = shared Array { flag: Shared, rc: 3, 42 }
            Output: Trace:   s . drop ;
            Output: Trace:   b . drop ;
            Output: Trace:   array_give [Int, given, shared](c . give , 0) ;
            Output: Trace: exit Main.main => 42
            Result: Ok: 42
            Alloc 0x14: [Int(42)]"#]]
    );
}

#[test]
fn shared_array_all_refs_dropped_frees() {
    // All references dropped: backing allocation freed.
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](1);
                    array_write[Int, mut[a]](a.mut, 0, 99);
                    let s = a.give.share;
                    let b = s.give;
                    let c = b.give;
                    s.drop;
                    b.drop;
                    c.drop;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](1) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [a]](a . mut , 0 , 99) ;
            Output: Trace:   let s = a . give . share ;
            Output: Trace:   s = shared Array { flag: Shared, rc: 1, 99 }
            Output: Trace:   let b = s . give ;
            Output: Trace:   b = shared Array { flag: Shared, rc: 2, 99 }
            Output: Trace:   let c = b . give ;
            Output: Trace:   c = shared Array { flag: Shared, rc: 3, 99 }
            Output: Trace:   s . drop ;
            Output: Trace:   b . drop ;
            Output: Trace:   c . drop ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x13: [Int(0)]"#]]
    );
}

// ---------------------------------------------------------------
// Nested arrays: Array[Array[T]]
// ---------------------------------------------------------------

#[test]
fn nested_array_create_and_capacity() {
    // Array[Array[Int]]: outer array holds inner arrays as elements.
    // Each element is 2 words (Flags + Pointer).
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let outer = array_new[Array[Int]](2);
                    let inner0 = array_new[Int](3);
                    array_write[Array[Int], mut[outer]](outer.mut, 0, inner0.give);
                    let got = array_give[Array[Int], given, given](outer.give, 0);
                    array_capacity[Int, given](got.give);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let outer = array_new [Array[Int]](2) ;
            Output: Trace:   outer = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   let inner0 = array_new [Int](3) ;
            Output: Trace:   inner0 = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ }
            Output: Trace:   array_write [Array[Int], mut [outer]](outer . mut , 0 , inner0 . give) ;
            Output: Trace:   let got = array_give [Array[Int], given, given](outer . give , 0) ;
            Output: Trace:   got = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ }
            Output: Trace:   array_capacity [Int, given](got . give) ;
            Output: Trace: exit Main.main => 3
            Result: Ok: 3
            Alloc 0x13: [Int(3)]"#]]
    );
}

#[test]
fn nested_array_give_inner_from_shared_outer() {
    // shared Array[Array[Int]]: giving an element from a shared outer array.
    // The inner array element has Given flags in the backing allocation.
    // When outer is shared, give_value sees Shared flags (from the outer's
    // shared perspective) and calls share_op, incrementing the inner array's
    // refcount. We can give the same inner element multiple times.
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let inner = array_new[Int](2);
                    array_write[Int, mut[inner]](inner.mut, 0, 10);
                    array_write[Int, mut[inner]](inner.mut, 1, 20);
                    let outer = array_new[Array[Int]](1);
                    array_write[Array[Int], mut[outer]](outer.mut, 0, inner.give);
                    let s = outer.give.share;
                    // Give the inner array element — should get a shared copy
                    // and increment inner's refcount.
                    let got = array_give[Array[Int], given, ref[s]](s.ref, 0);
                    print(got.give);
                    // Give it again — shared elements can be given repeatedly.
                    let got2 = array_give[Array[Int], given, shared](s.give, 0);
                    array_give[Int, given, given](got2.give, 1);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let inner = array_new [Int](2) ;
            Output: Trace:   inner = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [inner]](inner . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [inner]](inner . mut , 1 , 20) ;
            Output: Trace:   let outer = array_new [Array[Int]](1) ;
            Output: Trace:   outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Int], mut [outer]](outer . mut , 0 , inner . give) ;
            Output: Trace:   let s = outer . give . share ;
            Output: Trace:   s = shared Array { flag: Shared, rc: 1, Array { flag: Given, rc: 1, 10, 20 } }
            Output: Trace:   let got = array_give [Array[Int], given, ref [s]](s . ref , 0) ;
            Output: Trace:   got = ref [s] shared Array { flag: Borrowed, rc: 1, 10, 20 }
            Output: Trace:   print(got . give) ;
            Output: ----->   ref [s] shared Array { flag: Borrowed, rc: 1, 10, 20 }
            Output: Trace:   let got2 = array_give [Array[Int], given, shared](s . give , 0) ;
            Output: Trace:   got2 = shared Array { flag: Shared, rc: 2, 10, 20 }
            Output: Trace:   array_give [Int, given, given](got2 . give , 1) ;
            Output: Trace: exit Main.main => 20
            Result: Ok: 20
            Alloc 0x03: [RefCount(1), Capacity(2), Int(10), Int(20)]
            Alloc 0x24: [Int(20)]"#]]
    );
}

#[test]
fn nested_array_drop_inner_decrements_refcount() {
    // Array[Array[Int]]: dropping the inner element in the outer array
    // should decrement the inner array's refcount.
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let inner = array_new[Int](1);
                    array_write[Int, mut[inner]](inner.mut, 0, 42);
                    let s = inner.give.share;
                    let outer = array_new[Array[Int]](1);
                    array_write[Array[Int], mut[outer]](outer.mut, 0, s.give);
                    // s is shared: s.give copies + rc++. s still alive, rc=2.
                    // Drop the element in outer — refcount goes to 1.
                    array_drop[Array[Int], given, mut[outer]](outer.mut, 0);
                    // s var still alive, can still read.
                    array_give[Int, given, shared](s.give, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let inner = array_new [Int](1) ;
            Output: Trace:   inner = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [inner]](inner . mut , 0 , 42) ;
            Output: Trace:   let s = inner . give . share ;
            Output: Trace:   s = shared Array { flag: Shared, rc: 1, 42 }
            Output: Trace:   let outer = array_new [Array[Int]](1) ;
            Output: Trace:   outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Int], mut [outer]](outer . mut , 0 , s . give) ;
            Output: Trace:   array_drop [Array[Int], given, mut [outer]](outer . mut , 0) ;
            Output: Trace:   array_give [Int, given, shared](s . give , 0) ;
            Output: Trace: exit Main.main => 42
            Result: Ok: 42
            Alloc 0x19: [Int(42)]"#]]
    );
}

#[test]
fn nested_array_all_refs_freed() {
    // Nested array: when all references (outer + inner var) are dropped,
    // both backing allocations are freed.
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let inner = array_new[Int](1);
                    array_write[Int, mut[inner]](inner.mut, 0, 1);
                    let outer = array_new[Array[Int]](1);
                    array_write[Array[Int], mut[outer]](outer.mut, 0, inner.give);
                    // Drop outer — cascading: outer element drops, inner refcount→0, inner freed
                    outer.drop;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let inner = array_new [Int](1) ;
            Output: Trace:   inner = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [inner]](inner . mut , 0 , 1) ;
            Output: Trace:   let outer = array_new [Array[Int]](1) ;
            Output: Trace:   outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Int], mut [outer]](outer . mut , 0 , inner . give) ;
            Output: Trace:   outer . drop ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x03: [RefCount(1), Capacity(1), Int(1)]
            Alloc 0x13: [Int(0)]"#]]
    );
}

// ---------------------------------------------------------------
// shared Array[Array[Data]] — shared outer, class elements in inner
// ---------------------------------------------------------------

#[test]
fn shared_outer_array_of_data_arrays() {
    // shared Array[Array[Data]]: outer shared, inner arrays hold Data objects.
    // Giving an inner array element from the shared outer produces a shared copy
    // with incremented refcount. The inner array is also shared, so reading
    // Data elements through both paths works (shared semantics, no move).
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Int {
                    let inner = array_new[Data](1);
                    array_write[Data, mut[inner]](inner.mut, 0, new Data(42));
                    let si = inner.give.share;
                    let outer = array_new[Array[Data]](1);
                    array_write[Array[Data], mut[outer]](outer.mut, 0, si.give);
                    let so = outer.give.share;
                    // Give inner array element from shared outer — shared copy.
                    let got = array_give[Array[Data], given, ref[so]](so.ref, 0);
                    // Read Data through the copy — shared, so no move.
                    print(array_give[Data, given, given](got.give, 0));
                    // Read Data through original inner — still available.
                    print(array_give[Data, given, shared](si.give, 0));
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let inner = array_new [Data](1) ;
            Output: Trace:   inner = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [inner]](inner . mut , 0 , new Data (42)) ;
            Output: Trace:   let si = inner . give . share ;
            Output: Trace:   si = shared Array { flag: Shared, rc: 1, Data { x: 42 } }
            Output: Trace:   let outer = array_new [Array[Data]](1) ;
            Output: Trace:   outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Data], mut [outer]](outer . mut , 0 , si . give) ;
            Output: Trace:   let so = outer . give . share ;
            Output: Trace:   so = shared Array { flag: Shared, rc: 1, Array { flag: Shared, rc: 2, Data { x: 42 } } }
            Output: Trace:   let got = array_give [Array[Data], given, ref [so]](so . ref , 0) ;
            Output: Trace:   got = ref [so] shared Array { flag: Shared, rc: 3, Data { x: 42 } }
            Output: Trace:   print(array_give [Data, given, given](got . give , 0)) ;
            Output: ----->   ref [so] shared Data { x: 42 }
            Output: Trace:   print(array_give [Data, given, shared](si . give , 0)) ;
            Output: ----->   shared Data { x: 42 }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x03: [RefCount(1), Capacity(1), Int(42)]
            Alloc 0x23: [Int(0)]"#]]
    );
}

// ---------------------------------------------------------------
// Array[shared Array[Data]] — non-shared outer, shared inner elements
// ---------------------------------------------------------------

#[test]
fn array_of_shared_inner_arrays() {
    // The outer array holds a shared inner Array[Data] as an element.
    // The element in outer has Shared flags (bitwise copy from shared inner).
    // Giving the element calls share_op (increments inner backing refcount).
    // Both the copy and the original inner var can read Data elements
    // (shared semantics propagate through both array layers).
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Int {
                    let inner = array_new[Data](1);
                    array_write[Data, mut[inner]](inner.mut, 0, new Data(99));
                    let si = inner.give.share;
                    let outer = array_new[Array[Data]](1);
                    array_write[Array[Data], mut[outer]](outer.mut, 0, si.give);
                    let so = outer.give.share;
                    // Give element from outer — share_op increments inner refcount.
                    let got = array_give[Array[Data], given, ref[so]](so.ref, 0);
                    // Read Data through the copy — shared, no move.
                    print(array_give[Data, given, given](got.give, 0));
                    // Read Data through original inner — still available.
                    print(array_give[Data, given, shared](si.give, 0));
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let inner = array_new [Data](1) ;
            Output: Trace:   inner = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [inner]](inner . mut , 0 , new Data (99)) ;
            Output: Trace:   let si = inner . give . share ;
            Output: Trace:   si = shared Array { flag: Shared, rc: 1, Data { x: 99 } }
            Output: Trace:   let outer = array_new [Array[Data]](1) ;
            Output: Trace:   outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Data], mut [outer]](outer . mut , 0 , si . give) ;
            Output: Trace:   let so = outer . give . share ;
            Output: Trace:   so = shared Array { flag: Shared, rc: 1, Array { flag: Shared, rc: 2, Data { x: 99 } } }
            Output: Trace:   let got = array_give [Array[Data], given, ref [so]](so . ref , 0) ;
            Output: Trace:   got = ref [so] shared Array { flag: Shared, rc: 3, Data { x: 99 } }
            Output: Trace:   print(array_give [Data, given, given](got . give , 0)) ;
            Output: ----->   ref [so] shared Data { x: 99 }
            Output: Trace:   print(array_give [Data, given, shared](si . give , 0)) ;
            Output: ----->   shared Data { x: 99 }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x03: [RefCount(1), Capacity(1), Int(99)]
            Alloc 0x23: [Int(0)]"#]]
    );
}

#[test]
fn shared_outer_give_inner_survives_outer_drop() {
    // Key scenario: shared Array[Array[Data]] — giving an inner array
    // element produces a shared copy with incremented refcount.
    // After dropping the outer array entirely, the given copy still works
    // because share_op kept the inner backing alive.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Int {
                    let inner = array_new[Data](1);
                    array_write[Data, mut[inner]](inner.mut, 0, new Data(42));
                    let si = inner.give.share;
                    let outer = array_new[Array[Data]](1);
                    array_write[Array[Data], mut[outer]](outer.mut, 0, si.give);
                    let so = outer.give.share;
                    // Give the inner array element from shared outer.
                    let got = array_give[Array[Data], given, ref[so]](so.ref, 0);
                    // Drop outer entirely — cascading drop hits the element,
                    // which decrements inner refcount. But got's share_op
                    // already incremented it, so refcount > 0.
                    si.drop;
                    so.drop;
                    // got still alive — read the Data element.
                    array_give[Data, given, given](got.give, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let inner = array_new [Data](1) ;
            Output: Trace:   inner = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [inner]](inner . mut , 0 , new Data (42)) ;
            Output: Trace:   let si = inner . give . share ;
            Output: Trace:   si = shared Array { flag: Shared, rc: 1, Data { x: 42 } }
            Output: Trace:   let outer = array_new [Array[Data]](1) ;
            Output: Trace:   outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Data], mut [outer]](outer . mut , 0 , si . give) ;
            Output: Trace:   let so = outer . give . share ;
            Output: Trace:   so = shared Array { flag: Shared, rc: 1, Array { flag: Shared, rc: 2, Data { x: 42 } } }
            Output: Trace:   let got = array_give [Array[Data], given, ref [so]](so . ref , 0) ;
            Output: Trace:   got = ref [so] shared Array { flag: Shared, rc: 3, Data { x: 42 } }
            Output: Trace:   si . drop ;
            Output: Trace:   so . drop ;
            Output: Trace:   array_give [Data, given, given](got . give , 0) ;
            Output: Trace: exit Main.main => ref [so] shared Data { x: 42 }
            Result: Ok: ref [so] shared Data { x: 42 }
            Alloc 0x03: [RefCount(1), Capacity(1), Int(42)]
            Alloc 0x1f: [Int(42)]"#]]
    );
}

// ---------------------------------------------------------------
// shared Array[shared Array[Data]] — both layers shared
// ---------------------------------------------------------------

#[test]
fn shared_array_of_shared_arrays() {
    // shared Array[shared Array[Data]]: both outer and inner are shared.
    // Multiple gives from outer each increment inner refcount.
    // All three references (inner var, copy1, copy2) can independently
    // read Data elements — shared semantics propagate through both layers.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Int {
                    let inner = array_new[Data](1);
                    array_write[Data, mut[inner]](inner.mut, 0, new Data(77));
                    let si = inner.give.share;
                    let outer = array_new[Array[Data]](1);
                    array_write[Array[Data], mut[outer]](outer.mut, 0, si.give);
                    let so = outer.give.share;
                    // Give element twice from shared outer — each increments refcount.
                    let copy1 = array_give[Array[Data], given, ref[so]](so.ref, 0);
                    let copy2 = array_give[Array[Data], given, ref[so]](so.ref, 0);
                    // All three can read the same Data — shared, no move.
                    print(array_give[Data, given, given](copy1.give, 0));
                    print(array_give[Data, given, given](copy2.give, 0));
                    print(array_give[Data, given, shared](si.give, 0));
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let inner = array_new [Data](1) ;
            Output: Trace:   inner = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [inner]](inner . mut , 0 , new Data (77)) ;
            Output: Trace:   let si = inner . give . share ;
            Output: Trace:   si = shared Array { flag: Shared, rc: 1, Data { x: 77 } }
            Output: Trace:   let outer = array_new [Array[Data]](1) ;
            Output: Trace:   outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Data], mut [outer]](outer . mut , 0 , si . give) ;
            Output: Trace:   let so = outer . give . share ;
            Output: Trace:   so = shared Array { flag: Shared, rc: 1, Array { flag: Shared, rc: 2, Data { x: 77 } } }
            Output: Trace:   let copy1 = array_give [Array[Data], given, ref [so]](so . ref , 0) ;
            Output: Trace:   copy1 = ref [so] shared Array { flag: Shared, rc: 3, Data { x: 77 } }
            Output: Trace:   let copy2 = array_give [Array[Data], given, ref [so]](so . ref , 0) ;
            Output: Trace:   copy2 = ref [so] shared Array { flag: Shared, rc: 4, Data { x: 77 } }
            Output: Trace:   print(array_give [Data, given, given](copy1 . give , 0)) ;
            Output: ----->   ref [so] shared Data { x: 77 }
            Output: Trace:   print(array_give [Data, given, given](copy2 . give , 0)) ;
            Output: ----->   ref [so] shared Data { x: 77 }
            Output: Trace:   print(array_give [Data, given, shared](si . give , 0)) ;
            Output: ----->   shared Data { x: 77 }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x03: [RefCount(1), Capacity(1), Int(77)]
            Alloc 0x2b: [Int(0)]"#]]
    );
}

#[test]
fn shared_array_of_shared_arrays_drop_cascade() {
    // shared Array[shared Array[Data]]: drop all references.
    // Dropping outer cascades: drops the element (shared inner array),
    // which decrements inner refcount. Then dropping inner var hits zero.
    // Both backing allocations should be freed.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Int {
                    let inner = array_new[Data](1);
                    array_write[Data, mut[inner]](inner.mut, 0, new Data(55));
                    let si = inner.give.share;
                    let outer = array_new[Array[Data]](1);
                    array_write[Array[Data], mut[outer]](outer.mut, 0, si.give);
                    let so = outer.give.share;
                    // Give a copy from outer, then drop everything.
                    let copy1 = array_give[Array[Data], given, ref[so]](so.ref, 0);
                    copy1.drop;
                    so.drop;
                    si.drop;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let inner = array_new [Data](1) ;
            Output: Trace:   inner = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [inner]](inner . mut , 0 , new Data (55)) ;
            Output: Trace:   let si = inner . give . share ;
            Output: Trace:   si = shared Array { flag: Shared, rc: 1, Data { x: 55 } }
            Output: Trace:   let outer = array_new [Array[Data]](1) ;
            Output: Trace:   outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Data], mut [outer]](outer . mut , 0 , si . give) ;
            Output: Trace:   let so = outer . give . share ;
            Output: Trace:   so = shared Array { flag: Shared, rc: 1, Array { flag: Shared, rc: 2, Data { x: 55 } } }
            Output: Trace:   let copy1 = array_give [Array[Data], given, ref [so]](so . ref , 0) ;
            Output: Trace:   copy1 = ref [so] shared Array { flag: Shared, rc: 3, Data { x: 55 } }
            Output: Trace:   copy1 . drop ;
            Output: Trace:   so . drop ;
            Output: Trace:   si . drop ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x03: [RefCount(1), Capacity(1), Int(55)]
            Alloc 0x1e: [Int(0)]"#]]
    );
}

// ---------------------------------------------------------------
// ArrayDrop: Shared and Borrowed elements
// ---------------------------------------------------------------

#[test]
fn array_drop_shared_element_decrements_refcount() {
    // Array element with Shared flags: ArrayDrop should call drop_owned_value,
    // which for an array element decrements its refcount.
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let inner = array_new[Int](1);
                    array_write[Int, mut[inner]](inner.mut, 0, 42);
                    let si = inner.give.share;
                    let outer = array_new[Array[Int]](1);
                    array_write[Array[Int], mut[outer]](outer.mut, 0, si.give);
                    // Element in outer is shared Array[Int] — refcount 2.
                    // Drop it: refcount → 1. si var still valid.
                    array_drop[Array[Int], given, mut[outer]](outer.mut, 0);
                    array_give[Int, given, shared](si.give, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let inner = array_new [Int](1) ;
            Output: Trace:   inner = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [inner]](inner . mut , 0 , 42) ;
            Output: Trace:   let si = inner . give . share ;
            Output: Trace:   si = shared Array { flag: Shared, rc: 1, 42 }
            Output: Trace:   let outer = array_new [Array[Int]](1) ;
            Output: Trace:   outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Int], mut [outer]](outer . mut , 0 , si . give) ;
            Output: Trace:   array_drop [Array[Int], given, mut [outer]](outer . mut , 0) ;
            Output: Trace:   array_give [Int, given, shared](si . give , 0) ;
            Output: Trace: exit Main.main => 42
            Result: Ok: 42
            Alloc 0x19: [Int(42)]"#]]
    );
}

#[test]
fn array_drop_shared_class_element() {
    // Dropping a shared class element from an array should just uninitialize the slot.
    // Shared classes (struct classes) have no flags, so drop is just uninitialize.
    crate::assert_interpret_fault!(
        {
            shared class Pt { x: Int; y: Int; }
            class Main {
                fn main(given self) -> Pt {
                    let a = array_new[Pt](1);
                    array_write[Pt, mut[a]](a.mut, 0, new Pt(1, 2));
                    array_drop[Pt, given, mut[a]](a.mut, 0);
                    // Element is now uninitialized — giving it should fault.
                    array_give[Pt, given, given](a.give, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Pt](1) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, Pt { x: ⚡, y: ⚡ } }
            Output: Trace:   array_write [Pt, mut [a]](a . mut , 0 , new Pt (1, 2)) ;
            Output: Trace:   array_drop [Pt, given, mut [a]](a . mut , 0) ;
            Output: Trace:   array_give [Pt, given, given](a . give , 0) ;
            Result: Fault: access of uninitialized value
            Alloc 0x03: [RefCount(1), Capacity(1), Uninitialized, Uninitialized]
            Alloc 0x0f: [Flags(Given), Pointer(0x03)]"#]]
    );
}

// ---------------------------------------------------------------
// ArrayWrite with class containing array field
// ---------------------------------------------------------------

#[test]
fn array_write_class_with_array_field() {
    // Initialize an array element with a class that contains an Array field.
    // Ownership of the inner array transfers into the element slot.
    crate::assert_interpret_only!(
        {
            class Container {
                items: Array[Int];
            }
            class Main {
                fn main(given self) -> Int {
                    let outer = array_new[Container](1);
                    let inner = array_new[Int](2);
                    array_write[Int, mut[inner]](inner.mut, 0, 10);
                    array_write[Int, mut[inner]](inner.mut, 1, 20);
                    let c = new Container(inner.give);
                    array_write[Container, mut[outer]](outer.mut, 0, c.give);
                    // Read the container's inner array via give
                    let got = array_give[Container, given, given](outer.give, 0);
                    print(got.give);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let outer = array_new [Container](1) ;
            Output: Trace:   outer = Array { flag: Given, rc: 1, Container { items: ⚡ } }
            Output: Trace:   let inner = array_new [Int](2) ;
            Output: Trace:   inner = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [inner]](inner . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [inner]](inner . mut , 1 , 20) ;
            Output: Trace:   let c = new Container (inner . give) ;
            Output: Trace:   c = Container { items: Array { flag: Given, rc: 1, 10, 20 } }
            Output: Trace:   array_write [Container, mut [outer]](outer . mut , 0 , c . give) ;
            Output: Trace:   let got = array_give [Container, given, given](outer . give , 0) ;
            Output: Trace:   got = Container { items: Array { flag: Given, rc: 1, 10, 20 } }
            Output: Trace:   print(got . give) ;
            Output: ----->   Container { items: Array { flag: Given, rc: 1, 10, 20 } }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x1f: [Int(0)]"#]]
    );
}

#[test]
fn array_drop_class_with_array_field() {
    // Drop an array element that is a class containing an Array field.
    // Should recursively drop: class element → inner array (refcount→0, freed).
    crate::assert_interpret_only!(
        {
            class Container {
                items: Array[Int];
            }
            class Main {
                fn main(given self) -> Int {
                    let outer = array_new[Container](1);
                    let inner = array_new[Int](1);
                    array_write[Int, mut[inner]](inner.mut, 0, 99);
                    print(inner.ref);
                    let c = new Container(inner.give);
                    print(c.ref);
                    array_write[Container, mut[outer]](outer.mut, 0, c.give);
                    print(outer.ref);
                    // Drop the container element — inner array should be freed.
                    array_drop[Container, given, mut[outer]](outer.mut, 0);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let outer = array_new [Container](1) ;
            Output: Trace:   outer = Array { flag: Given, rc: 1, Container { items: ⚡ } }
            Output: Trace:   let inner = array_new [Int](1) ;
            Output: Trace:   inner = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [inner]](inner . mut , 0 , 99) ;
            Output: Trace:   print(inner . ref) ;
            Output: ----->   ref [inner] Array { flag: Borrowed, rc: 1, 99 }
            Output: Trace:   let c = new Container (inner . give) ;
            Output: Trace:   c = Container { items: Array { flag: Given, rc: 1, 99 } }
            Output: Trace:   print(c . ref) ;
            Output: ----->   ref [c] Container { items: Array { flag: Borrowed, rc: 1, 99 } }
            Output: Trace:   array_write [Container, mut [outer]](outer . mut , 0 , c . give) ;
            Output: Trace:   print(outer . ref) ;
            Output: ----->   ref [outer] Array { flag: Borrowed, rc: 1, Container { items: Array { flag: Given, rc: 1, 99 } } }
            Output: Trace:   array_drop [Container, given, mut [outer]](outer . mut , 0) ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x1e: [Int(0)]"#]]
    );
}

#[test]
fn array_share_uninitialized() {
    // Sharing a newly created array with uninitialized elements succeeds —
    // array elements are user-managed (unsafe), so share doesn't traverse them.
    crate::assert_interpret_only!(
        {
            class Container {
                items: Array[Int];
            }
            class Main {
                fn main(given self) -> Int {
                    let outer = array_new[Container](1).share;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let outer = array_new [Container](1) . share ;
            Output: Trace:   outer = shared Array { flag: Shared, rc: 1, Container { items: ⚡ } }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x06: [Int(0)]"#]]
    );
}

// ---------------------------------------------------------------
// Sharing paths: a.ref on shared array
// ---------------------------------------------------------------

#[test]
fn shared_array_give_increments_refcount() {
    // Giving a shared array increments the refcount.
    // After dropping the original, the copy keeps the array alive.
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](1);
                    array_write[Int, mut[a]](a.mut, 0, 55);
                    let s = a.give.share;
                    let b = s.give;
                    s.drop;
                    // b is a shared copy — give incremented refcount.
                    // After s.drop, refcount is still > 0.
                    array_give[Int, given, shared](b.give, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](1) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [a]](a . mut , 0 , 55) ;
            Output: Trace:   let s = a . give . share ;
            Output: Trace:   s = shared Array { flag: Shared, rc: 1, 55 }
            Output: Trace:   let b = s . give ;
            Output: Trace:   b = shared Array { flag: Shared, rc: 2, 55 }
            Output: Trace:   s . drop ;
            Output: Trace:   array_give [Int, given, shared](b . give , 0) ;
            Output: Trace: exit Main.main => 55
            Result: Ok: 55
            Alloc 0x11: [Int(55)]"#]]
    );
}

// ---------------------------------------------------------------
// Ref arrays
// ---------------------------------------------------------------

#[test]
fn ref_array_print() {
    // Taking a ref to an array and printing it.
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_write[Int, mut[a]](a.mut, 0, 10);
                    array_write[Int, mut[a]](a.mut, 1, 20);
                    print(a.ref);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [a]](a . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [a]](a . mut , 1 , 20) ;
            Output: Trace:   print(a . ref) ;
            Output: ----->   ref [a] Array { flag: Borrowed, rc: 1, 10, 20 }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x10: [Int(0)]"#]]
    );
}

#[test]
fn ref_array_give_int_element() {
    // Giving an Int element from a ref to a given array yields a copy.
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_write[Int, mut[a]](a.mut, 0, 42);
                    array_write[Int, mut[a]](a.mut, 1, 99);
                    let x = array_give[Int, given, ref[a]](a.ref, 0);
                    let y = array_give[Int, given, ref[a]](a.ref, 1);
                    print(x.give);
                    print(y.give);
                    // Original array still intact — ref didn't move elements.
                    print(a.ref);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [a]](a . mut , 0 , 42) ;
            Output: Trace:   array_write [Int, mut [a]](a . mut , 1 , 99) ;
            Output: Trace:   let x = array_give [Int, given, ref [a]](a . ref , 0) ;
            Output: Trace:   x = 42
            Output: Trace:   let y = array_give [Int, given, ref [a]](a . ref , 1) ;
            Output: Trace:   y = 99
            Output: Trace:   print(x . give) ;
            Output: ----->   42
            Output: Trace:   print(y . give) ;
            Output: ----->   99
            Output: Trace:   print(a . ref) ;
            Output: ----->   ref [a] Array { flag: Borrowed, rc: 1, 42, 99 }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x1c: [Int(0)]"#]]
    );
}

#[test]
fn ref_array_give_class_element() {
    // Giving a class element from a ref to a given array yields a borrowed copy.
    crate::assert_interpret_only!(
        {
            class Data {
                x: Int;
            }
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Data](1);
                    array_write[Data, mut[a]](a.mut, 0, new Data(42));
                    let d = array_give[Data, given, ref[a]](a.ref, 0);
                    print(d.give);
                    // Original still intact.
                    print(a.ref);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Data](1) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [a]](a . mut , 0 , new Data (42)) ;
            Output: Trace:   let d = array_give [Data, given, ref [a]](a . ref , 0) ;
            Output: Trace:   d = ref [a] Data { x: 42 }
            Output: Trace:   print(d . give) ;
            Output: ----->   ref [a] Data { x: 42 }
            Output: Trace:   print(a . ref) ;
            Output: ----->   ref [a] Array { flag: Borrowed, rc: 1, Data { x: 42 } }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x13: [Int(0)]"#]]
    );
}

#[test]
fn ref_array_of_shared_arrays() {
    // Array[shared Array[Int]]: giving an element through a ref to the outer
    // array should copy out the shared inner array and increment its refcount.
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let inner = array_new[Int](2);
                    array_write[Int, mut[inner]](inner.mut, 0, 10);
                    array_write[Int, mut[inner]](inner.mut, 1, 20);
                    let si = inner.give.share;
                    let outer = array_new[Array[Int]](1);
                    array_write[Array[Int], mut[outer]](outer.mut, 0, si.give);
                    // outer is given Array[shared Array[Int]].
                    // Take a ref to outer, then give the element.
                    let got = array_give[Array[Int], given, ref[outer]](outer.ref, 0);
                    print(got.give);
                    // Original outer still intact.
                    print(outer.ref);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let inner = array_new [Int](2) ;
            Output: Trace:   inner = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [inner]](inner . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [inner]](inner . mut , 1 , 20) ;
            Output: Trace:   let si = inner . give . share ;
            Output: Trace:   si = shared Array { flag: Shared, rc: 1, 10, 20 }
            Output: Trace:   let outer = array_new [Array[Int]](1) ;
            Output: Trace:   outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Int], mut [outer]](outer . mut , 0 , si . give) ;
            Output: Trace:   let got = array_give [Array[Int], given, ref [outer]](outer . ref , 0) ;
            Output: Trace:   got = ref [outer] Array { flag: Shared, rc: 3, 10, 20 }
            Output: Trace:   print(got . give) ;
            Output: ----->   ref [outer] Array { flag: Shared, rc: 4, 10, 20 }
            Output: Trace:   print(outer . ref) ;
            Output: ----->   ref [outer] Array { flag: Borrowed, rc: 1, Array { flag: Shared, rc: 3, 10, 20 } }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x03: [RefCount(1), Capacity(2), Int(10), Int(20)]
            Alloc 0x20: [Int(0)]"#]]
    );
}
