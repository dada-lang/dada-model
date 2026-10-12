// Tests for Array[T] operations: ArrayNew, ArrayCapacity, ArrayGive, ArrayDrop, ArrayWrite.
//
// All tests use assert_interpret_only! since the type checker's Array rules
// are simplified stubs — the real typing (e.g., ArrayGive returning given[array] T)
// is deferred.
//
// Expected patterns:
// - Arrays are typically `given` (owned)
// - Use `!` for modifications (array_write, array_drop)
// - Use `.share` for read-only access (array_give, array_capacity, print)
// - Use `given` only when transferring ownership
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
    // the reference count to 0 and freed the allocation; now `uninitialize` is
    // used instead.
    crate::assert_interpret_only!(
        {
            struct Wrapper {
                field: Array[Int];
            }
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](3);
                    let w = new Wrapper(a^);
                    array_capacity[Int, given](w.field^);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](3) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ }
            Output: Trace:   let _1_w = new Wrapper (_1_a ^) ;
            Output: Trace:   _1_w = Wrapper { field: Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ } }
            Output: Trace:   array_capacity [Int, given](_1_w . field ^) ;
            Output: Trace: exit Main.main => 3
            Result: Ok: 3
            Alloc 0x0a: [Int(3)]"#]]
    );
}

#[test]
fn reassign_drops_old_array() {
    // Reassigning a variable that holds an Array should drop (decrement
    // reference count of) the old array before installing the new one.
    // If the old array were leaked the reference count would never reach zero
    // and its allocation would still appear in the heap snapshot.
    crate::assert_interpret_only!(
        {
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_write[Int, ![a]](a!, 0, 1);
                    array_write[Int, ![a]](a!, 1, 2);
                    // Replace a with a fresh array — old array must be dropped.
                    a = array_new[Int](4);
                    array_capacity[Int, given](a^);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 0 , 1) ;
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 1 , 2) ;
            Output: Trace:   _1_a = array_new [Int](4) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡, ⚡ }
            Output: Trace:   array_capacity [Int, given](_1_a ^) ;
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
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](3);
                    array_capacity[Int, given](a^);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](3) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ }
            Output: Trace:   array_capacity [Int, given](_1_a ^) ;
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
            struct Main {
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
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](3);
                    array_write[Int, ![a]](a!, 0, 10);
                    array_write[Int, ![a]](a!, 1, 20);
                    array_write[Int, ![a]](a!, 2, 30);
                    print(array_give[Int, given, shared[a]](a.share, 0));
                    print(array_give[Int, given, shared[a]](a.share, 1));
                    array_give[Int, given, given](a^, 2);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](3) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 0 , 10) ;
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 1 , 20) ;
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 2 , 30) ;
            Output: Trace:   print(array_give [Int, given, shared [_1_a]](_1_a . share , 0)) ;
            Output: ----->   10
            Output: Trace:   print(array_give [Int, given, shared [_1_a]](_1_a . share , 1)) ;
            Output: ----->   20
            Output: Trace:   array_give [Int, given, given](_1_a ^ , 2) ;
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
            struct Data { x: Int; }
            struct Main {
                fn main(given self) -> Data {
                    let a = array_new[Data](2);
                    array_write[Data, ![a]](a!, 0, new Data(42));
                    array_write[Data, ![a]](a!, 1, new Data(99));
                    print(array_give[Data, given, shared[a]](a.share, 0));
                    array_give[Data, given, given](a^, 1);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ }, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, ! [_1_a]](_1_a ! , 0 , new Data (42)) ;
            Output: Trace:   array_write [Data, ! [_1_a]](_1_a ! , 1 , new Data (99)) ;
            Output: Trace:   print(array_give [Data, given, shared [_1_a]](_1_a . share , 0)) ;
            Output: ----->   Data { x: 42 }
            Output: Trace:   array_give [Data, given, given](_1_a ^ , 1) ;
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
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](3);
                    array_give[Int, given, given](a^, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](3) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ }
            Output: Trace:   array_give [Int, given, given](_1_a ^ , 0) ;
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
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_write[Int, ![a]](a!, 0, 42);
                    let x = array_give[Int, given, shared[a]](a.share, 0);
                    array_give[Int, given, given](a^, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 0 , 42) ;
            Output: Trace:   let _1_x = array_give [Int, given, shared [_1_a]](_1_a . share , 0) ;
            Output: Trace:   _1_x = 42
            Output: Trace:   array_give [Int, given, given](_1_a ^ , 0) ;
            Output: Trace: exit Main.main => 42
            Result: Ok: 42
            Alloc 0x10: [Int(42)]"#]]
    );
}

#[test]
fn given_array_give_class_moves_out() {
    // Given array: giving the array to array_give moves the element out
    // (Given effective flags → move semantics). The element is
    // uninitalized in the backing, but the array place sharing is consumed too,
    // so there's no second access to fault on. Verify by giving element,
    // then checking the element was actually moved (backing has Uninitialized).
    // To observe the move: share the array first, give through one place sharing
    // (which is shared → copy), then drop the share and access ^.
    //
    // Actually, the simplest way to test Given move: use a given array,
    // give element 0 (moves it), then use array_give on element 1.
    crate::assert_interpret_only!(
        {
            struct Data { x: Int; }
            struct Main {
                fn main(given self) -> Data {
                    let a = array_new[Data](2);
                    array_write[Data, ![a]](a!, 0, new Data(42));
                    array_write[Data, ![a]](a!, 1, new Data(99));
                    // Give element 0 from given array — moves it out.
                    // The array place sharing is consumed, so we pass a^.
                    array_give[Data, given, given](a^, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ }, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, ! [_1_a]](_1_a ! , 0 , new Data (42)) ;
            Output: Trace:   array_write [Data, ! [_1_a]](_1_a ! , 1 , new Data (99)) ;
            Output: Trace:   array_give [Data, given, given](_1_a ^ , 0) ;
            Output: Trace: exit Main.main => Data { x: 42 }
            Result: Ok: Data { x: 42 }
            Alloc 0x12: [Int(42)]"#]]
    );
}

#[test]
fn shared_array_give_class_is_shared_copy() {
    // Shared array: class elements are given with shared semantics —
    // no move, element remains available for repeated gives.
    // P=shared produces a shared copy (rc++ on boxed fields).
    crate::assert_interpret_only!(
        {
            struct Data { x: Int; }
            struct Main {
                fn main(given self) -> Data {
                    let a = array_new[Data](1);
                    array_write[Data, ![a]](a!, 0, new Data(42));
                    let s = a^.share;
                    let x = array_give[Data, shared, shared[s]](s.share, 0);
                    print(x^);
                    // Element still available — shared semantics, no move.
                    array_give[Data, shared, shared](s^, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, ! [_1_a]](_1_a ! , 0 , new Data (42)) ;
            Output: Trace:   let _1_s = _1_a ^ . share ;
            Output: Trace:   _1_s = shared Array { flag: SharedOwned, rc: 1, Data { x: 42 } }
            Output: Trace:   let _1_x = array_give [Data, shared, shared [_1_s]](_1_s . share , 0) ;
            Output: Trace:   _1_x = shared Data { x: 42 }
            Output: Trace:   print(_1_x ^) ;
            Output: ----->   shared Data { x: 42 }
            Output: Trace:   array_give [Data, shared, shared](_1_s ^ , 0) ;
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
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_give[Int, given, given](a^, 5);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_give [Int, given, given](_1_a ^ , 5) ;
            Result: Fault: array_give: index 5 out of bounds (capacity 2)
            Alloc 0x03: [RefCount(1), Capacity(2), Uninitialized, Uninitialized]
            Alloc 0x06: [Flags(Given), Pointer(0x03)]"#]]
    );
}

#[test]
fn array_write_out_of_bounds() {
    crate::assert_interpret_fault!(
        {
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_write[Int, ![a]](a!, 3, 42);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 3 , 42) ;
            Result: Fault: array_give: index 3 out of bounds (capacity 2)
            Alloc 0x03: [RefCount(1), Capacity(2), Uninitialized, Uninitialized]
            Alloc 0x04: [Flags(Given), Pointer(0x03)]
            Alloc 0x06: [Lease(0x03)]"#]]
    );
}

// ---------------------------------------------------------------
// Double initialize
// ---------------------------------------------------------------

#[test]
fn array_write_overwrites_existing() {
    crate::assert_interpret_only!(
        {
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_write[Int, ![a]](a!, 0, 10);
                    array_write[Int, ![a]](a!, 0, 20);
                    array_give[Int, given, given](a^, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 0 , 10) ;
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 0 , 20) ;
            Output: Trace:   array_give [Int, given, given](_1_a ^ , 0) ;
            Output: Trace: exit Main.main => 20
            Result: Ok: 20
            Alloc 0x10: [Int(20)]"#]]
    );
}

/// array_write overwriting a shared array element should decrement reference count
/// and free the old array when reference count reaches zero.
#[test]
fn array_write_overwrites_shared_array() {
    crate::assert_interpret_only!(
        {
            struct Main {
                fn main(given self) -> Int {
                    let outer = array_new[Array[Int]](1);
                    let inner = array_new[Int](0).share;
                    array_write[Array[Int], ![outer]](outer!, 0, inner^);
                    let replacement = array_new[Int](1);
                    array_write[Int, ![replacement]](replacement!, 0, 99);

                    print(outer.share);
                    print(inner.share);
                    print(replacement.share);

                    array_write[Array[Int], ![outer]](outer!, 0, replacement^);

                    print(outer.share);
                    print(inner.share);
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_outer = array_new [Array[Int]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   let _1_inner = array_new [Int](0) . share ;
            Output: Trace:   _1_inner = shared Array { flag: SharedOwned, rc: 1 }
            Output: Trace:   array_write [Array[Int], ! [_1_outer]](_1_outer ! , 0 , _1_inner ^) ;
            Output: Trace:   let _1_replacement = array_new [Int](1) ;
            Output: Trace:   _1_replacement = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_replacement]](_1_replacement ! , 0 , 99) ;
            Output: Trace:   print(_1_outer . share) ;
            Output: ----->   shared [_1_outer] Array { flag: SharedPlace, rc: 1, Array { flag: SharedOwned, rc: 2 } }
            Output: Trace:   print(_1_inner . share) ;
            Output: ----->   shared Array { flag: SharedPlace, rc: 2 }
            Output: Trace:   print(_1_replacement . share) ;
            Output: ----->   shared [_1_replacement] Array { flag: SharedPlace, rc: 1, 99 }
            Output: Trace:   array_write [Array[Int], ! [_1_outer]](_1_outer ! , 0 , _1_replacement ^) ;
            Output: Trace:   print(_1_outer . share) ;
            Output: ----->   shared [_1_outer] Array { flag: SharedPlace, rc: 1, Array { flag: Given, rc: 1, 99 } }
            Output: Trace:   print(_1_inner . share) ;
            Output: ----->   shared Array { flag: SharedPlace, rc: 2 }
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
    // Drop a class element (move type), then getting it should fault.
    // Note: Int is a copy type, so array_drop[Int, given, ...] would be a no-op.
    // We use Data (a move type) to test actual drop semantics.
    crate::assert_interpret_fault!(
        {
            struct Data { x: Int; }
            struct Main {
                fn main(given self) -> Data {
                    let a = array_new[Data](2);
                    array_write[Data, ![a]](a!, 0, new Data(42));
                    array_drop[Data, given, ![a]](a!, 0, 1);
                    array_give[Data, given, given](a^, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ }, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, ! [_1_a]](_1_a ! , 0 , new Data (42)) ;
            Output: Trace:   array_drop [Data, given, ! [_1_a]](_1_a ! , 0 , 1) ;
            Output: Trace:   array_give [Data, given, given](_1_a ^ , 0) ;
            Result: Fault: access of uninitialized value
            Alloc 0x03: [RefCount(1), Capacity(2), Uninitialized, Uninitialized]
            Alloc 0x0f: [Flags(Given), Pointer(0x03)]"#]]
    );
}

#[test]
fn array_drop_class_element() {
    // Drop a class element — should recursively drop.
    crate::assert_interpret_only!(
        {
            struct Data { x: Int; }
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Data](1);
                    array_write[Data, ![a]](a!, 0, new Data(42));
                    array_drop[Data, given, ![a]](a!, 0, 1);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, ! [_1_a]](_1_a ! , 0 , new Data (42)) ;
            Output: Trace:   array_drop [Data, given, ! [_1_a]](_1_a ! , 0 , 1) ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x0f: [Int(0)]"#]]
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
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](1);
                    let b = a^;
                    array_capacity[Int, given](b^);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   let _1_b = _1_a ^ ;
            Output: Trace:   _1_b = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_capacity [Int, given](_1_b ^) ;
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
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_write[Int, ![a]](a!, 0, 10);
                    array_write[Int, ![a]](a!, 1, 20);
                    let b = a^;
                    array_give[Int, given, given](b^, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 0 , 10) ;
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 1 , 20) ;
            Output: Trace:   let _1_b = _1_a ^ ;
            Output: Trace:   _1_b = Array { flag: Given, rc: 1, 10, 20 }
            Output: Trace:   array_give [Int, given, given](_1_b ^ , 0) ;
            Output: Trace: exit Main.main => 10
            Result: Ok: 10
            Alloc 0x12: [Int(10)]"#]]
    );
}

#[test]
fn array_give_uninitializes_source() {
    crate::assert_interpret_fault!(
        {
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](1);
                    let b = a^;
                    array_capacity[Int, given](a^);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   let _1_b = _1_a ^ ;
            Output: Trace:   _1_b = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_capacity [Int, given](_1_a ^) ;
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
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_write[Int, ![a]](a!, 0, 10);
                    array_write[Int, ![a]](a!, 1, 20);
                    let s = a^.share;
                    let x = array_give[Int, given, shared[s]](s.share, 0);
                    let y = array_give[Int, given, shared](s^, 1);
                    x^ + y^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 0 , 10) ;
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 1 , 20) ;
            Output: Trace:   let _1_s = _1_a ^ . share ;
            Output: Trace:   _1_s = shared Array { flag: SharedOwned, rc: 1, 10, 20 }
            Output: Trace:   let _1_x = array_give [Int, given, shared [_1_s]](_1_s . share , 0) ;
            Output: Trace:   _1_x = 10
            Output: Trace:   let _1_y = array_give [Int, given, shared](_1_s ^ , 1) ;
            Output: Trace:   _1_y = 20
            Output: Trace:   _1_x ^ + _1_y ^ ;
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
    // The reference count goes: 1 (new) → shared → 2 (give to b) → 1 (a dropped) → use b.
    crate::assert_interpret_only!(
        {
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_write[Int, ![a]](a!, 0, 10);
                    array_write[Int, ![a]](a!, 1, 20);
                    let s = a^.share;
                    let b = s^;
                    drop s;
                    array_give[Int, given, shared](b^, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 0 , 10) ;
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 1 , 20) ;
            Output: Trace:   let _1_s = _1_a ^ . share ;
            Output: Trace:   _1_s = shared Array { flag: SharedOwned, rc: 1, 10, 20 }
            Output: Trace:   let _1_b = _1_s ^ ;
            Output: Trace:   _1_b = shared Array { flag: SharedOwned, rc: 2, 10, 20 }
            Output: Trace:   drop _1_s ;
            Output: Trace:   array_give [Int, given, shared](_1_b ^ , 0) ;
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
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_write[Int, ![a]](a!, 0, 10);
                    array_write[Int, ![a]](a!, 1, 20);
                    let s = a^.share;
                    let b = s^;
                    drop s;
                    drop b;
                    42;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 0 , 10) ;
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 1 , 20) ;
            Output: Trace:   let _1_s = _1_a ^ . share ;
            Output: Trace:   _1_s = shared Array { flag: SharedOwned, rc: 1, 10, 20 }
            Output: Trace:   let _1_b = _1_s ^ ;
            Output: Trace:   _1_b = shared Array { flag: SharedOwned, rc: 2, 10, 20 }
            Output: Trace:   drop _1_s ;
            Output: Trace:   drop _1_b ;
            Output: Trace:   42 ;
            Output: Trace: exit Main.main => 42
            Result: Ok: 42
            Alloc 0x14: [Int(42)]"#]]
    );
}

#[test]
fn nested_array_in_class_field() {
    // A class with an Array[Int] field — dropping the class
    // recursively drops the array (decrements reference count to 0).
    crate::assert_interpret_only!(
        {
            struct Wrapper {
                items: Array[Int];
            }
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](1);
                    array_write[Int, ![a]](a!, 0, 99);
                    let w = new Wrapper(a^);
                    drop w;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 0 , 99) ;
            Output: Trace:   let _1_w = new Wrapper (_1_a ^) ;
            Output: Trace:   _1_w = Wrapper { items: Array { flag: Given, rc: 1, 99 } }
            Output: Trace:   drop _1_w ;
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
    // shared struct elements have no flags word per element.
    crate::assert_interpret_only!(
        {
            shared struct Pt { x: Int; y: Int; }
            struct Main {
                fn main(given self) -> Pt {
                    let a = array_new[Pt](2);
                    array_write[Pt, ![a]](a!, 0, new Pt(1, 2));
                    array_write[Pt, ![a]](a!, 1, new Pt(3, 4));
                    print(array_give[Pt, given, shared[a]](a.share, 0));
                    array_give[Pt, given, given](a^, 1);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Pt](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Pt { x: ⚡, y: ⚡ }, Pt { x: ⚡, y: ⚡ } }
            Output: Trace:   array_write [Pt, ! [_1_a]](_1_a ! , 0 , new Pt (1, 2)) ;
            Output: Trace:   array_write [Pt, ! [_1_a]](_1_a ! , 1 , new Pt (3, 4)) ;
            Output: Trace:   print(array_give [Pt, given, shared [_1_a]](_1_a . share , 0)) ;
            Output: ----->   Pt { x: 1, y: 2 }
            Output: Trace:   array_give [Pt, given, given](_1_a ^ , 1) ;
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
            struct Inner { value: Int; }
            struct Outer { inner: Inner; }
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Outer](2);
                    array_write[Outer, ![a]](a!, 0, new Outer(new Inner(1)));
                    array_write[Outer, ![a]](a!, 1, new Outer(new Inner(2)));
                    drop a;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Outer](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Outer { inner: Inner { value: ⚡ } }, Outer { inner: Inner { value: ⚡ } } }
            Output: Trace:   array_write [Outer, ! [_1_a]](_1_a ! , 0 , new Outer (new Inner (1))) ;
            Output: Trace:   array_write [Outer, ! [_1_a]](_1_a ! , 1 , new Outer (new Inner (2))) ;
            Output: Trace:   drop _1_a ;
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
    // Use Data (move type) so array_drop actually executes.
    // Int would be a no-op (copy type).
    crate::assert_interpret_fault!(
        {
            struct Data { x: Int; }
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Data](2);
                    array_drop[Data, given, ![a]](a!, 5, 6);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ }, Data { x: ⚡ } }
            Output: Trace:   array_drop [Data, given, ! [_1_a]](_1_a ! , 5 , 6) ;
            Result: Fault: array_drop: index 5 out of bounds (capacity 2)
            Alloc 0x03: [RefCount(1), Capacity(2), Uninitialized, Uninitialized]
            Alloc 0x04: [Flags(Given), Pointer(0x03)]
            Alloc 0x06: [Lease(0x03)]"#]]
    );
}

#[test]
fn array_drop_uninitialized_faults() {
    // Use Data (move type) so array_drop actually executes.
    // Int would be a no-op (copy type).
    crate::assert_interpret_fault!(
        {
            struct Data { x: Int; }
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Data](2);
                    array_drop[Data, given, ![a]](a!, 0, 1);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ }, Data { x: ⚡ } }
            Output: Trace:   array_drop [Data, given, ! [_1_a]](_1_a ! , 0 , 1) ;
            Result: Fault: access of uninitialized value
            Alloc 0x03: [RefCount(1), Capacity(2), Uninitialized, Uninitialized]
            Alloc 0x04: [Flags(Given), Pointer(0x03)]
            Alloc 0x06: [Lease(0x03)]"#]]
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
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](0);
                    array_capacity[Int, given](a^);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](0) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1 }
            Output: Trace:   array_capacity [Int, given](_1_a ^) ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x07: [Int(0)]"#]]
    );
}

#[test]
fn array_zero_length_access_faults() {
    crate::assert_interpret_fault!(
        {
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](0);
                    array_give[Int, given, given](a^, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](0) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1 }
            Output: Trace:   array_give [Int, given, given](_1_a ^ , 0) ;
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
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_write[Int, ![a]](a!, 0, 10);
                    array_write[Int, ![a]](a!, 1, 20);
                    let b = a^;
                    array_give[Int, given, given](b^, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 0 , 10) ;
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 1 , 20) ;
            Output: Trace:   let _1_b = _1_a ^ ;
            Output: Trace:   _1_b = Array { flag: Given, rc: 1, 10, 20 }
            Output: Trace:   array_give [Int, given, given](_1_b ^ , 0) ;
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
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](1);
                    let b = a^;
                    let c = a^;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   let _1_b = _1_a ^ ;
            Output: Trace:   _1_b = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   let _1_c = _1_a ^ ;
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
            struct Container {
                items: Array[Int];
            }
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_write[Int, ![a]](a!, 0, 1);
                    array_write[Int, ![a]](a!, 1, 2);
                    let c = new Container(a^);
                    let s = c^.share;
                    print(s^);
                    print(array_give[Int, given, shared[s.items]](s.items.share, 0));
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 0 , 1) ;
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 1 , 2) ;
            Output: Trace:   let _1_c = new Container (_1_a ^) ;
            Output: Trace:   _1_c = Container { items: Array { flag: Given, rc: 1, 1, 2 } }
            Output: Trace:   let _1_s = _1_c ^ . share ;
            Output: Trace:   _1_s = shared Container { items: Array { flag: SharedOwned, rc: 1, 1, 2 } }
            Output: Trace:   print(_1_s ^) ;
            Output: ----->   shared Container { items: Array { flag: SharedOwned, rc: 2, 1, 2 } }
            Output: Trace:   print(array_give [Int, given, shared [_1_s . items]](_1_s . items . share , 0)) ;
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
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](3);
                    array_write[Int, ![a]](a!, 0, 10);
                    array_write[Int, ![a]](a!, 1, 20);
                    array_write[Int, ![a]](a!, 2, 30);
                    print(a.share);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](3) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 0 , 10) ;
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 1 , 20) ;
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 2 , 30) ;
            Output: Trace:   print(_1_a . share) ;
            Output: ----->   shared [_1_a] Array { flag: SharedPlace, rc: 1, 10, 20, 30 }
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
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_write[Int, ![a]](a!, 0, 10);
                    array_write[Int, ![a]](a!, 1, 20);
                    let s = a^.share;
                    let b = s^;
                    // Both s and b point to the same backing; reference count is 2.
                    let x = array_give[Int, given, shared[s]](s.share, 0);
                    let y = array_give[Int, given, shared](b^, 1);
                    x^ + y^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 0 , 10) ;
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 1 , 20) ;
            Output: Trace:   let _1_s = _1_a ^ . share ;
            Output: Trace:   _1_s = shared Array { flag: SharedOwned, rc: 1, 10, 20 }
            Output: Trace:   let _1_b = _1_s ^ ;
            Output: Trace:   _1_b = shared Array { flag: SharedOwned, rc: 2, 10, 20 }
            Output: Trace:   let _1_x = array_give [Int, given, shared [_1_s]](_1_s . share , 0) ;
            Output: Trace:   _1_x = 10
            Output: Trace:   let _1_y = array_give [Int, given, shared](_1_b ^ , 1) ;
            Output: Trace:   _1_y = 20
            Output: Trace:   _1_x ^ + _1_y ^ ;
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
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](1);
                    array_write[Int, ![a]](a!, 0, 42);
                    let s = a^.share;
                    let b = s^;
                    let c = s^;
                    // reference count = 3
                    drop s;
                    drop b;
                    // reference count = 1, c still alive
                    array_give[Int, given, shared](c^, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 0 , 42) ;
            Output: Trace:   let _1_s = _1_a ^ . share ;
            Output: Trace:   _1_s = shared Array { flag: SharedOwned, rc: 1, 42 }
            Output: Trace:   let _1_b = _1_s ^ ;
            Output: Trace:   _1_b = shared Array { flag: SharedOwned, rc: 2, 42 }
            Output: Trace:   let _1_c = _1_s ^ ;
            Output: Trace:   _1_c = shared Array { flag: SharedOwned, rc: 3, 42 }
            Output: Trace:   drop _1_s ;
            Output: Trace:   drop _1_b ;
            Output: Trace:   array_give [Int, given, shared](_1_c ^ , 0) ;
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
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](1);
                    array_write[Int, ![a]](a!, 0, 99);
                    let s = a^.share;
                    let b = s^;
                    let c = b^;
                    drop s;
                    drop b;
                    drop c;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 0 , 99) ;
            Output: Trace:   let _1_s = _1_a ^ . share ;
            Output: Trace:   _1_s = shared Array { flag: SharedOwned, rc: 1, 99 }
            Output: Trace:   let _1_b = _1_s ^ ;
            Output: Trace:   _1_b = shared Array { flag: SharedOwned, rc: 2, 99 }
            Output: Trace:   let _1_c = _1_b ^ ;
            Output: Trace:   _1_c = shared Array { flag: SharedOwned, rc: 3, 99 }
            Output: Trace:   drop _1_s ;
            Output: Trace:   drop _1_b ;
            Output: Trace:   drop _1_c ;
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
            struct Main {
                fn main(given self) -> Int {
                    let outer = array_new[Array[Int]](2);
                    let inner0 = array_new[Int](3);
                    array_write[Array[Int], ![outer]](outer!, 0, inner0^);
                    let got = array_give[Array[Int], given, given](outer^, 0);
                    array_capacity[Int, given](got^);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_outer = array_new [Array[Int]](2) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   let _1_inner0 = array_new [Int](3) ;
            Output: Trace:   _1_inner0 = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ }
            Output: Trace:   array_write [Array[Int], ! [_1_outer]](_1_outer ! , 0 , _1_inner0 ^) ;
            Output: Trace:   let _1_got = array_give [Array[Int], given, given](_1_outer ^ , 0) ;
            Output: Trace:   _1_got = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ }
            Output: Trace:   array_capacity [Int, given](_1_got ^) ;
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
    // reference count. We can give the same inner element multiple times.
    crate::assert_interpret_only!(
        {
            struct Main {
                fn main(given self) -> Int {
                    let inner = array_new[Int](2);
                    array_write[Int, ![inner]](inner!, 0, 10);
                    array_write[Int, ![inner]](inner!, 1, 20);
                    let outer = array_new[Array[Int]](1);
                    array_write[Array[Int], ![outer]](outer!, 0, inner^);
                    let s = outer^.share;
                    // Give the inner array element — should get a shared copy
                    // and increment inner's reference count.
                    let got = array_give[Array[Int], shared, shared[s]](s.share, 0);
                    print(got^);
                    // Give it again — shared elements can be given repeatedly.
                    let got2 = array_give[Array[Int], shared, shared](s^, 0);
                    array_give[Int, given, given](got2^, 1);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Int](2) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_inner]](_1_inner ! , 0 , 10) ;
            Output: Trace:   array_write [Int, ! [_1_inner]](_1_inner ! , 1 , 20) ;
            Output: Trace:   let _1_outer = array_new [Array[Int]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Int], ! [_1_outer]](_1_outer ! , 0 , _1_inner ^) ;
            Output: Trace:   let _1_s = _1_outer ^ . share ;
            Output: Trace:   _1_s = shared Array { flag: SharedOwned, rc: 1, Array { flag: Given, rc: 1, 10, 20 } }
            Output: Trace:   let _1_got = array_give [Array[Int], shared, shared [_1_s]](_1_s . share , 0) ;
            Output: Trace:   _1_got = shared Array { flag: SharedOwned, rc: 2, 10, 20 }
            Output: Trace:   print(_1_got ^) ;
            Output: ----->   shared Array { flag: SharedOwned, rc: 3, 10, 20 }
            Output: Trace:   let _1_got2 = array_give [Array[Int], shared, shared](_1_s ^ , 0) ;
            Output: Trace:   _1_got2 = shared Array { flag: SharedOwned, rc: 3, 10, 20 }
            Output: Trace:   array_give [Int, given, given](_1_got2 ^ , 1) ;
            Output: Trace: exit Main.main => 20
            Result: Ok: 20
            Alloc 0x03: [RefCount(1), Capacity(2), Int(10), Int(20)]
            Alloc 0x24: [Int(20)]"#]]
    );
}

#[test]
fn nested_array_drop_inner_decrements_refcount() {
    // Array[Array[Int]]: dropping the inner element in the outer array
    // should decrement the inner array's reference count.
    crate::assert_interpret_only!(
        {
            struct Main {
                fn main(given self) -> Int {
                    let inner = array_new[Int](1);
                    array_write[Int, ![inner]](inner!, 0, 42);
                    let s = inner^.share;
                    let outer = array_new[Array[Int]](1);
                    array_write[Array[Int], ![outer]](outer!, 0, s^);
                    // s is shared: s^ copies + rc++. s still alive, rc=2.
                    // Drop the element in outer — reference count goes to 1.
                    array_drop[Array[Int], given, ![outer]](outer!, 0, 1);
                    // s var still alive, can still read.
                    array_give[Int, given, shared](s^, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Int](1) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_inner]](_1_inner ! , 0 , 42) ;
            Output: Trace:   let _1_s = _1_inner ^ . share ;
            Output: Trace:   _1_s = shared Array { flag: SharedOwned, rc: 1, 42 }
            Output: Trace:   let _1_outer = array_new [Array[Int]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Int], ! [_1_outer]](_1_outer ! , 0 , _1_s ^) ;
            Output: Trace:   array_drop [Array[Int], given, ! [_1_outer]](_1_outer ! , 0 , 1) ;
            Output: Trace:   array_give [Int, given, shared](_1_s ^ , 0) ;
            Output: Trace: exit Main.main => 42
            Result: Ok: 42
            Alloc 0x1a: [Int(42)]"#]]
    );
}

#[test]
fn nested_array_all_refs_freed() {
    // Nested array: dropping the outer array scrubs its backing but does NOT
    // drop elements (arrays don't drop their elements — that's the user's job).
    // The inner array's backing allocation remains as an orphan in the heap.
    // This documents the unsafe contract: use array_drop to clean up elements.
    crate::assert_interpret_only!(
        {
            struct Main {
                fn main(given self) -> Int {
                    let inner = array_new[Int](1);
                    array_write[Int, ![inner]](inner!, 0, 1);
                    let outer = array_new[Array[Int]](1);
                    array_write[Array[Int], ![outer]](outer!, 0, inner^);
                    // Drop outer — outer backing scrubbed, but inner backing leaks.
                    drop outer;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Int](1) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_inner]](_1_inner ! , 0 , 1) ;
            Output: Trace:   let _1_outer = array_new [Array[Int]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Int], ! [_1_outer]](_1_outer ! , 0 , _1_inner ^) ;
            Output: Trace:   drop _1_outer ;
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
    // with incremented reference count. The inner array is also shared, so reading
    // Data elements through both paths works (shared semantics, no move).
    crate::assert_interpret_only!(
        {
            struct Data { x: Int; }
            struct Main {
                fn main(given self) -> Int {
                    let inner = array_new[Data](1);
                    array_write[Data, ![inner]](inner!, 0, new Data(42));
                    let si = inner^.share;
                    let outer = array_new[Array[Data]](1);
                    array_write[Array[Data], ![outer]](outer!, 0, si^);
                    let so = outer^.share;
                    // Give inner array element from shared outer — shared copy.
                    let got = array_give[Array[Data], shared, shared[so]](so.share, 0);
                    // Read Data through the copy — shared, so no move.
                    print(array_give[Data, shared, shared](got^, 0));
                    // Read Data through original inner — still available.
                    print(array_give[Data, shared, shared](si^, 0));
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Data](1) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, ! [_1_inner]](_1_inner ! , 0 , new Data (42)) ;
            Output: Trace:   let _1_si = _1_inner ^ . share ;
            Output: Trace:   _1_si = shared Array { flag: SharedOwned, rc: 1, Data { x: 42 } }
            Output: Trace:   let _1_outer = array_new [Array[Data]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Data], ! [_1_outer]](_1_outer ! , 0 , _1_si ^) ;
            Output: Trace:   let _1_so = _1_outer ^ . share ;
            Output: Trace:   _1_so = shared Array { flag: SharedOwned, rc: 1, Array { flag: SharedOwned, rc: 2, Data { x: 42 } } }
            Output: Trace:   let _1_got = array_give [Array[Data], shared, shared [_1_so]](_1_so . share , 0) ;
            Output: Trace:   _1_got = shared Array { flag: SharedOwned, rc: 3, Data { x: 42 } }
            Output: Trace:   print(array_give [Data, shared, shared](_1_got ^ , 0)) ;
            Output: ----->   shared Data { x: 42 }
            Output: Trace:   print(array_give [Data, shared, shared](_1_si ^ , 0)) ;
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
    // Giving the element calls share_op (increments inner backing reference count).
    // Both the copy and the original inner var can read Data elements
    // (shared semantics propagate through both array layers).
    crate::assert_interpret_only!(
        {
            struct Data { x: Int; }
            struct Main {
                fn main(given self) -> Int {
                    let inner = array_new[Data](1);
                    array_write[Data, ![inner]](inner!, 0, new Data(99));
                    let si = inner^.share;
                    let outer = array_new[Array[Data]](1);
                    array_write[Array[Data], ![outer]](outer!, 0, si^);
                    let so = outer^.share;
                    // Give element from outer — share_op increments inner reference count.
                    let got = array_give[Array[Data], shared, shared[so]](so.share, 0);
                    // Read Data through the copy — shared, no move.
                    print(array_give[Data, shared, shared](got^, 0));
                    // Read Data through original inner — still available.
                    print(array_give[Data, shared, shared](si^, 0));
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Data](1) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, ! [_1_inner]](_1_inner ! , 0 , new Data (99)) ;
            Output: Trace:   let _1_si = _1_inner ^ . share ;
            Output: Trace:   _1_si = shared Array { flag: SharedOwned, rc: 1, Data { x: 99 } }
            Output: Trace:   let _1_outer = array_new [Array[Data]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Data], ! [_1_outer]](_1_outer ! , 0 , _1_si ^) ;
            Output: Trace:   let _1_so = _1_outer ^ . share ;
            Output: Trace:   _1_so = shared Array { flag: SharedOwned, rc: 1, Array { flag: SharedOwned, rc: 2, Data { x: 99 } } }
            Output: Trace:   let _1_got = array_give [Array[Data], shared, shared [_1_so]](_1_so . share , 0) ;
            Output: Trace:   _1_got = shared Array { flag: SharedOwned, rc: 3, Data { x: 99 } }
            Output: Trace:   print(array_give [Data, shared, shared](_1_got ^ , 0)) ;
            Output: ----->   shared Data { x: 99 }
            Output: Trace:   print(array_give [Data, shared, shared](_1_si ^ , 0)) ;
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
    // element produces a shared copy with incremented reference count.
    // After dropping the outer array entirely, the given copy still works
    // because share_op kept the inner backing alive.
    crate::assert_interpret_only!(
        {
            struct Data { x: Int; }
            struct Main {
                fn main(given self) -> Int {
                    let inner = array_new[Data](1);
                    array_write[Data, ![inner]](inner!, 0, new Data(42));
                    let si = inner^.share;
                    let outer = array_new[Array[Data]](1);
                    array_write[Array[Data], ![outer]](outer!, 0, si^);
                    let so = outer^.share;
                    // Give the inner array element from shared outer.
                    let got = array_give[Array[Data], shared, shared[so]](so.share, 0);
                    // Drop outer entirely — cascading drop hits the element,
                    // which decrements inner reference count. But got's share_op
                    // already incremented it, so reference count > 0.
                    drop si;
                    drop so;
                    // got still alive — read the Data element.
                    array_give[Data, shared, shared](got^, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Data](1) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, ! [_1_inner]](_1_inner ! , 0 , new Data (42)) ;
            Output: Trace:   let _1_si = _1_inner ^ . share ;
            Output: Trace:   _1_si = shared Array { flag: SharedOwned, rc: 1, Data { x: 42 } }
            Output: Trace:   let _1_outer = array_new [Array[Data]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Data], ! [_1_outer]](_1_outer ! , 0 , _1_si ^) ;
            Output: Trace:   let _1_so = _1_outer ^ . share ;
            Output: Trace:   _1_so = shared Array { flag: SharedOwned, rc: 1, Array { flag: SharedOwned, rc: 2, Data { x: 42 } } }
            Output: Trace:   let _1_got = array_give [Array[Data], shared, shared [_1_so]](_1_so . share , 0) ;
            Output: Trace:   _1_got = shared Array { flag: SharedOwned, rc: 3, Data { x: 42 } }
            Output: Trace:   drop _1_si ;
            Output: Trace:   drop _1_so ;
            Output: Trace:   array_give [Data, shared, shared](_1_got ^ , 0) ;
            Output: Trace: exit Main.main => shared Data { x: 42 }
            Result: Ok: shared Data { x: 42 }
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
    // Multiple gives from outer each increment inner reference count.
    // All three references (inner var, copy1, copy2) can independently
    // read Data elements — shared semantics propagate through both layers.
    crate::assert_interpret_only!(
        {
            struct Data { x: Int; }
            struct Main {
                fn main(given self) -> Int {
                    let inner = array_new[Data](1);
                    array_write[Data, ![inner]](inner!, 0, new Data(77));
                    let si = inner^.share;
                    let outer = array_new[Array[Data]](1);
                    array_write[Array[Data], ![outer]](outer!, 0, si^);
                    let so = outer^.share;
                    // Give element twice from shared outer — each increments reference count.
                    let copy1 = array_give[Array[Data], shared, shared[so]](so.share, 0);
                    let copy2 = array_give[Array[Data], shared, shared[so]](so.share, 0);
                    // All three can read the same Data — shared, no move.
                    print(array_give[Data, shared, shared](copy1^, 0));
                    print(array_give[Data, shared, shared](copy2^, 0));
                    print(array_give[Data, shared, shared](si^, 0));
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Data](1) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, ! [_1_inner]](_1_inner ! , 0 , new Data (77)) ;
            Output: Trace:   let _1_si = _1_inner ^ . share ;
            Output: Trace:   _1_si = shared Array { flag: SharedOwned, rc: 1, Data { x: 77 } }
            Output: Trace:   let _1_outer = array_new [Array[Data]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Data], ! [_1_outer]](_1_outer ! , 0 , _1_si ^) ;
            Output: Trace:   let _1_so = _1_outer ^ . share ;
            Output: Trace:   _1_so = shared Array { flag: SharedOwned, rc: 1, Array { flag: SharedOwned, rc: 2, Data { x: 77 } } }
            Output: Trace:   let _1_copy1 = array_give [Array[Data], shared, shared [_1_so]](_1_so . share , 0) ;
            Output: Trace:   _1_copy1 = shared Array { flag: SharedOwned, rc: 3, Data { x: 77 } }
            Output: Trace:   let _1_copy2 = array_give [Array[Data], shared, shared [_1_so]](_1_so . share , 0) ;
            Output: Trace:   _1_copy2 = shared Array { flag: SharedOwned, rc: 4, Data { x: 77 } }
            Output: Trace:   print(array_give [Data, shared, shared](_1_copy1 ^ , 0)) ;
            Output: ----->   shared Data { x: 77 }
            Output: Trace:   print(array_give [Data, shared, shared](_1_copy2 ^ , 0)) ;
            Output: ----->   shared Data { x: 77 }
            Output: Trace:   print(array_give [Data, shared, shared](_1_si ^ , 0)) ;
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
    // shared Array[Array[Data]]: P=given but runtime element is shared.
    // array_give correctly produces a shared copy (rc++) rather than a move,
    // because the runtime Shared flags override the static P=given.
    // The inner array backing leaks (rc=1) because arrays don't drop
    // their elements — the outer's scrub doesn't decrement the inner's rc.
    crate::assert_interpret_only!(
        {
            struct Data { x: Int; }
            struct Main {
                fn main(given self) -> Int {
                    let inner = array_new[Data](1);
                    array_write[Data, ![inner]](inner!, 0, new Data(55));
                    let si = inner^.share;
                    let outer = array_new[Array[Data]](1);
                    array_write[Array[Data], ![outer]](outer!, 0, si^);
                    let so = outer^.share;
                    // Give a copy from outer: runtime flags are Shared, so this
                    // produces a shared copy (rc++) not a move.
                    let copy1 = array_give[Array[Data], given, shared[so]](so.share, 0);
                    drop copy1;
                    drop so;
                    drop si;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Data](1) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, ! [_1_inner]](_1_inner ! , 0 , new Data (55)) ;
            Output: Trace:   let _1_si = _1_inner ^ . share ;
            Output: Trace:   _1_si = shared Array { flag: SharedOwned, rc: 1, Data { x: 55 } }
            Output: Trace:   let _1_outer = array_new [Array[Data]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Data], ! [_1_outer]](_1_outer ! , 0 , _1_si ^) ;
            Output: Trace:   let _1_so = _1_outer ^ . share ;
            Output: Trace:   _1_so = shared Array { flag: SharedOwned, rc: 1, Array { flag: SharedOwned, rc: 2, Data { x: 55 } } }
            Output: Trace:   let _1_copy1 = array_give [Array[Data], given, shared [_1_so]](_1_so . share , 0) ;
            Output: Trace:   _1_copy1 = Array { flag: SharedOwned, rc: 3, Data { x: 55 } }
            Output: Trace:   drop _1_copy1 ;
            Output: Trace:   drop _1_so ;
            Output: Trace:   drop _1_si ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x03: [RefCount(1), Capacity(1), Int(55)]
            Alloc 0x1e: [Int(0)]"#]]
    );
}

// ---------------------------------------------------------------
// ArrayDrop: Shared and SharedPlace elements
// ---------------------------------------------------------------

#[test]
fn array_drop_shared_element_decrements_refcount() {
    // Array element with Shared flags: ArrayDrop should call drop_owned_value,
    // which for an array element decrements its reference count.
    crate::assert_interpret_only!(
        {
            struct Main {
                fn main(given self) -> Int {
                    let inner = array_new[Int](1);
                    array_write[Int, ![inner]](inner!, 0, 42);
                    let si = inner^.share;
                    let outer = array_new[Array[Int]](1);
                    array_write[Array[Int], ![outer]](outer!, 0, si^);
                    // Element in outer is shared Array[Int] — reference count 2.
                    // Drop it: reference count → 1. si var still valid.
                    array_drop[Array[Int], given, ![outer]](outer!, 0, 1);
                    array_give[Int, given, shared](si^, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Int](1) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_inner]](_1_inner ! , 0 , 42) ;
            Output: Trace:   let _1_si = _1_inner ^ . share ;
            Output: Trace:   _1_si = shared Array { flag: SharedOwned, rc: 1, 42 }
            Output: Trace:   let _1_outer = array_new [Array[Int]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Int], ! [_1_outer]](_1_outer ! , 0 , _1_si ^) ;
            Output: Trace:   array_drop [Array[Int], given, ! [_1_outer]](_1_outer ! , 0 , 1) ;
            Output: Trace:   array_give [Int, given, shared](_1_si ^ , 0) ;
            Output: Trace: exit Main.main => 42
            Result: Ok: 42
            Alloc 0x1a: [Int(42)]"#]]
    );
}

#[test]
fn array_drop_shared_class_element() {
    // Even though Pt is a `shared struct` (copy type), array_drop with P=given
    // actually drops the element. P=given means "I own these, clean them up."
    // This is needed to avoid leaks: a shared struct with boxed fields would
    // leak reference counts if array_drop were a no-op.
    crate::assert_interpret_fault!(
        {
            shared struct Pt { x: Int; y: Int; }
            struct Main {
                fn main(given self) -> Pt {
                    let a = array_new[Pt](1);
                    array_write[Pt, ![a]](a!, 0, new Pt(1, 2));
                    array_drop[Pt, given, ![a]](a!, 0, 1);
                    // Element is now uninitialized — giving it should fault.
                    array_give[Pt, given, given](a^, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Pt](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Pt { x: ⚡, y: ⚡ } }
            Output: Trace:   array_write [Pt, ! [_1_a]](_1_a ! , 0 , new Pt (1, 2)) ;
            Output: Trace:   array_drop [Pt, given, ! [_1_a]](_1_a ! , 0 , 1) ;
            Output: Trace:   array_give [Pt, given, given](_1_a ^ , 0) ;
            Result: Fault: access of uninitialized value
            Alloc 0x03: [RefCount(1), Capacity(1), Uninitialized, Uninitialized]
            Alloc 0x10: [Flags(Given), Pointer(0x03)]"#]]
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
            struct Container {
                items: Array[Int];
            }
            struct Main {
                fn main(given self) -> Int {
                    let outer = array_new[Container](1);
                    let inner = array_new[Int](2);
                    array_write[Int, ![inner]](inner!, 0, 10);
                    array_write[Int, ![inner]](inner!, 1, 20);
                    let c = new Container(inner^);
                    array_write[Container, ![outer]](outer!, 0, c^);
                    // Read the container's inner array via give
                    let got = array_give[Container, given, given](outer^, 0);
                    print(got^);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_outer = array_new [Container](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, Container { items: ⚡ } }
            Output: Trace:   let _1_inner = array_new [Int](2) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_inner]](_1_inner ! , 0 , 10) ;
            Output: Trace:   array_write [Int, ! [_1_inner]](_1_inner ! , 1 , 20) ;
            Output: Trace:   let _1_c = new Container (_1_inner ^) ;
            Output: Trace:   _1_c = Container { items: Array { flag: Given, rc: 1, 10, 20 } }
            Output: Trace:   array_write [Container, ! [_1_outer]](_1_outer ! , 0 , _1_c ^) ;
            Output: Trace:   let _1_got = array_give [Container, given, given](_1_outer ^ , 0) ;
            Output: Trace:   _1_got = Container { items: Array { flag: Given, rc: 1, 10, 20 } }
            Output: Trace:   print(_1_got ^) ;
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
    // Should recursively drop: class element → inner array (reference count→0, freed).
    crate::assert_interpret_only!(
        {
            struct Container {
                items: Array[Int];
            }
            struct Main {
                fn main(given self) -> Int {
                    let outer = array_new[Container](1);
                    let inner = array_new[Int](1);
                    array_write[Int, ![inner]](inner!, 0, 99);
                    print(inner.share);
                    let c = new Container(inner^);
                    print(c.share);
                    array_write[Container, ![outer]](outer!, 0, c^);
                    print(outer.share);
                    // Drop the container element — inner array should be freed.
                    array_drop[Container, given, ![outer]](outer!, 0, 1);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_outer = array_new [Container](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, Container { items: ⚡ } }
            Output: Trace:   let _1_inner = array_new [Int](1) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_inner]](_1_inner ! , 0 , 99) ;
            Output: Trace:   print(_1_inner . share) ;
            Output: ----->   shared [_1_inner] Array { flag: SharedPlace, rc: 1, 99 }
            Output: Trace:   let _1_c = new Container (_1_inner ^) ;
            Output: Trace:   _1_c = Container { items: Array { flag: Given, rc: 1, 99 } }
            Output: Trace:   print(_1_c . share) ;
            Output: ----->   shared [_1_c] Container { items: Array { flag: SharedPlace, rc: 1, 99 } }
            Output: Trace:   array_write [Container, ! [_1_outer]](_1_outer ! , 0 , _1_c ^) ;
            Output: Trace:   print(_1_outer . share) ;
            Output: ----->   shared [_1_outer] Array { flag: SharedPlace, rc: 1, Container { items: Array { flag: Given, rc: 1, 99 } } }
            Output: Trace:   array_drop [Container, given, ! [_1_outer]](_1_outer ! , 0 , 1) ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x1f: [Int(0)]"#]]
    );
}

#[test]
fn array_share_uninitialized() {
    // Sharing a newly created array with uninitialized elements succeeds —
    // array elements are user-managed (unsafe), so share doesn't traverse them.
    crate::assert_interpret_only!(
        {
            struct Container {
                items: Array[Int];
            }
            struct Main {
                fn main(given self) -> Int {
                    let outer = array_new[Container](1).share;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_outer = array_new [Container](1) . share ;
            Output: Trace:   _1_outer = shared Array { flag: SharedOwned, rc: 1, Container { items: ⚡ } }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x06: [Int(0)]"#]]
    );
}

// ---------------------------------------------------------------
// Sharing paths: a.share on shared array
// ---------------------------------------------------------------

#[test]
fn shared_array_give_increments_refcount() {
    // Giving a shared array increments the reference count.
    // After dropping the original, the copy keeps the array alive.
    crate::assert_interpret_only!(
        {
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](1);
                    array_write[Int, ![a]](a!, 0, 55);
                    let s = a^.share;
                    let b = s^;
                    drop s;
                    // b is a shared copy — give incremented reference count.
                    // After s.drop, reference count is still > 0.
                    array_give[Int, given, shared](b^, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 0 , 55) ;
            Output: Trace:   let _1_s = _1_a ^ . share ;
            Output: Trace:   _1_s = shared Array { flag: SharedOwned, rc: 1, 55 }
            Output: Trace:   let _1_b = _1_s ^ ;
            Output: Trace:   _1_b = shared Array { flag: SharedOwned, rc: 2, 55 }
            Output: Trace:   drop _1_s ;
            Output: Trace:   array_give [Int, given, shared](_1_b ^ , 0) ;
            Output: Trace: exit Main.main => 55
            Result: Ok: 55
            Alloc 0x11: [Int(55)]"#]]
    );
}

// ---------------------------------------------------------------
// Place sharing for arrays
// ---------------------------------------------------------------

#[test]
fn ref_array_print() {
    // Taking a place sharing to an array and printing it.
    crate::assert_interpret_only!(
        {
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_write[Int, ![a]](a!, 0, 10);
                    array_write[Int, ![a]](a!, 1, 20);
                    print(a.share);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 0 , 10) ;
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 1 , 20) ;
            Output: Trace:   print(_1_a . share) ;
            Output: ----->   shared [_1_a] Array { flag: SharedPlace, rc: 1, 10, 20 }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x10: [Int(0)]"#]]
    );
}

#[test]
fn ref_array_give_int_element() {
    // Giving an Int element from a place sharing array with P=place sharing yields a copy.
    // Int is a shared struct (copy type), so place sharing produces a copy.
    crate::assert_interpret_only!(
        {
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_write[Int, ![a]](a!, 0, 42);
                    array_write[Int, ![a]](a!, 1, 99);
                    let x = array_give[Int, shared[a], shared[a]](a.share, 0);
                    let y = array_give[Int, shared[a], shared[a]](a.share, 1);
                    print(x^);
                    print(y^);
                    // Original array still intact — place sharing didn't move elements.
                    print(a.share);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 0 , 42) ;
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 1 , 99) ;
            Output: Trace:   let _1_x = array_give [Int, shared [_1_a], shared [_1_a]](_1_a . share , 0) ;
            Output: Trace:   _1_x = 42
            Output: Trace:   let _1_y = array_give [Int, shared [_1_a], shared [_1_a]](_1_a . share , 1) ;
            Output: Trace:   _1_y = 99
            Output: Trace:   print(_1_x ^) ;
            Output: ----->   42
            Output: Trace:   print(_1_y ^) ;
            Output: ----->   99
            Output: Trace:   print(_1_a . share) ;
            Output: ----->   shared [_1_a] Array { flag: SharedPlace, rc: 1, 42, 99 }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x1c: [Int(0)]"#]]
    );
}

#[test]
fn ref_array_give_class_element() {
    // Giving a class element with P=place sharing yields a borrowed copy (place sharing flags on boxed fields).
    crate::assert_interpret_only!(
        {
            struct Data {
                x: Int;
            }
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Data](1);
                    array_write[Data, ![a]](a!, 0, new Data(42));
                    let d = array_give[Data, shared[a], shared[a]](a.share, 0);
                    print(d^);
                    // Original still intact.
                    print(a.share);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, ! [_1_a]](_1_a ! , 0 , new Data (42)) ;
            Output: Trace:   let _1_d = array_give [Data, shared [_1_a], shared [_1_a]](_1_a . share , 0) ;
            Output: Trace:   _1_d = shared [_1_a] Data { x: 42 }
            Output: Trace:   print(_1_d ^) ;
            Output: ----->   shared [_1_a] Data { x: 42 }
            Output: Trace:   print(_1_a . share) ;
            Output: ----->   shared [_1_a] Array { flag: SharedPlace, rc: 1, Data { x: 42 } }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x13: [Int(0)]"#]]
    );
}

#[test]
fn ref_array_of_shared_arrays() {
    // place sharing to Array[shared Array[Int]]: the outer array holds shared inner arrays.
    // Giving an element with P=place sharing through a place sharing to the outer produces a
    // borrowed copy of the shared inner array (flag: SharedPlace, rc incremented
    // to keep backing alive).
    crate::assert_interpret_only!(
        {
            struct Main {
                fn main(given self) -> Int {
                    let inner = array_new[Int](2);
                    array_write[Int, ![inner]](inner!, 0, 10);
                    array_write[Int, ![inner]](inner!, 1, 20);
                    let si = inner^.share;
                    let outer = array_new[shared Array[Int]](1);
                    array_write[shared Array[Int], ![outer]](outer!, 0, si^);
                    // outer holds shared Array[Int] elements.
                    // Take a place sharing to outer, give the element with P=place sharing.
                    let got = array_give[shared Array[Int], shared[outer], shared[outer]](outer.share, 0);
                    print(got^);
                    // Original outer still intact.
                    print(outer.share);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Int](2) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_inner]](_1_inner ! , 0 , 10) ;
            Output: Trace:   array_write [Int, ! [_1_inner]](_1_inner ! , 1 , 20) ;
            Output: Trace:   let _1_si = _1_inner ^ . share ;
            Output: Trace:   _1_si = shared Array { flag: SharedOwned, rc: 1, 10, 20 }
            Output: Trace:   let _1_outer = array_new [shared Array[Int]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, shared ⚡ }
            Output: Trace:   array_write [shared Array[Int], ! [_1_outer]](_1_outer ! , 0 , _1_si ^) ;
            Output: Trace:   let _1_got = array_give [shared Array[Int], shared [_1_outer], shared [_1_outer]](_1_outer . share , 0) ;
            Output: Trace:   _1_got = shared Array { flag: SharedOwned, rc: 3, 10, 20 }
            Output: Trace:   print(_1_got ^) ;
            Output: ----->   shared Array { flag: SharedOwned, rc: 4, 10, 20 }
            Output: Trace:   print(_1_outer . share) ;
            Output: ----->   shared [_1_outer] Array { flag: SharedPlace, rc: 1, shared Array { flag: SharedOwned, rc: 3, 10, 20 } }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x03: [RefCount(1), Capacity(2), Int(10), Int(20)]
            Alloc 0x20: [Int(0)]"#]]
    );
}

// ---------------------------------------------------------------
// Phase 3.5: Static place sharing, runtime shared — mismatch scenario
// ---------------------------------------------------------------

#[test]
fn array_give_ref_of_runtime_shared_element() {
    // The element type is shared[dummy] Array[Int] — the array holds borrowed arrays.
    // But at runtime, the stored element has Shared flags (came from .share;
    // shared ≤ place sharing so this is valid). array_give with P=place sharing dispatches on the
    // static type `shared[outer] shared[dummy] Array[Int]` — what happens?
    crate::assert_interpret_only!(
        {
            struct Main {
                fn main(given self) -> Int {
                    let inner = array_new[Int](1);
                    array_write[Int, ![inner]](inner!, 0, 42);
                    let shared_inner = inner^.share;
                    // dummy variable so we can write shared[dummy] as the element type.
                    let dummy = array_new[Int](0);
                    // Element type is shared[dummy] Array[Int], but we store a shared array.
                    let outer = array_new[shared[dummy] Array[Int]](1);
                    array_write[shared[dummy] Array[Int], ![outer]](outer!, 0, shared_inner^);
                    // Give with P=place sharing: static type says place sharing, runtime flags say Shared.
                    let got = array_give[shared[dummy] Array[Int], shared[outer], shared[outer]](outer.share, 0);
                    print(got^);
                    // Is the reference count correct? Is the element still intact?
                    print(outer.share);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Int](1) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_inner]](_1_inner ! , 0 , 42) ;
            Output: Trace:   let _1_shared_inner = _1_inner ^ . share ;
            Output: Trace:   _1_shared_inner = shared Array { flag: SharedOwned, rc: 1, 42 }
            Output: Trace:   let _1_dummy = array_new [Int](0) ;
            Output: Trace:   _1_dummy = Array { flag: Given, rc: 1 }
            Output: Trace:   let _1_outer = array_new [shared [_1_dummy] Array[Int]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, shared [_1_dummy] ⚡ }
            Output: Trace:   array_write [shared [_1_dummy] Array[Int], ! [_1_outer]](_1_outer ! , 0 , _1_shared_inner ^) ;
            Output: Trace:   let _1_got = array_give [shared [_1_dummy] Array[Int], shared [_1_outer], shared [_1_outer]](_1_outer . share , 0) ;
            Output: Trace:   _1_got = shared [_1_dummy] Array { flag: SharedOwned, rc: 3, 42 }
            Output: Trace:   print(_1_got ^) ;
            Output: ----->   shared [_1_dummy] Array { flag: SharedOwned, rc: 4, 42 }
            Output: Trace:   print(_1_outer . share) ;
            Output: ----->   shared [_1_outer] Array { flag: SharedPlace, rc: 1, shared [_1_dummy] Array { flag: SharedOwned, rc: 3, 42 } }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x03: [RefCount(1), Capacity(1), Int(42)]
            Alloc 0x20: [Int(0)]"#]]
    );
}

// ---------------------------------------------------------------
// Phase 3: Poly-permission semantics tests
// ---------------------------------------------------------------

#[test]
fn array_give_p_mut() {
    // array_give with P=mut returns a mutable reference to the element.
    crate::assert_interpret_only!(
        {
            struct Data { x: Int; }
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Data](1);
                    array_write[Data, ![a]](a!, 0, new Data(42));
                    let d = array_give[Data, ![a], shared[a]](a.share, 0);
                    print(d.share);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, ! [_1_a]](_1_a ! , 0 , new Data (42)) ;
            Output: Trace:   let _1_d = array_give [Data, ! [_1_a], shared [_1_a]](_1_a . share , 0) ;
            Output: Trace:   _1_d = ! [_1_a] Data { x: 42 }
            Output: Trace:   print(_1_d . share) ;
            Output: ----->   shared [_1_d] ! [_1_a] Data { x: 42 }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x11: [Int(0)]"#]]
    );
}

#[test]
fn array_give_p_shared() {
    // array_give with P=shared returns a shared copy, rc incremented.
    crate::assert_interpret_only!(
        {
            struct Main {
                fn main(given self) -> Int {
                    let inner = array_new[Int](1);
                    array_write[Int, ![inner]](inner!, 0, 77);
                    let s = inner^.share;
                    let outer = array_new[Array[Int]](1);
                    array_write[Array[Int], ![outer]](outer!, 0, s^);
                    // Give with P=shared: should produce a shared copy with rc++
                    let got = array_give[Array[Int], shared, shared[outer]](outer.share, 0);
                    print(got^);
                    // Original still intact
                    print(outer.share);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Int](1) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_inner]](_1_inner ! , 0 , 77) ;
            Output: Trace:   let _1_s = _1_inner ^ . share ;
            Output: Trace:   _1_s = shared Array { flag: SharedOwned, rc: 1, 77 }
            Output: Trace:   let _1_outer = array_new [Array[Int]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Int], ! [_1_outer]](_1_outer ! , 0 , _1_s ^) ;
            Output: Trace:   let _1_got = array_give [Array[Int], shared, shared [_1_outer]](_1_outer . share , 0) ;
            Output: Trace:   _1_got = shared Array { flag: SharedOwned, rc: 3, 77 }
            Output: Trace:   print(_1_got ^) ;
            Output: ----->   shared Array { flag: SharedOwned, rc: 4, 77 }
            Output: Trace:   print(_1_outer . share) ;
            Output: ----->   shared [_1_outer] Array { flag: SharedPlace, rc: 1, Array { flag: SharedOwned, rc: 3, 77 } }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x03: [RefCount(1), Capacity(1), Int(77)]
            Alloc 0x1c: [Int(0)]"#]]
    );
}

#[test]
fn array_give_p_ref() {
    // array_give with P=place sharing returns a borrowed copy.
    crate::assert_interpret_only!(
        {
            struct Main {
                fn main(given self) -> Int {
                    let inner = array_new[Int](1);
                    array_write[Int, ![inner]](inner!, 0, 55);
                    let outer = array_new[Array[Int]](1);
                    array_write[Array[Int], ![outer]](outer!, 0, inner^);
                    // Give with P=place sharing: should produce a borrowed copy
                    let got = array_give[Array[Int], shared[outer], shared[outer]](outer.share, 0);
                    print(got^);
                    // Original still intact
                    print(outer.share);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Int](1) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_inner]](_1_inner ! , 0 , 55) ;
            Output: Trace:   let _1_outer = array_new [Array[Int]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Int], ! [_1_outer]](_1_outer ! , 0 , _1_inner ^) ;
            Output: Trace:   let _1_got = array_give [Array[Int], shared [_1_outer], shared [_1_outer]](_1_outer . share , 0) ;
            Output: Trace:   _1_got = shared [_1_outer] Array { flag: SharedPlace, rc: 1, 55 }
            Output: Trace:   print(_1_got ^) ;
            Output: ----->   shared [_1_outer] Array { flag: SharedPlace, rc: 1, 55 }
            Output: Trace:   print(_1_outer . share) ;
            Output: ----->   shared [_1_outer] Array { flag: SharedPlace, rc: 1, Array { flag: Given, rc: 1, 55 } }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x03: [RefCount(1), Capacity(1), Int(55)]
            Alloc 0x1a: [Int(0)]"#]]
    );
}

#[test]
fn array_drop_p_shared_is_noop() {
    // array_drop with P=shared should be a no-op — element still accessible.
    crate::assert_interpret_only!(
        {
            struct Data { x: Int; }
            struct Main {
                fn main(given self) -> Data {
                    let a = array_new[Data](1);
                    array_write[Data, ![a]](a!, 0, new Data(42));
                    array_drop[Data, shared, shared[a]](a.share, 0, 1);
                    // Element still accessible — shared drop is a no-op.
                    array_give[Data, given, given](a^, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, ! [_1_a]](_1_a ! , 0 , new Data (42)) ;
            Output: Trace:   array_drop [Data, shared, shared [_1_a]](_1_a . share , 0 , 1) ;
            Output: Trace:   array_give [Data, given, given](_1_a ^ , 0) ;
            Output: Trace: exit Main.main => Data { x: 42 }
            Result: Ok: Data { x: 42 }
            Alloc 0x11: [Int(42)]"#]]
    );
}

#[test]
fn array_drop_p_given_range() {
    // array_drop with P=given on a range of elements drops all of them.
    crate::assert_interpret_fault!(
        {
            struct Data { x: Int; }
            struct Main {
                fn main(given self) -> Data {
                    let a = array_new[Data](3);
                    array_write[Data, ![a]](a!, 0, new Data(10));
                    array_write[Data, ![a]](a!, 1, new Data(20));
                    array_write[Data, ![a]](a!, 2, new Data(30));
                    // Drop elements 0, 1, 2
                    array_drop[Data, given, shared[a]](a.share, 0, 3);
                    // All elements are now uninitialized — giving any should fault.
                    array_give[Data, given, given](a^, 1);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](3) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ }, Data { x: ⚡ }, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, ! [_1_a]](_1_a ! , 0 , new Data (10)) ;
            Output: Trace:   array_write [Data, ! [_1_a]](_1_a ! , 1 , new Data (20)) ;
            Output: Trace:   array_write [Data, ! [_1_a]](_1_a ! , 2 , new Data (30)) ;
            Output: Trace:   array_drop [Data, given, shared [_1_a]](_1_a . share , 0 , 3) ;
            Output: Trace:   array_give [Data, given, given](_1_a ^ , 1) ;
            Result: Fault: access of uninitialized value
            Alloc 0x03: [RefCount(1), Capacity(3), Uninitialized, Uninitialized, Uninitialized]
            Alloc 0x19: [Flags(Given), Pointer(0x03)]"#]]
    );
}

#[test]
fn array_give_p_given_int_is_copy() {
    // Giving an Int element with P=given copies without uninitializing.
    // Even though P = given, the combined type `given Int` is shared/copy
    // (Int is a shared struct), so array_give copies rather than moving.
    crate::assert_interpret_only!(
        {
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](1);
                    array_write[Int, ![a]](a!, 0, 42);
                    let x = array_give[Int, given, shared[a]](a.share, 0);
                    // Element still accessible — Int is shared, no move
                    let y = array_give[Int, given, given](a^, 0);
                    x^ + y^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_a]](_1_a ! , 0 , 42) ;
            Output: Trace:   let _1_x = array_give [Int, given, shared [_1_a]](_1_a . share , 0) ;
            Output: Trace:   _1_x = 42
            Output: Trace:   let _1_y = array_give [Int, given, given](_1_a ^ , 0) ;
            Output: Trace:   _1_y = 42
            Output: Trace:   _1_x ^ + _1_y ^ ;
            Output: Trace: exit Main.main => 84
            Result: Ok: 84
            Alloc 0x14: [Int(84)]"#]]
    );
}

#[test]
fn array_drop_empty_range_is_noop() {
    // array_drop with from >= to is a no-op.
    crate::assert_interpret_only!(
        {
            struct Data { x: Int; }
            struct Main {
                fn main(given self) -> Data {
                    let a = array_new[Data](2);
                    array_write[Data, ![a]](a!, 0, new Data(42));
                    array_write[Data, ![a]](a!, 1, new Data(99));
                    // from >= to: no-op
                    array_drop[Data, given, shared[a]](a.share, 1, 1);
                    array_drop[Data, given, shared[a]](a.share, 2, 0);
                    // Elements still accessible
                    array_give[Data, given, given](a^, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ }, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, ! [_1_a]](_1_a ! , 0 , new Data (42)) ;
            Output: Trace:   array_write [Data, ! [_1_a]](_1_a ! , 1 , new Data (99)) ;
            Output: Trace:   array_drop [Data, given, shared [_1_a]](_1_a . share , 1 , 1) ;
            Output: Trace:   array_drop [Data, given, shared [_1_a]](_1_a . share , 2 , 0) ;
            Output: Trace:   array_give [Data, given, given](_1_a ^ , 0) ;
            Output: Trace: exit Main.main => Data { x: 42 }
            Result: Ok: Data { x: 42 }
            Alloc 0x1a: [Int(42)]"#]]
    );
}

// ---------------------------------------------------------------
// Phase 3.5: Intentional leak tests
// ---------------------------------------------------------------

#[test]
fn array_leak_all_elements() {
    // Drop array without dropping any elements. The backing allocation is freed
    // (scrubbed) but boxed element allocations remain as orphans in the heap.
    // Documents the unsafe contract: array does NOT drop its elements.
    // Uses Array[Array[Int]] so inner arrays are boxed and have separate
    // heap allocations that survive the outer array's scrub.
    crate::assert_interpret_only!(
        {
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Array[Int]](2);
                    let e0 = array_new[Int](1);
                    array_write[Int, ![e0]](e0!, 0, 10);
                    let e1 = array_new[Int](1);
                    array_write[Int, ![e1]](e1!, 0, 20);
                    array_write[Array[Int], ![a]](a!, 0, e0^);
                    array_write[Array[Int], ![a]](a!, 1, e1^);
                    // Drop the outer array without dropping elements first.
                    // Inner array backing allocations leak.
                    drop a;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Array[Int]](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   let _1_e0 = array_new [Int](1) ;
            Output: Trace:   _1_e0 = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_e0]](_1_e0 ! , 0 , 10) ;
            Output: Trace:   let _1_e1 = array_new [Int](1) ;
            Output: Trace:   _1_e1 = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_e1]](_1_e1 ! , 0 , 20) ;
            Output: Trace:   array_write [Array[Int], ! [_1_a]](_1_a ! , 0 , _1_e0 ^) ;
            Output: Trace:   array_write [Array[Int], ! [_1_a]](_1_a ! , 1 , _1_e1 ^) ;
            Output: Trace:   drop _1_a ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x07: [RefCount(1), Capacity(1), Int(10)]
            Alloc 0x0f: [RefCount(1), Capacity(1), Int(20)]
            Alloc 0x1f: [Int(0)]"#]]
    );
}

#[test]
fn array_leak_some_elements() {
    // Drop element 0 of a 2-element array, skip element 1, drop array.
    // Element 1's backing allocation remains as an orphan in the heap.
    crate::assert_interpret_only!(
        {
            struct Main {
                fn main(given self) -> Int {
                    let a = array_new[Array[Int]](2);
                    let e0 = array_new[Int](1);
                    array_write[Int, ![e0]](e0!, 0, 10);
                    let e1 = array_new[Int](1);
                    array_write[Int, ![e1]](e1!, 0, 20);
                    array_write[Array[Int], ![a]](a!, 0, e0^);
                    array_write[Array[Int], ![a]](a!, 1, e1^);
                    // Drop only element 0.
                    array_drop[Array[Int], given, shared[a]](a.share, 0, 1);
                    // Drop the array — element 1 leaks.
                    drop a;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Array[Int]](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   let _1_e0 = array_new [Int](1) ;
            Output: Trace:   _1_e0 = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_e0]](_1_e0 ! , 0 , 10) ;
            Output: Trace:   let _1_e1 = array_new [Int](1) ;
            Output: Trace:   _1_e1 = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, ! [_1_e1]](_1_e1 ! , 0 , 20) ;
            Output: Trace:   array_write [Array[Int], ! [_1_a]](_1_a ! , 0 , _1_e0 ^) ;
            Output: Trace:   array_write [Array[Int], ! [_1_a]](_1_a ! , 1 , _1_e1 ^) ;
            Output: Trace:   array_drop [Array[Int], given, shared [_1_a]](_1_a . share , 0 , 1) ;
            Output: Trace:   drop _1_a ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x0f: [RefCount(1), Capacity(1), Int(20)]
            Alloc 0x23: [Int(0)]"#]]
    );
}
