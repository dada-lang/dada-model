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
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](3) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ }
            Output: Trace:   let _1_w = new Wrapper (_1_a . give) ;
            Output: Trace:   _1_w = Wrapper { field: Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ } }
            Output: Trace:   array_capacity [Int, given](_1_w . field . give) ;
            Output: Trace: exit Main.main => 3
            Result: Ok: 3
            Alloc 0x0a: [Int(3)]"#]])
    );
}

#[test]
fn reassign_drops_old_array() {
    // Reassigning a variable that holds an Array should drop (decrement
    // refcount of) the old array before installing the new one.
    // If the old array were leaked the refcount would never reach zero
    // and its allocation would still appear in the heap snapshot.
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 0 , 1) ;
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 1 , 2) ;
            Output: Trace:   _1_a = array_new [Int](4) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡, ⚡ }
            Output: Trace:   array_capacity [Int, given](_1_a . give) ;
            Output: Trace: exit Main.main => 4
            Result: Ok: 4
            Alloc 0x13: [Int(4)]"#]])
    );
}

// ---------------------------------------------------------------
// Basic array creation and capacity
// ---------------------------------------------------------------

#[test]
fn array_new_and_capacity() {
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](3);
                    array_capacity[Int, given](a.give);
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](3) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ }
            Output: Trace:   array_capacity [Int, given](_1_a . give) ;
            Output: Trace: exit Main.main => 3
            Result: Ok: 3
            Alloc 0x07: [Int(3)]"#]])
    );
}

#[test]
fn array_size_of() {
    // Array[T] is two words: Word::Flags + Word::Pointer
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    size_of[Array[Int]]();
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   size_of [Array[Int]]() ;
            Output: Trace: exit Main.main => 2
            Result: Ok: 2
            Alloc 0x02: [Int(2)]"#]])
    );
}

// ---------------------------------------------------------------
// Initialize and get — Int elements
// ---------------------------------------------------------------

#[test]
fn array_write_and_get_int() {
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](3) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 1 , 20) ;
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 2 , 30) ;
            Output: Trace:   print(array_give [Int, given, ref [_1_a]](_1_a . ref , 0)) ;
            Output: ----->   10
            Output: Trace:   print(array_give [Int, given, ref [_1_a]](_1_a . ref , 1)) ;
            Output: ----->   20
            Output: Trace:   array_give [Int, given, given](_1_a . give , 2) ;
            Output: Trace: exit Main.main => 30
            Result: Ok: 30
            Alloc 0x1c: [Int(30)]"#]])
    );
}

// ---------------------------------------------------------------
// Initialize and get — class elements
// ---------------------------------------------------------------

#[test]
fn array_write_and_get_class() {
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ }, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [_1_a]](_1_a . mut , 0 , new Data (42)) ;
            Output: Trace:   array_write [Data, mut [_1_a]](_1_a . mut , 1 , new Data (99)) ;
            Output: Trace:   print(array_give [Data, given, ref [_1_a]](_1_a . ref , 0)) ;
            Output: ----->   Data { x: 42 }
            Output: Trace:   array_give [Data, given, given](_1_a . give , 1) ;
            Output: Trace: exit Main.main => Data { x: 99 }
            Result: Ok: Data { x: 99 }
            Alloc 0x16: [Int(99)]"#]])
    );
}

// ---------------------------------------------------------------
// Error cases: uninitialized access
// ---------------------------------------------------------------

#[test]
// NOTE: future-panic test. Type checker correctly accepts; fault is a runtime bounds/init check.
fn array_give_uninitialized_faults() {
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](3);
                    array_give[Int, given, given](a.give, 0);
                }
            }
        },
        type: ok, interpret: fault(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](3) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ }
            Output: Trace:   array_give [Int, given, given](_1_a . give , 0) ;
            Result: Fault: access of uninitialized value
            Alloc 0x03: [RefCount(1), Capacity(3), Uninitialized, Uninitialized, Uninitialized]
            Alloc 0x06: [Flags(Given), Pointer(0x03)]"#]])
    );
}

#[test]
fn array_give_int_is_copy() {
    // Int is a copy type — giving it doesn't uninitialize the source.
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 0 , 42) ;
            Output: Trace:   let _1_x = array_give [Int, given, ref [_1_a]](_1_a . ref , 0) ;
            Output: Trace:   _1_x = 42
            Output: Trace:   array_give [Int, given, given](_1_a . give , 0) ;
            Output: Trace: exit Main.main => 42
            Result: Ok: 42
            Alloc 0x10: [Int(42)]"#]])
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
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ }, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [_1_a]](_1_a . mut , 0 , new Data (42)) ;
            Output: Trace:   array_write [Data, mut [_1_a]](_1_a . mut , 1 , new Data (99)) ;
            Output: Trace:   array_give [Data, given, given](_1_a . give , 0) ;
            Output: Trace: exit Main.main => Data { x: 42 }
            Result: Ok: Data { x: 42 }
            Alloc 0x12: [Int(42)]"#]])
    );
}

#[test]
fn shared_array_give_class_is_shared_copy() {
    // Shared array: class elements are given with shared semantics —
    // no move, element remains available for repeated gives.
    // P=shared produces a shared copy (rc++ on boxed fields).
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let a = array_new[Data](1);
                    array_write[Data, mut[a]](a.mut, 0, new Data(42));
                    let s = a.give.share;
                    let x = array_give[Data, shared, ref[s]](s.ref, 0);
                    print(x.give);
                    // Element still available — shared semantics, no move.
                    array_give[Data, shared, shared](s.give, 0);
                }
            }
        },
        type: error(expect_test::expect![[r#"src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }"#]]), interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [_1_a]](_1_a . mut , 0 , new Data (42)) ;
            Output: Trace:   let _1_s = _1_a . give . share ;
            Output: Trace:   _1_s = shared Array { flag: Shared, rc: 1, Data { x: 42 } }
            Output: Trace:   let _1_x = array_give [Data, shared, ref [_1_s]](_1_s . ref , 0) ;
            Output: Trace:   _1_x = shared Data { x: 42 }
            Output: Trace:   print(_1_x . give) ;
            Output: ----->   shared Data { x: 42 }
            Output: Trace:   array_give [Data, shared, shared](_1_s . give , 0) ;
            Output: Trace: exit Main.main => shared Data { x: 42 }
            Result: Ok: shared Data { x: 42 }
            Alloc 0x15: [Int(42)]"#]])
    );
}

// ---------------------------------------------------------------
// Error cases: out of bounds
// ---------------------------------------------------------------

#[test]
// NOTE: future-panic test. Type checker correctly accepts; fault is a runtime bounds/init check.
fn array_give_out_of_bounds() {
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_give[Int, given, given](a.give, 5);
                }
            }
        },
        type: ok, interpret: fault(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_give [Int, given, given](_1_a . give , 5) ;
            Result: Fault: array_give: index 5 out of bounds (capacity 2)
            Alloc 0x03: [RefCount(1), Capacity(2), Uninitialized, Uninitialized]
            Alloc 0x06: [Flags(Given), Pointer(0x03)]"#]])
    );
}

#[test]
// NOTE: future-panic test. Type checker correctly accepts; fault is a runtime bounds/init check.
fn array_write_out_of_bounds() {
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_write[Int, mut[a]](a.mut, 3, 42);
                    0;
                }
            }
        },
        type: ok, interpret: fault(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 3 , 42) ;
            Result: Fault: array_give: index 3 out of bounds (capacity 2)
            Alloc 0x03: [RefCount(1), Capacity(2), Uninitialized, Uninitialized]
            Alloc 0x04: [Flags(Given), Pointer(0x03)]
            Alloc 0x06: [MutRef(0x03)]"#]])
    );
}

// ---------------------------------------------------------------
// Double initialize
// ---------------------------------------------------------------

#[test]
fn array_write_overwrites_existing() {
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 0 , 20) ;
            Output: Trace:   array_give [Int, given, given](_1_a . give , 0) ;
            Output: Trace: exit Main.main => 20
            Result: Ok: 20
            Alloc 0x10: [Int(20)]"#]])
    );
}

/// array_write overwriting a shared array element should decrement refcount
/// and free the old array when refcount reaches zero.
#[test]
fn array_write_overwrites_shared_array() {
    crate::assert_interpret!(
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
        type: error(expect_test::expect![[r#"src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, inner: shared Array[Int], outer: Array[Array[Int]]}, assumptions: {}, fresh: 0 } }"#]]), interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_outer = array_new [Array[Int]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   let _1_inner = array_new [Int](0) . share ;
            Output: Trace:   _1_inner = shared Array { flag: Shared, rc: 1 }
            Output: Trace:   array_write [Array[Int], mut [_1_outer]](_1_outer . mut , 0 , _1_inner . give) ;
            Output: Trace:   let _1_replacement = array_new [Int](1) ;
            Output: Trace:   _1_replacement = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_replacement]](_1_replacement . mut , 0 , 99) ;
            Output: Trace:   print(_1_outer . ref) ;
            Output: ----->   ref [_1_outer] Array { flag: Borrowed, rc: 1, Array { flag: Shared, rc: 2 } }
            Output: Trace:   print(_1_inner . ref) ;
            Output: ----->   shared Array { flag: Borrowed, rc: 2 }
            Output: Trace:   print(_1_replacement . ref) ;
            Output: ----->   ref [_1_replacement] Array { flag: Borrowed, rc: 1, 99 }
            Output: Trace:   array_write [Array[Int], mut [_1_outer]](_1_outer . mut , 0 , _1_replacement . give) ;
            Output: Trace:   print(_1_outer . ref) ;
            Output: ----->   ref [_1_outer] Array { flag: Borrowed, rc: 1, Array { flag: Given, rc: 1, 99 } }
            Output: Trace:   print(_1_inner . ref) ;
            Output: ----->   shared Array { flag: Borrowed, rc: 2 }
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()
            Alloc 0x07: [RefCount(1), Capacity(0)]
            Alloc 0x0f: [RefCount(1), Capacity(1), Int(99)]"#]])
    );
}

// ---------------------------------------------------------------
// ArrayDrop
// ---------------------------------------------------------------

#[test]
// BUG: soundness gap — type checker accepts but interpreter faults (use after array_drop).
fn array_drop_element() {
    // Drop a class element (move type), then getting it should fault.
    // Note: Int is a copy type, so array_drop[Int, given, ...] would be a no-op.
    // We use Data (a move type) to test actual drop semantics.
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let a = array_new[Data](2);
                    array_write[Data, mut[a]](a.mut, 0, new Data(42));
                    array_drop[Data, given, mut[a]](a.mut, 0, 1);
                    array_give[Data, given, given](a.give, 0);
                }
            }
        },
        type: ok, interpret: fault(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ }, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [_1_a]](_1_a . mut , 0 , new Data (42)) ;
            Output: Trace:   array_drop [Data, given, mut [_1_a]](_1_a . mut , 0 , 1) ;
            Output: Trace:   array_give [Data, given, given](_1_a . give , 0) ;
            Result: Fault: access of uninitialized value
            Alloc 0x03: [RefCount(1), Capacity(2), Uninitialized, Uninitialized]
            Alloc 0x0f: [Flags(Given), Pointer(0x03)]"#]])
    );
}

#[test]
fn array_drop_class_element() {
    // Drop a class element — should recursively drop.
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Data](1);
                    array_write[Data, mut[a]](a.mut, 0, new Data(42));
                    array_drop[Data, given, mut[a]](a.mut, 0, 1);
                    0;
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [_1_a]](_1_a . mut , 0 , new Data (42)) ;
            Output: Trace:   array_drop [Data, given, mut [_1_a]](_1_a . mut , 0 , 1) ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x0f: [Int(0)]"#]])
    );
}

// ---------------------------------------------------------------
// Array give and share
// ---------------------------------------------------------------

#[test]
fn array_give() {
    // Giving a Given array moves it — new owner can access elements.
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](1);
                    let b = a.give;
                    array_capacity[Int, given](b.give);
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   let _1_b = _1_a . give ;
            Output: Trace:   _1_b = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_capacity [Int, given](_1_b . give) ;
            Output: Trace: exit Main.main => 1
            Result: Ok: 1
            Alloc 0x09: [Int(1)]"#]])
    );
}

#[test]
fn array_give_then_get() {
    // Give the array to a new variable, then use the new variable.
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 1 , 20) ;
            Output: Trace:   let _1_b = _1_a . give ;
            Output: Trace:   _1_b = Array { flag: Given, rc: 1, 10, 20 }
            Output: Trace:   array_give [Int, given, given](_1_b . give , 0) ;
            Output: Trace: exit Main.main => 10
            Result: Ok: 10
            Alloc 0x12: [Int(10)]"#]])
    );
}

#[test]
fn array_give_uninitializes_source() {
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](1);
                    let b = a.give;
                    array_capacity[Int, given](a.give);
                }
            }
        },
        type: error(expect_test::expect![[r#"
            src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Array[Int], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, a: Array[Int]}, assumptions: {}, fresh: 0 } }

            the rule "give" at (expressions.rs) failed because
              condition evaluated to false: `!live_after.is_live(place)`
                live_after = LivePlaces { accessed: {a}, traversed: {} }
                place = a"#]]), interpret: fault(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   let _1_b = _1_a . give ;
            Output: Trace:   _1_b = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_capacity [Int, given](_1_a . give) ;
            Result: Fault: access of uninitialized value
            Alloc 0x03: [RefCount(1), Capacity(1), Uninitialized]
            Alloc 0x06: [Flags(Given), Pointer(0x03)]"#]])
    );
}

#[test]
fn array_share() {
    // Sharing an array sets its flags to Shared.
    // A shared array can be given multiple times.
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 1 , 20) ;
            Output: Trace:   let _1_s = _1_a . give . share ;
            Output: Trace:   _1_s = shared Array { flag: Shared, rc: 1, 10, 20 }
            Output: Trace:   let _1_x = array_give [Int, given, ref [_1_s]](_1_s . ref , 0) ;
            Output: Trace:   _1_x = 10
            Output: Trace:   let _1_y = array_give [Int, given, shared](_1_s . give , 1) ;
            Output: Trace:   _1_y = 20
            Output: Trace:   _1_x . give + _1_y . give ;
            Output: Trace: exit Main.main => 30
            Result: Ok: 30
            Alloc 0x1a: [Int(30)]"#]])
    );
}

// ---------------------------------------------------------------
// Refcount lifecycle
// ---------------------------------------------------------------

#[test]
fn shared_array_survives_after_original_dropped() {
    // Share an array to two variables, drop one, the other still works.
    // The refcount goes: 1 (new) → shared → 2 (give to b) → 1 (a dropped) → use b.
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 1 , 20) ;
            Output: Trace:   let _1_s = _1_a . give . share ;
            Output: Trace:   _1_s = shared Array { flag: Shared, rc: 1, 10, 20 }
            Output: Trace:   let _1_b = _1_s . give ;
            Output: Trace:   _1_b = shared Array { flag: Shared, rc: 2, 10, 20 }
            Output: Trace:   _1_s . drop ;
            Output: Trace:   array_give [Int, given, shared](_1_b . give , 0) ;
            Output: Trace: exit Main.main => 10
            Result: Ok: 10
            Alloc 0x15: [Int(10)]"#]])
    );
}

#[test]
fn refcount_reaches_zero_frees_allocation() {
    // When the last reference is dropped, the backing allocation is freed.
    // The heap snapshot should show only the result Int — no array allocation.
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 1 , 20) ;
            Output: Trace:   let _1_s = _1_a . give . share ;
            Output: Trace:   _1_s = shared Array { flag: Shared, rc: 1, 10, 20 }
            Output: Trace:   let _1_b = _1_s . give ;
            Output: Trace:   _1_b = shared Array { flag: Shared, rc: 2, 10, 20 }
            Output: Trace:   _1_s . drop ;
            Output: Trace:   _1_b . drop ;
            Output: Trace:   42 ;
            Output: Trace: exit Main.main => 42
            Result: Ok: 42
            Alloc 0x14: [Int(42)]"#]])
    );
}

#[test]
fn nested_array_in_class_field() {
    // A class with an Array[Int] field — dropping the class
    // recursively drops the array (decrements refcount to 0).
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 0 , 99) ;
            Output: Trace:   let _1_w = new Wrapper (_1_a . give) ;
            Output: Trace:   _1_w = Wrapper { items: Array { flag: Given, rc: 1, 99 } }
            Output: Trace:   _1_w . drop ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x0e: [Int(0)]"#]])
    );
}

// ---------------------------------------------------------------
// Element type variations
// ---------------------------------------------------------------

#[test]
fn array_of_shared_class_elements() {
    // shared class elements have no flags word per element.
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Pt](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Pt { x: ⚡, y: ⚡ }, Pt { x: ⚡, y: ⚡ } }
            Output: Trace:   array_write [Pt, mut [_1_a]](_1_a . mut , 0 , new Pt (1, 2)) ;
            Output: Trace:   array_write [Pt, mut [_1_a]](_1_a . mut , 1 , new Pt (3, 4)) ;
            Output: Trace:   print(array_give [Pt, given, ref [_1_a]](_1_a . ref , 0)) ;
            Output: ----->   Pt { x: 1, y: 2 }
            Output: Trace:   array_give [Pt, given, given](_1_a . give , 1) ;
            Output: Trace: exit Main.main => Pt { x: 3, y: 4 }
            Result: Ok: Pt { x: 3, y: 4 }
            Alloc 0x18: [Int(3), Int(4)]"#]])
    );
}

#[test]
fn array_of_class_recursive_drop() {
    // Array of class with a nested field — dropping the array
    // should recursively drop each class element's fields.
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Outer](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Outer { inner: Inner { value: ⚡ } }, Outer { inner: Inner { value: ⚡ } } }
            Output: Trace:   array_write [Outer, mut [_1_a]](_1_a . mut , 0 , new Outer (new Inner (1))) ;
            Output: Trace:   array_write [Outer, mut [_1_a]](_1_a . mut , 1 , new Outer (new Inner (2))) ;
            Output: Trace:   _1_a . drop ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x13: [Int(0)]"#]])
    );
}

// ---------------------------------------------------------------
// ArrayDrop paths
// ---------------------------------------------------------------

#[test]
// NOTE: future-panic test. Type checker correctly accepts; fault is a runtime bounds/init check.
fn array_drop_out_of_bounds() {
    // Use Data (move type) so array_drop actually executes.
    // Int would be a no-op (copy type).
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Data](2);
                    array_drop[Data, given, mut[a]](a.mut, 5, 6);
                    0;
                }
            }
        },
        type: ok, interpret: fault(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ }, Data { x: ⚡ } }
            Output: Trace:   array_drop [Data, given, mut [_1_a]](_1_a . mut , 5 , 6) ;
            Result: Fault: array_drop: index 5 out of bounds (capacity 2)
            Alloc 0x03: [RefCount(1), Capacity(2), Uninitialized, Uninitialized]
            Alloc 0x04: [Flags(Given), Pointer(0x03)]
            Alloc 0x06: [MutRef(0x03)]"#]])
    );
}

#[test]
// NOTE: future-panic test. Type checker correctly accepts; fault is a runtime bounds/init check.
fn array_drop_uninitialized_faults() {
    // Use Data (move type) so array_drop actually executes.
    // Int would be a no-op (copy type).
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Data](2);
                    array_drop[Data, given, mut[a]](a.mut, 0, 1);
                    0;
                }
            }
        },
        type: ok, interpret: fault(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ }, Data { x: ⚡ } }
            Output: Trace:   array_drop [Data, given, mut [_1_a]](_1_a . mut , 0 , 1) ;
            Result: Fault: access of uninitialized value
            Alloc 0x03: [RefCount(1), Capacity(2), Uninitialized, Uninitialized]
            Alloc 0x04: [Flags(Given), Pointer(0x03)]
            Alloc 0x06: [MutRef(0x03)]"#]])
    );
}

// ---------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------

#[test]
fn array_new_zero_length() {
    // Zero-length array: capacity is 0, any access is out of bounds.
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](0);
                    array_capacity[Int, given](a.give);
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](0) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1 }
            Output: Trace:   array_capacity [Int, given](_1_a . give) ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x07: [Int(0)]"#]])
    );
}

#[test]
// NOTE: future-panic test. Type checker correctly accepts; fault is a runtime bounds/init check.
fn array_zero_length_access_faults() {
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](0);
                    array_give[Int, given, given](a.give, 0);
                }
            }
        },
        type: ok, interpret: fault(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](0) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1 }
            Output: Trace:   array_give [Int, given, given](_1_a . give , 0) ;
            Result: Fault: array_give: index 0 out of bounds (capacity 0)
            Alloc 0x03: [RefCount(1), Capacity(0)]
            Alloc 0x06: [Flags(Given), Pointer(0x03)]"#]])
    );
}

// ---------------------------------------------------------------
// Given array operations
// ---------------------------------------------------------------

#[test]
fn given_array_give_moves() {
    // A Given array (not shared) — giving it moves the whole array.
    // The original becomes uninitialized.
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 1 , 20) ;
            Output: Trace:   let _1_b = _1_a . give ;
            Output: Trace:   _1_b = Array { flag: Given, rc: 1, 10, 20 }
            Output: Trace:   array_give [Int, given, given](_1_b . give , 0) ;
            Output: Trace: exit Main.main => 10
            Result: Ok: 10
            Alloc 0x12: [Int(10)]"#]])
    );
}

#[test]
fn given_array_double_give_faults() {
    // A Given array can only be given once — second give faults.
    crate::assert_interpret!(
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
        type: error(expect_test::expect![[r#"
            src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Array[Int], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, a: Array[Int]}, assumptions: {}, fresh: 0 } }

            the rule "give" at (expressions.rs) failed because
              condition evaluated to false: `!live_after.is_live(place)`
                live_after = LivePlaces { accessed: {a}, traversed: {} }
                place = a"#]]), interpret: fault(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   let _1_b = _1_a . give ;
            Output: Trace:   _1_b = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   let _1_c = _1_a . give ;
            Result: Fault: access of uninitialized value
            Alloc 0x03: [RefCount(1), Capacity(1), Uninitialized]
            Alloc 0x06: [Flags(Given), Pointer(0x03)]"#]])
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
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 0 , 1) ;
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 1 , 2) ;
            Output: Trace:   let _1_c = new Container (_1_a . give) ;
            Output: Trace:   _1_c = Container { items: Array { flag: Given, rc: 1, 1, 2 } }
            Output: Trace:   let _1_s = _1_c . give . share ;
            Output: Trace:   _1_s = shared Container { items: Array { flag: Shared, rc: 1, 1, 2 } }
            Output: Trace:   print(_1_s . give) ;
            Output: ----->   shared Container { items: Array { flag: Shared, rc: 2, 1, 2 } }
            Output: Trace:   print(array_give [Int, given, ref [_1_s . items]](_1_s . items . ref , 0)) ;
            Output: ----->   1
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x19: [Int(0)]"#]])
    );
}

// ---------------------------------------------------------------
// Display
// ---------------------------------------------------------------

#[test]
fn array_display() {
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](3) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 1 , 20) ;
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 2 , 30) ;
            Output: Trace:   print(_1_a . ref) ;
            Output: ----->   ref [_1_a] Array { flag: Borrowed, rc: 1, 10, 20, 30 }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x14: [Int(0)]"#]])
    );
}

// ---------------------------------------------------------------
// Multiple references to the same shared array
// ---------------------------------------------------------------

#[test]
fn shared_array_two_refs_both_usable() {
    // Two variables referencing the same shared array.
    // Both can read elements independently.
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 1 , 20) ;
            Output: Trace:   let _1_s = _1_a . give . share ;
            Output: Trace:   _1_s = shared Array { flag: Shared, rc: 1, 10, 20 }
            Output: Trace:   let _1_b = _1_s . give ;
            Output: Trace:   _1_b = shared Array { flag: Shared, rc: 2, 10, 20 }
            Output: Trace:   let _1_x = array_give [Int, given, ref [_1_s]](_1_s . ref , 0) ;
            Output: Trace:   _1_x = 10
            Output: Trace:   let _1_y = array_give [Int, given, shared](_1_b . give , 1) ;
            Output: Trace:   _1_y = 20
            Output: Trace:   _1_x . give + _1_y . give ;
            Output: Trace: exit Main.main => 30
            Result: Ok: 30
            Alloc 0x1c: [Int(30)]"#]])
    );
}

#[test]
fn shared_array_three_refs_drop_two() {
    // Three references: drop two, last one still works.
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 0 , 42) ;
            Output: Trace:   let _1_s = _1_a . give . share ;
            Output: Trace:   _1_s = shared Array { flag: Shared, rc: 1, 42 }
            Output: Trace:   let _1_b = _1_s . give ;
            Output: Trace:   _1_b = shared Array { flag: Shared, rc: 2, 42 }
            Output: Trace:   let _1_c = _1_s . give ;
            Output: Trace:   _1_c = shared Array { flag: Shared, rc: 3, 42 }
            Output: Trace:   _1_s . drop ;
            Output: Trace:   _1_b . drop ;
            Output: Trace:   array_give [Int, given, shared](_1_c . give , 0) ;
            Output: Trace: exit Main.main => 42
            Result: Ok: 42
            Alloc 0x14: [Int(42)]"#]])
    );
}

#[test]
fn shared_array_all_refs_dropped_frees() {
    // All references dropped: backing allocation freed.
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 0 , 99) ;
            Output: Trace:   let _1_s = _1_a . give . share ;
            Output: Trace:   _1_s = shared Array { flag: Shared, rc: 1, 99 }
            Output: Trace:   let _1_b = _1_s . give ;
            Output: Trace:   _1_b = shared Array { flag: Shared, rc: 2, 99 }
            Output: Trace:   let _1_c = _1_b . give ;
            Output: Trace:   _1_c = shared Array { flag: Shared, rc: 3, 99 }
            Output: Trace:   _1_s . drop ;
            Output: Trace:   _1_b . drop ;
            Output: Trace:   _1_c . drop ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x13: [Int(0)]"#]])
    );
}

// ---------------------------------------------------------------
// Nested arrays: Array[Array[T]]
// ---------------------------------------------------------------

#[test]
fn nested_array_create_and_capacity() {
    // Array[Array[Int]]: outer array holds inner arrays as elements.
    // Each element is 2 words (Flags + Pointer).
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_outer = array_new [Array[Int]](2) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   let _1_inner0 = array_new [Int](3) ;
            Output: Trace:   _1_inner0 = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ }
            Output: Trace:   array_write [Array[Int], mut [_1_outer]](_1_outer . mut , 0 , _1_inner0 . give) ;
            Output: Trace:   let _1_got = array_give [Array[Int], given, given](_1_outer . give , 0) ;
            Output: Trace:   _1_got = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ }
            Output: Trace:   array_capacity [Int, given](_1_got . give) ;
            Output: Trace: exit Main.main => 3
            Result: Ok: 3
            Alloc 0x13: [Int(3)]"#]])
    );
}

#[test]
fn nested_array_give_inner_from_shared_outer() {
    // shared Array[Array[Int]]: giving an element from a shared outer array.
    // The inner array element has Given flags in the backing allocation.
    // When outer is shared, give_value sees Shared flags (from the outer's
    // shared perspective) and calls share_op, incrementing the inner array's
    // refcount. We can give the same inner element multiple times.
    crate::assert_interpret!(
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
                    let got = array_give[Array[Int], shared, ref[s]](s.ref, 0);
                    print(got.give);
                    // Give it again — shared elements can be given repeatedly.
                    let got2 = array_give[Array[Int], shared, shared](s.give, 0);
                    array_give[Int, given, given](got2.give, 1);
                }
            }
        },
        type: error(expect_test::expect![[r#"src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, got: shared Array[Int], got2: shared Array[Int], inner: Array[Int], outer: Array[Array[Int]], s: shared Array[Array[Int]]}, assumptions: {}, fresh: 0 } }"#]]), interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Int](2) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_inner]](_1_inner . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [_1_inner]](_1_inner . mut , 1 , 20) ;
            Output: Trace:   let _1_outer = array_new [Array[Int]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Int], mut [_1_outer]](_1_outer . mut , 0 , _1_inner . give) ;
            Output: Trace:   let _1_s = _1_outer . give . share ;
            Output: Trace:   _1_s = shared Array { flag: Shared, rc: 1, Array { flag: Given, rc: 1, 10, 20 } }
            Output: Trace:   let _1_got = array_give [Array[Int], shared, ref [_1_s]](_1_s . ref , 0) ;
            Output: Trace:   _1_got = shared Array { flag: Shared, rc: 2, 10, 20 }
            Output: Trace:   print(_1_got . give) ;
            Output: ----->   shared Array { flag: Shared, rc: 3, 10, 20 }
            Output: Trace:   let _1_got2 = array_give [Array[Int], shared, shared](_1_s . give , 0) ;
            Output: Trace:   _1_got2 = shared Array { flag: Shared, rc: 3, 10, 20 }
            Output: Trace:   array_give [Int, given, given](_1_got2 . give , 1) ;
            Output: Trace: exit Main.main => 20
            Result: Ok: 20
            Alloc 0x03: [RefCount(1), Capacity(2), Int(10), Int(20)]
            Alloc 0x24: [Int(20)]"#]])
    );
}

#[test]
fn nested_array_drop_inner_decrements_refcount() {
    // Array[Array[Int]]: dropping the inner element in the outer array
    // should decrement the inner array's refcount.
    crate::assert_interpret!(
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
                    array_drop[Array[Int], given, mut[outer]](outer.mut, 0, 1);
                    // s var still alive, can still read.
                    array_give[Int, given, shared](s.give, 0);
                }
            }
        },
        type: error(expect_test::expect![[r#"src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, inner: Array[Int], outer: Array[Array[Int]], s: shared Array[Int]}, assumptions: {}, fresh: 0 } }"#]]), interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Int](1) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_inner]](_1_inner . mut , 0 , 42) ;
            Output: Trace:   let _1_s = _1_inner . give . share ;
            Output: Trace:   _1_s = shared Array { flag: Shared, rc: 1, 42 }
            Output: Trace:   let _1_outer = array_new [Array[Int]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Int], mut [_1_outer]](_1_outer . mut , 0 , _1_s . give) ;
            Output: Trace:   array_drop [Array[Int], given, mut [_1_outer]](_1_outer . mut , 0 , 1) ;
            Output: Trace:   array_give [Int, given, shared](_1_s . give , 0) ;
            Output: Trace: exit Main.main => 42
            Result: Ok: 42
            Alloc 0x1a: [Int(42)]"#]])
    );
}

#[test]
fn nested_array_all_refs_freed() {
    // Nested array: dropping the outer array scrubs its backing but does NOT
    // drop elements (arrays don't drop their elements — that's the user's job).
    // The inner array's backing allocation remains as an orphan in the heap.
    // This documents the unsafe contract: use array_drop to clean up elements.
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    let inner = array_new[Int](1);
                    array_write[Int, mut[inner]](inner.mut, 0, 1);
                    let outer = array_new[Array[Int]](1);
                    array_write[Array[Int], mut[outer]](outer.mut, 0, inner.give);
                    // Drop outer — outer backing scrubbed, but inner backing leaks.
                    outer.drop;
                    0;
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Int](1) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_inner]](_1_inner . mut , 0 , 1) ;
            Output: Trace:   let _1_outer = array_new [Array[Int]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Int], mut [_1_outer]](_1_outer . mut , 0 , _1_inner . give) ;
            Output: Trace:   _1_outer . drop ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x03: [RefCount(1), Capacity(1), Int(1)]
            Alloc 0x13: [Int(0)]"#]])
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
    crate::assert_interpret!(
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
                    let got = array_give[Array[Data], shared, ref[so]](so.ref, 0);
                    // Read Data through the copy — shared, so no move.
                    print(array_give[Data, shared, shared](got.give, 0));
                    // Read Data through original inner — still available.
                    print(array_give[Data, shared, shared](si.give, 0));
                    0;
                }
            }
        },
        type: error(expect_test::expect![[r#"src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, inner: Array[Data], outer: Array[Array[Data]], si: shared Array[Data]}, assumptions: {}, fresh: 0 } }"#]]), interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Data](1) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [_1_inner]](_1_inner . mut , 0 , new Data (42)) ;
            Output: Trace:   let _1_si = _1_inner . give . share ;
            Output: Trace:   _1_si = shared Array { flag: Shared, rc: 1, Data { x: 42 } }
            Output: Trace:   let _1_outer = array_new [Array[Data]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Data], mut [_1_outer]](_1_outer . mut , 0 , _1_si . give) ;
            Output: Trace:   let _1_so = _1_outer . give . share ;
            Output: Trace:   _1_so = shared Array { flag: Shared, rc: 1, Array { flag: Shared, rc: 2, Data { x: 42 } } }
            Output: Trace:   let _1_got = array_give [Array[Data], shared, ref [_1_so]](_1_so . ref , 0) ;
            Output: Trace:   _1_got = shared Array { flag: Shared, rc: 3, Data { x: 42 } }
            Output: Trace:   print(array_give [Data, shared, shared](_1_got . give , 0)) ;
            Output: ----->   shared Data { x: 42 }
            Output: Trace:   print(array_give [Data, shared, shared](_1_si . give , 0)) ;
            Output: ----->   shared Data { x: 42 }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x03: [RefCount(1), Capacity(1), Int(42)]
            Alloc 0x23: [Int(0)]"#]])
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
    crate::assert_interpret!(
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
                    let got = array_give[Array[Data], shared, ref[so]](so.ref, 0);
                    // Read Data through the copy — shared, no move.
                    print(array_give[Data, shared, shared](got.give, 0));
                    // Read Data through original inner — still available.
                    print(array_give[Data, shared, shared](si.give, 0));
                    0;
                }
            }
        },
        type: error(expect_test::expect![[r#"src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, inner: Array[Data], outer: Array[Array[Data]], si: shared Array[Data]}, assumptions: {}, fresh: 0 } }"#]]), interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Data](1) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [_1_inner]](_1_inner . mut , 0 , new Data (99)) ;
            Output: Trace:   let _1_si = _1_inner . give . share ;
            Output: Trace:   _1_si = shared Array { flag: Shared, rc: 1, Data { x: 99 } }
            Output: Trace:   let _1_outer = array_new [Array[Data]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Data], mut [_1_outer]](_1_outer . mut , 0 , _1_si . give) ;
            Output: Trace:   let _1_so = _1_outer . give . share ;
            Output: Trace:   _1_so = shared Array { flag: Shared, rc: 1, Array { flag: Shared, rc: 2, Data { x: 99 } } }
            Output: Trace:   let _1_got = array_give [Array[Data], shared, ref [_1_so]](_1_so . ref , 0) ;
            Output: Trace:   _1_got = shared Array { flag: Shared, rc: 3, Data { x: 99 } }
            Output: Trace:   print(array_give [Data, shared, shared](_1_got . give , 0)) ;
            Output: ----->   shared Data { x: 99 }
            Output: Trace:   print(array_give [Data, shared, shared](_1_si . give , 0)) ;
            Output: ----->   shared Data { x: 99 }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x03: [RefCount(1), Capacity(1), Int(99)]
            Alloc 0x23: [Int(0)]"#]])
    );
}

#[test]
fn shared_outer_give_inner_survives_outer_drop() {
    // Key scenario: shared Array[Array[Data]] — giving an inner array
    // element produces a shared copy with incremented refcount.
    // After dropping the outer array entirely, the given copy still works
    // because share_op kept the inner backing alive.
    crate::assert_interpret!(
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
                    let got = array_give[Array[Data], shared, ref[so]](so.ref, 0);
                    // Drop outer entirely — cascading drop hits the element,
                    // which decrements inner refcount. But got's share_op
                    // already incremented it, so refcount > 0.
                    si.drop;
                    so.drop;
                    // got still alive — read the Data element.
                    array_give[Data, shared, shared](got.give, 0);
                }
            }
        },
        type: error(expect_test::expect![[r#"src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, inner: Array[Data], outer: Array[Array[Data]], si: shared Array[Data]}, assumptions: {}, fresh: 0 } }"#]]), interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Data](1) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [_1_inner]](_1_inner . mut , 0 , new Data (42)) ;
            Output: Trace:   let _1_si = _1_inner . give . share ;
            Output: Trace:   _1_si = shared Array { flag: Shared, rc: 1, Data { x: 42 } }
            Output: Trace:   let _1_outer = array_new [Array[Data]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Data], mut [_1_outer]](_1_outer . mut , 0 , _1_si . give) ;
            Output: Trace:   let _1_so = _1_outer . give . share ;
            Output: Trace:   _1_so = shared Array { flag: Shared, rc: 1, Array { flag: Shared, rc: 2, Data { x: 42 } } }
            Output: Trace:   let _1_got = array_give [Array[Data], shared, ref [_1_so]](_1_so . ref , 0) ;
            Output: Trace:   _1_got = shared Array { flag: Shared, rc: 3, Data { x: 42 } }
            Output: Trace:   _1_si . drop ;
            Output: Trace:   _1_so . drop ;
            Output: Trace:   array_give [Data, shared, shared](_1_got . give , 0) ;
            Output: Trace: exit Main.main => shared Data { x: 42 }
            Result: Ok: shared Data { x: 42 }
            Alloc 0x03: [RefCount(1), Capacity(1), Int(42)]
            Alloc 0x1f: [Int(42)]"#]])
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
    crate::assert_interpret!(
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
                    let copy1 = array_give[Array[Data], shared, ref[so]](so.ref, 0);
                    let copy2 = array_give[Array[Data], shared, ref[so]](so.ref, 0);
                    // All three can read the same Data — shared, no move.
                    print(array_give[Data, shared, shared](copy1.give, 0));
                    print(array_give[Data, shared, shared](copy2.give, 0));
                    print(array_give[Data, shared, shared](si.give, 0));
                    0;
                }
            }
        },
        type: error(expect_test::expect![[r#"src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, inner: Array[Data], outer: Array[Array[Data]], si: shared Array[Data]}, assumptions: {}, fresh: 0 } }"#]]), interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Data](1) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [_1_inner]](_1_inner . mut , 0 , new Data (77)) ;
            Output: Trace:   let _1_si = _1_inner . give . share ;
            Output: Trace:   _1_si = shared Array { flag: Shared, rc: 1, Data { x: 77 } }
            Output: Trace:   let _1_outer = array_new [Array[Data]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Data], mut [_1_outer]](_1_outer . mut , 0 , _1_si . give) ;
            Output: Trace:   let _1_so = _1_outer . give . share ;
            Output: Trace:   _1_so = shared Array { flag: Shared, rc: 1, Array { flag: Shared, rc: 2, Data { x: 77 } } }
            Output: Trace:   let _1_copy1 = array_give [Array[Data], shared, ref [_1_so]](_1_so . ref , 0) ;
            Output: Trace:   _1_copy1 = shared Array { flag: Shared, rc: 3, Data { x: 77 } }
            Output: Trace:   let _1_copy2 = array_give [Array[Data], shared, ref [_1_so]](_1_so . ref , 0) ;
            Output: Trace:   _1_copy2 = shared Array { flag: Shared, rc: 4, Data { x: 77 } }
            Output: Trace:   print(array_give [Data, shared, shared](_1_copy1 . give , 0)) ;
            Output: ----->   shared Data { x: 77 }
            Output: Trace:   print(array_give [Data, shared, shared](_1_copy2 . give , 0)) ;
            Output: ----->   shared Data { x: 77 }
            Output: Trace:   print(array_give [Data, shared, shared](_1_si . give , 0)) ;
            Output: ----->   shared Data { x: 77 }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x03: [RefCount(1), Capacity(1), Int(77)]
            Alloc 0x2b: [Int(0)]"#]])
    );
}

#[test]
fn shared_array_of_shared_arrays_drop_cascade() {
    // shared Array[Array[Data]]: P=given but runtime element is shared.
    // array_give correctly produces a shared copy (rc++) rather than a move,
    // because the runtime Shared flags override the static P=given.
    // The inner array backing leaks (rc=1) because arrays don't drop
    // their elements — the outer's scrub doesn't decrement the inner's rc.
    crate::assert_interpret!(
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
                    // Give a copy from outer: runtime flags are Shared, so this
                    // produces a shared copy (rc++) not a move.
                    let copy1 = array_give[Array[Data], given, ref[so]](so.ref, 0);
                    copy1.drop;
                    so.drop;
                    si.drop;
                    0;
                }
            }
        },
        type: error(expect_test::expect![[r#"src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, inner: Array[Data], outer: Array[Array[Data]], si: shared Array[Data]}, assumptions: {}, fresh: 0 } }"#]]), interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Data](1) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [_1_inner]](_1_inner . mut , 0 , new Data (55)) ;
            Output: Trace:   let _1_si = _1_inner . give . share ;
            Output: Trace:   _1_si = shared Array { flag: Shared, rc: 1, Data { x: 55 } }
            Output: Trace:   let _1_outer = array_new [Array[Data]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Data], mut [_1_outer]](_1_outer . mut , 0 , _1_si . give) ;
            Output: Trace:   let _1_so = _1_outer . give . share ;
            Output: Trace:   _1_so = shared Array { flag: Shared, rc: 1, Array { flag: Shared, rc: 2, Data { x: 55 } } }
            Output: Trace:   let _1_copy1 = array_give [Array[Data], given, ref [_1_so]](_1_so . ref , 0) ;
            Output: Trace:   _1_copy1 = Array { flag: Shared, rc: 3, Data { x: 55 } }
            Output: Trace:   _1_copy1 . drop ;
            Output: Trace:   _1_so . drop ;
            Output: Trace:   _1_si . drop ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x03: [RefCount(1), Capacity(1), Int(55)]
            Alloc 0x1e: [Int(0)]"#]])
    );
}

// ---------------------------------------------------------------
// ArrayDrop: Shared and Borrowed elements
// ---------------------------------------------------------------

#[test]
fn array_drop_shared_element_decrements_refcount() {
    // Array element with Shared flags: ArrayDrop should call drop_owned_value,
    // which for an array element decrements its refcount.
    crate::assert_interpret!(
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
                    array_drop[Array[Int], given, mut[outer]](outer.mut, 0, 1);
                    array_give[Int, given, shared](si.give, 0);
                }
            }
        },
        type: error(expect_test::expect![[r#"src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, inner: Array[Int], outer: Array[Array[Int]], si: shared Array[Int]}, assumptions: {}, fresh: 0 } }"#]]), interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Int](1) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_inner]](_1_inner . mut , 0 , 42) ;
            Output: Trace:   let _1_si = _1_inner . give . share ;
            Output: Trace:   _1_si = shared Array { flag: Shared, rc: 1, 42 }
            Output: Trace:   let _1_outer = array_new [Array[Int]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Int], mut [_1_outer]](_1_outer . mut , 0 , _1_si . give) ;
            Output: Trace:   array_drop [Array[Int], given, mut [_1_outer]](_1_outer . mut , 0 , 1) ;
            Output: Trace:   array_give [Int, given, shared](_1_si . give , 0) ;
            Output: Trace: exit Main.main => 42
            Result: Ok: 42
            Alloc 0x1a: [Int(42)]"#]])
    );
}

#[test]
// BUG: soundness gap — type checker accepts but interpreter faults (use after array_drop).
fn array_drop_shared_class_element() {
    // Even though Pt is a `shared class` (copy type), array_drop with P=given
    // actually drops the element. P=given means "I own these, clean them up."
    // This is needed to avoid leaks: a shared class with boxed fields would
    // leak refcounts if array_drop were a no-op.
    crate::assert_interpret!(
        {
            shared class Pt { x: Int; y: Int; }
            class Main {
                fn main(given self) -> Pt {
                    let a = array_new[Pt](1);
                    array_write[Pt, mut[a]](a.mut, 0, new Pt(1, 2));
                    array_drop[Pt, given, mut[a]](a.mut, 0, 1);
                    // Element is now uninitialized — giving it should fault.
                    array_give[Pt, given, given](a.give, 0);
                }
            }
        },
        type: ok, interpret: fault(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Pt](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Pt { x: ⚡, y: ⚡ } }
            Output: Trace:   array_write [Pt, mut [_1_a]](_1_a . mut , 0 , new Pt (1, 2)) ;
            Output: Trace:   array_drop [Pt, given, mut [_1_a]](_1_a . mut , 0 , 1) ;
            Output: Trace:   array_give [Pt, given, given](_1_a . give , 0) ;
            Result: Fault: access of uninitialized value
            Alloc 0x03: [RefCount(1), Capacity(1), Uninitialized, Uninitialized]
            Alloc 0x10: [Flags(Given), Pointer(0x03)]"#]])
    );
}

// ---------------------------------------------------------------
// ArrayWrite with class containing array field
// ---------------------------------------------------------------

#[test]
fn array_write_class_with_array_field() {
    // Initialize an array element with a class that contains an Array field.
    // Ownership of the inner array transfers into the element slot.
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_outer = array_new [Container](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, Container { items: ⚡ } }
            Output: Trace:   let _1_inner = array_new [Int](2) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_inner]](_1_inner . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [_1_inner]](_1_inner . mut , 1 , 20) ;
            Output: Trace:   let _1_c = new Container (_1_inner . give) ;
            Output: Trace:   _1_c = Container { items: Array { flag: Given, rc: 1, 10, 20 } }
            Output: Trace:   array_write [Container, mut [_1_outer]](_1_outer . mut , 0 , _1_c . give) ;
            Output: Trace:   let _1_got = array_give [Container, given, given](_1_outer . give , 0) ;
            Output: Trace:   _1_got = Container { items: Array { flag: Given, rc: 1, 10, 20 } }
            Output: Trace:   print(_1_got . give) ;
            Output: ----->   Container { items: Array { flag: Given, rc: 1, 10, 20 } }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x1f: [Int(0)]"#]])
    );
}

#[test]
fn array_drop_class_with_array_field() {
    // Drop an array element that is a class containing an Array field.
    // Should recursively drop: class element → inner array (refcount→0, freed).
    crate::assert_interpret!(
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
                    array_drop[Container, given, mut[outer]](outer.mut, 0, 1);
                    0;
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_outer = array_new [Container](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, Container { items: ⚡ } }
            Output: Trace:   let _1_inner = array_new [Int](1) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_inner]](_1_inner . mut , 0 , 99) ;
            Output: Trace:   print(_1_inner . ref) ;
            Output: ----->   ref [_1_inner] Array { flag: Borrowed, rc: 1, 99 }
            Output: Trace:   let _1_c = new Container (_1_inner . give) ;
            Output: Trace:   _1_c = Container { items: Array { flag: Given, rc: 1, 99 } }
            Output: Trace:   print(_1_c . ref) ;
            Output: ----->   ref [_1_c] Container { items: Array { flag: Borrowed, rc: 1, 99 } }
            Output: Trace:   array_write [Container, mut [_1_outer]](_1_outer . mut , 0 , _1_c . give) ;
            Output: Trace:   print(_1_outer . ref) ;
            Output: ----->   ref [_1_outer] Array { flag: Borrowed, rc: 1, Container { items: Array { flag: Given, rc: 1, 99 } } }
            Output: Trace:   array_drop [Container, given, mut [_1_outer]](_1_outer . mut , 0 , 1) ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x1f: [Int(0)]"#]])
    );
}

#[test]
fn array_share_uninitialized() {
    // Sharing a newly created array with uninitialized elements succeeds —
    // array elements are user-managed (unsafe), so share doesn't traverse them.
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_outer = array_new [Container](1) . share ;
            Output: Trace:   _1_outer = shared Array { flag: Shared, rc: 1, Container { items: ⚡ } }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x06: [Int(0)]"#]])
    );
}

// ---------------------------------------------------------------
// Sharing paths: a.ref on shared array
// ---------------------------------------------------------------

#[test]
fn shared_array_give_increments_refcount() {
    // Giving a shared array increments the refcount.
    // After dropping the original, the copy keeps the array alive.
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 0 , 55) ;
            Output: Trace:   let _1_s = _1_a . give . share ;
            Output: Trace:   _1_s = shared Array { flag: Shared, rc: 1, 55 }
            Output: Trace:   let _1_b = _1_s . give ;
            Output: Trace:   _1_b = shared Array { flag: Shared, rc: 2, 55 }
            Output: Trace:   _1_s . drop ;
            Output: Trace:   array_give [Int, given, shared](_1_b . give , 0) ;
            Output: Trace: exit Main.main => 55
            Result: Ok: 55
            Alloc 0x11: [Int(55)]"#]])
    );
}

// ---------------------------------------------------------------
// Ref arrays
// ---------------------------------------------------------------

#[test]
fn ref_array_print() {
    // Taking a ref to an array and printing it.
    crate::assert_interpret!(
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
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 1 , 20) ;
            Output: Trace:   print(_1_a . ref) ;
            Output: ----->   ref [_1_a] Array { flag: Borrowed, rc: 1, 10, 20 }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x10: [Int(0)]"#]])
    );
}

#[test]
fn ref_array_give_int_element() {
    // Giving an Int element from a ref array with P=ref yields a copy.
    // Int is a shared class (copy type), so ref produces a copy.
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_write[Int, mut[a]](a.mut, 0, 42);
                    array_write[Int, mut[a]](a.mut, 1, 99);
                    let x = array_give[Int, ref[a], ref[a]](a.ref, 0);
                    let y = array_give[Int, ref[a], ref[a]](a.ref, 1);
                    print(x.give);
                    print(y.give);
                    // Original array still intact — ref didn't move elements.
                    print(a.ref);
                    0;
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 0 , 42) ;
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 1 , 99) ;
            Output: Trace:   let _1_x = array_give [Int, ref [_1_a], ref [_1_a]](_1_a . ref , 0) ;
            Output: Trace:   _1_x = 42
            Output: Trace:   let _1_y = array_give [Int, ref [_1_a], ref [_1_a]](_1_a . ref , 1) ;
            Output: Trace:   _1_y = 99
            Output: Trace:   print(_1_x . give) ;
            Output: ----->   42
            Output: Trace:   print(_1_y . give) ;
            Output: ----->   99
            Output: Trace:   print(_1_a . ref) ;
            Output: ----->   ref [_1_a] Array { flag: Borrowed, rc: 1, 42, 99 }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x1c: [Int(0)]"#]])
    );
}

#[test]
fn ref_array_give_class_element() {
    // Giving a class element with P=ref yields a borrowed copy (ref flags on boxed fields).
    crate::assert_interpret!(
        {
            class Data {
                x: Int;
            }
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Data](1);
                    array_write[Data, mut[a]](a.mut, 0, new Data(42));
                    let d = array_give[Data, ref[a], ref[a]](a.ref, 0);
                    print(d.give);
                    // Original still intact.
                    print(a.ref);
                    0;
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [_1_a]](_1_a . mut , 0 , new Data (42)) ;
            Output: Trace:   let _1_d = array_give [Data, ref [_1_a], ref [_1_a]](_1_a . ref , 0) ;
            Output: Trace:   _1_d = ref [_1_a] Data { x: 42 }
            Output: Trace:   print(_1_d . give) ;
            Output: ----->   ref [_1_a] Data { x: 42 }
            Output: Trace:   print(_1_a . ref) ;
            Output: ----->   ref [_1_a] Array { flag: Borrowed, rc: 1, Data { x: 42 } }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x13: [Int(0)]"#]])
    );
}

#[test]
fn ref_array_of_shared_arrays() {
    // ref to Array[shared Array[Int]]: the outer array holds shared inner arrays.
    // Giving an element with P=ref through a ref to the outer produces a
    // borrowed copy of the shared inner array (flag: Borrowed, rc incremented
    // to keep backing alive).
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    let inner = array_new[Int](2);
                    array_write[Int, mut[inner]](inner.mut, 0, 10);
                    array_write[Int, mut[inner]](inner.mut, 1, 20);
                    let si = inner.give.share;
                    let outer = array_new[shared Array[Int]](1);
                    array_write[shared Array[Int], mut[outer]](outer.mut, 0, si.give);
                    // outer holds shared Array[Int] elements.
                    // Take a ref to outer, give the element with P=ref.
                    let got = array_give[shared Array[Int], ref[outer], ref[outer]](outer.ref, 0);
                    print(got.give);
                    // Original outer still intact.
                    print(outer.ref);
                    0;
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Int](2) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_inner]](_1_inner . mut , 0 , 10) ;
            Output: Trace:   array_write [Int, mut [_1_inner]](_1_inner . mut , 1 , 20) ;
            Output: Trace:   let _1_si = _1_inner . give . share ;
            Output: Trace:   _1_si = shared Array { flag: Shared, rc: 1, 10, 20 }
            Output: Trace:   let _1_outer = array_new [shared Array[Int]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, shared ⚡ }
            Output: Trace:   array_write [shared Array[Int], mut [_1_outer]](_1_outer . mut , 0 , _1_si . give) ;
            Output: Trace:   let _1_got = array_give [shared Array[Int], ref [_1_outer], ref [_1_outer]](_1_outer . ref , 0) ;
            Output: Trace:   _1_got = shared Array { flag: Shared, rc: 3, 10, 20 }
            Output: Trace:   print(_1_got . give) ;
            Output: ----->   shared Array { flag: Shared, rc: 4, 10, 20 }
            Output: Trace:   print(_1_outer . ref) ;
            Output: ----->   ref [_1_outer] Array { flag: Borrowed, rc: 1, shared Array { flag: Shared, rc: 3, 10, 20 } }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x03: [RefCount(1), Capacity(2), Int(10), Int(20)]
            Alloc 0x20: [Int(0)]"#]])
    );
}

// ---------------------------------------------------------------
// Phase 3.5: Static ref, runtime shared — mismatch scenario
// ---------------------------------------------------------------

#[test]
fn array_give_ref_of_runtime_shared_element() {
    // The element type is ref[dummy] Array[Int] — the array holds borrowed arrays.
    // But at runtime, the stored element has Shared flags (came from .share;
    // shared ≤ ref so this is valid). array_give with P=ref dispatches on the
    // static type `ref[outer] ref[dummy] Array[Int]` — what happens?
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    let inner = array_new[Int](1);
                    array_write[Int, mut[inner]](inner.mut, 0, 42);
                    let shared_inner = inner.give.share;
                    // dummy variable so we can write ref[dummy] as the element type.
                    let dummy = array_new[Int](0);
                    // Element type is ref[dummy] Array[Int], but we store a shared array.
                    let outer = array_new[ref[dummy] Array[Int]](1);
                    array_write[ref[dummy] Array[Int], mut[outer]](outer.mut, 0, shared_inner.give);
                    // Give with P=ref: static type says ref, runtime flags say Shared.
                    let got = array_give[ref[dummy] Array[Int], ref[outer], ref[outer]](outer.ref, 0);
                    print(got.give);
                    // Is the refcount correct? Is the element still intact?
                    print(outer.ref);
                    0;
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Int](1) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_inner]](_1_inner . mut , 0 , 42) ;
            Output: Trace:   let _1_shared_inner = _1_inner . give . share ;
            Output: Trace:   _1_shared_inner = shared Array { flag: Shared, rc: 1, 42 }
            Output: Trace:   let _1_dummy = array_new [Int](0) ;
            Output: Trace:   _1_dummy = Array { flag: Given, rc: 1 }
            Output: Trace:   let _1_outer = array_new [ref [_1_dummy] Array[Int]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ref [_1_dummy] ⚡ }
            Output: Trace:   array_write [ref [_1_dummy] Array[Int], mut [_1_outer]](_1_outer . mut , 0 , _1_shared_inner . give) ;
            Output: Trace:   let _1_got = array_give [ref [_1_dummy] Array[Int], ref [_1_outer], ref [_1_outer]](_1_outer . ref , 0) ;
            Output: Trace:   _1_got = ref [_1_dummy] Array { flag: Shared, rc: 3, 42 }
            Output: Trace:   print(_1_got . give) ;
            Output: ----->   ref [_1_dummy] Array { flag: Shared, rc: 4, 42 }
            Output: Trace:   print(_1_outer . ref) ;
            Output: ----->   ref [_1_outer] Array { flag: Borrowed, rc: 1, ref [_1_dummy] Array { flag: Shared, rc: 3, 42 } }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x03: [RefCount(1), Capacity(1), Int(42)]
            Alloc 0x20: [Int(0)]"#]])
    );
}

// ---------------------------------------------------------------
// Phase 3: Poly-permission semantics tests
// ---------------------------------------------------------------

#[test]
fn array_give_p_mut() {
    // array_give with P=mut returns a mutable reference to the element.
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Data](1);
                    array_write[Data, mut[a]](a.mut, 0, new Data(42));
                    let d = array_give[Data, mut[a], ref[a]](a.ref, 0);
                    print(d.ref);
                    0;
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [_1_a]](_1_a . mut , 0 , new Data (42)) ;
            Output: Trace:   let _1_d = array_give [Data, mut [_1_a], ref [_1_a]](_1_a . ref , 0) ;
            Output: Trace:   _1_d = mut [_1_a] Data { x: 42 }
            Output: Trace:   print(_1_d . ref) ;
            Output: ----->   ref [_1_d] mut [_1_a] Data { x: 42 }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x11: [Int(0)]"#]])
    );
}

#[test]
fn array_give_p_shared() {
    // array_give with P=shared returns a shared copy, rc incremented.
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    let inner = array_new[Int](1);
                    array_write[Int, mut[inner]](inner.mut, 0, 77);
                    let s = inner.give.share;
                    let outer = array_new[Array[Int]](1);
                    array_write[Array[Int], mut[outer]](outer.mut, 0, s.give);
                    // Give with P=shared: should produce a shared copy with rc++
                    let got = array_give[Array[Int], shared, ref[outer]](outer.ref, 0);
                    print(got.give);
                    // Original still intact
                    print(outer.ref);
                    0;
                }
            }
        },
        type: error(expect_test::expect![[r#"src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, inner: Array[Int], outer: Array[Array[Int]], s: shared Array[Int]}, assumptions: {}, fresh: 0 } }"#]]), interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Int](1) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_inner]](_1_inner . mut , 0 , 77) ;
            Output: Trace:   let _1_s = _1_inner . give . share ;
            Output: Trace:   _1_s = shared Array { flag: Shared, rc: 1, 77 }
            Output: Trace:   let _1_outer = array_new [Array[Int]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Int], mut [_1_outer]](_1_outer . mut , 0 , _1_s . give) ;
            Output: Trace:   let _1_got = array_give [Array[Int], shared, ref [_1_outer]](_1_outer . ref , 0) ;
            Output: Trace:   _1_got = shared Array { flag: Shared, rc: 3, 77 }
            Output: Trace:   print(_1_got . give) ;
            Output: ----->   shared Array { flag: Shared, rc: 4, 77 }
            Output: Trace:   print(_1_outer . ref) ;
            Output: ----->   ref [_1_outer] Array { flag: Borrowed, rc: 1, Array { flag: Shared, rc: 3, 77 } }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x03: [RefCount(1), Capacity(1), Int(77)]
            Alloc 0x1c: [Int(0)]"#]])
    );
}

#[test]
fn array_give_p_ref() {
    // array_give with P=ref returns a borrowed copy.
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    let inner = array_new[Int](1);
                    array_write[Int, mut[inner]](inner.mut, 0, 55);
                    let outer = array_new[Array[Int]](1);
                    array_write[Array[Int], mut[outer]](outer.mut, 0, inner.give);
                    // Give with P=ref: should produce a borrowed copy
                    let got = array_give[Array[Int], ref[outer], ref[outer]](outer.ref, 0);
                    print(got.give);
                    // Original still intact
                    print(outer.ref);
                    0;
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_inner = array_new [Int](1) ;
            Output: Trace:   _1_inner = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_inner]](_1_inner . mut , 0 , 55) ;
            Output: Trace:   let _1_outer = array_new [Array[Int]](1) ;
            Output: Trace:   _1_outer = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Array[Int], mut [_1_outer]](_1_outer . mut , 0 , _1_inner . give) ;
            Output: Trace:   let _1_got = array_give [Array[Int], ref [_1_outer], ref [_1_outer]](_1_outer . ref , 0) ;
            Output: Trace:   _1_got = ref [_1_outer] Array { flag: Borrowed, rc: 1, 55 }
            Output: Trace:   print(_1_got . give) ;
            Output: ----->   ref [_1_outer] Array { flag: Borrowed, rc: 1, 55 }
            Output: Trace:   print(_1_outer . ref) ;
            Output: ----->   ref [_1_outer] Array { flag: Borrowed, rc: 1, Array { flag: Given, rc: 1, 55 } }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x03: [RefCount(1), Capacity(1), Int(55)]
            Alloc 0x1a: [Int(0)]"#]])
    );
}

#[test]
fn array_drop_p_shared_is_noop() {
    // array_drop with P=shared should be a no-op — element still accessible.
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let a = array_new[Data](1);
                    array_write[Data, mut[a]](a.mut, 0, new Data(42));
                    array_drop[Data, shared, ref[a]](a.ref, 0, 1);
                    // Element still accessible — shared drop is a no-op.
                    array_give[Data, given, given](a.give, 0);
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [_1_a]](_1_a . mut , 0 , new Data (42)) ;
            Output: Trace:   array_drop [Data, shared, ref [_1_a]](_1_a . ref , 0 , 1) ;
            Output: Trace:   array_give [Data, given, given](_1_a . give , 0) ;
            Output: Trace: exit Main.main => Data { x: 42 }
            Result: Ok: Data { x: 42 }
            Alloc 0x11: [Int(42)]"#]])
    );
}

#[test]
// BUG: soundness gap — type checker accepts but interpreter faults (use after array_drop).
fn array_drop_p_given_range() {
    // array_drop with P=given on a range of elements drops all of them.
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let a = array_new[Data](3);
                    array_write[Data, mut[a]](a.mut, 0, new Data(10));
                    array_write[Data, mut[a]](a.mut, 1, new Data(20));
                    array_write[Data, mut[a]](a.mut, 2, new Data(30));
                    // Drop elements 0, 1, 2
                    array_drop[Data, given, ref[a]](a.ref, 0, 3);
                    // All elements are now uninitialized — giving any should fault.
                    array_give[Data, given, given](a.give, 1);
                }
            }
        },
        type: ok, interpret: fault(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](3) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ }, Data { x: ⚡ }, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [_1_a]](_1_a . mut , 0 , new Data (10)) ;
            Output: Trace:   array_write [Data, mut [_1_a]](_1_a . mut , 1 , new Data (20)) ;
            Output: Trace:   array_write [Data, mut [_1_a]](_1_a . mut , 2 , new Data (30)) ;
            Output: Trace:   array_drop [Data, given, ref [_1_a]](_1_a . ref , 0 , 3) ;
            Output: Trace:   array_give [Data, given, given](_1_a . give , 1) ;
            Result: Fault: access of uninitialized value
            Alloc 0x03: [RefCount(1), Capacity(3), Uninitialized, Uninitialized, Uninitialized]
            Alloc 0x19: [Flags(Given), Pointer(0x03)]"#]])
    );
}

#[test]
fn array_give_p_given_int_is_copy() {
    // Giving an Int element with P=given copies without uninitializing.
    // Even though P = given, the combined type `given Int` is shared/copy
    // (Int is a shared class), so array_give copies rather than moving.
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](1);
                    array_write[Int, mut[a]](a.mut, 0, 42);
                    let x = array_give[Int, given, ref[a]](a.ref, 0);
                    // Element still accessible — Int is copy, no move
                    let y = array_give[Int, given, given](a.give, 0);
                    x.give + y.give;
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Int](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_a]](_1_a . mut , 0 , 42) ;
            Output: Trace:   let _1_x = array_give [Int, given, ref [_1_a]](_1_a . ref , 0) ;
            Output: Trace:   _1_x = 42
            Output: Trace:   let _1_y = array_give [Int, given, given](_1_a . give , 0) ;
            Output: Trace:   _1_y = 42
            Output: Trace:   _1_x . give + _1_y . give ;
            Output: Trace: exit Main.main => 84
            Result: Ok: 84
            Alloc 0x14: [Int(84)]"#]])
    );
}

#[test]
fn array_drop_empty_range_is_noop() {
    // array_drop with from >= to is a no-op.
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let a = array_new[Data](2);
                    array_write[Data, mut[a]](a.mut, 0, new Data(42));
                    array_write[Data, mut[a]](a.mut, 1, new Data(99));
                    // from >= to: no-op
                    array_drop[Data, given, ref[a]](a.ref, 1, 1);
                    array_drop[Data, given, ref[a]](a.ref, 2, 0);
                    // Elements still accessible
                    array_give[Data, given, given](a.give, 0);
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ }, Data { x: ⚡ } }
            Output: Trace:   array_write [Data, mut [_1_a]](_1_a . mut , 0 , new Data (42)) ;
            Output: Trace:   array_write [Data, mut [_1_a]](_1_a . mut , 1 , new Data (99)) ;
            Output: Trace:   array_drop [Data, given, ref [_1_a]](_1_a . ref , 1 , 1) ;
            Output: Trace:   array_drop [Data, given, ref [_1_a]](_1_a . ref , 2 , 0) ;
            Output: Trace:   array_give [Data, given, given](_1_a . give , 0) ;
            Output: Trace: exit Main.main => Data { x: 42 }
            Result: Ok: Data { x: 42 }
            Alloc 0x1a: [Int(42)]"#]])
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
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Array[Int]](2);
                    let e0 = array_new[Int](1);
                    array_write[Int, mut[e0]](e0.mut, 0, 10);
                    let e1 = array_new[Int](1);
                    array_write[Int, mut[e1]](e1.mut, 0, 20);
                    array_write[Array[Int], mut[a]](a.mut, 0, e0.give);
                    array_write[Array[Int], mut[a]](a.mut, 1, e1.give);
                    // Drop the outer array without dropping elements first.
                    // Inner array backing allocations leak.
                    a.drop;
                    0;
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Array[Int]](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   let _1_e0 = array_new [Int](1) ;
            Output: Trace:   _1_e0 = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_e0]](_1_e0 . mut , 0 , 10) ;
            Output: Trace:   let _1_e1 = array_new [Int](1) ;
            Output: Trace:   _1_e1 = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_e1]](_1_e1 . mut , 0 , 20) ;
            Output: Trace:   array_write [Array[Int], mut [_1_a]](_1_a . mut , 0 , _1_e0 . give) ;
            Output: Trace:   array_write [Array[Int], mut [_1_a]](_1_a . mut , 1 , _1_e1 . give) ;
            Output: Trace:   _1_a . drop ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x07: [RefCount(1), Capacity(1), Int(10)]
            Alloc 0x0f: [RefCount(1), Capacity(1), Int(20)]
            Alloc 0x1f: [Int(0)]"#]])
    );
}

#[test]
fn array_leak_some_elements() {
    // Drop element 0 of a 2-element array, skip element 1, drop array.
    // Element 1's backing allocation remains as an orphan in the heap.
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Array[Int]](2);
                    let e0 = array_new[Int](1);
                    array_write[Int, mut[e0]](e0.mut, 0, 10);
                    let e1 = array_new[Int](1);
                    array_write[Int, mut[e1]](e1.mut, 0, 20);
                    array_write[Array[Int], mut[a]](a.mut, 0, e0.give);
                    array_write[Array[Int], mut[a]](a.mut, 1, e1.give);
                    // Drop only element 0.
                    array_drop[Array[Int], given, ref[a]](a.ref, 0, 1);
                    // Drop the array — element 1 leaks.
                    a.drop;
                    0;
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Array[Int]](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   let _1_e0 = array_new [Int](1) ;
            Output: Trace:   _1_e0 = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_e0]](_1_e0 . mut , 0 , 10) ;
            Output: Trace:   let _1_e1 = array_new [Int](1) ;
            Output: Trace:   _1_e1 = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int, mut [_1_e1]](_1_e1 . mut , 0 , 20) ;
            Output: Trace:   array_write [Array[Int], mut [_1_a]](_1_a . mut , 0 , _1_e0 . give) ;
            Output: Trace:   array_write [Array[Int], mut [_1_a]](_1_a . mut , 1 , _1_e1 . give) ;
            Output: Trace:   array_drop [Array[Int], given, ref [_1_a]](_1_a . ref , 0 , 1) ;
            Output: Trace:   _1_a . drop ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x0f: [RefCount(1), Capacity(1), Int(20)]
            Alloc 0x23: [Int(0)]"#]])
    );
}
