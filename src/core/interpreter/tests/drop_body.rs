/// Tests for drop body (custom destructor) execution,
/// Bool type, comparison operators, subtraction, and is_last_ref.
///
/// Interpreter-only examples with shared destructors intentionally bypass the
/// checker: structs cannot have destructors in the checked language. These
/// preserve coverage of the runtime cleanup machinery for unchecked programs.
///
/// is_last_ref coverage:
/// - sole owner: true (is_last_ref_true_when_sole_owner)
/// - two shared handles: false (is_last_ref_false_when_shared)
/// - conditional cleanup in drop body (drop_body_with_is_last_ref)
/// - place sharing handle doesn't run drop body (ref_handle_does_not_run_drop_body)
/// - sequential drops, only last triggers cleanup (is_last_ref_sequential_drops_only_last_cleans)
/// - non-boxed type always returns false (is_last_ref_non_boxed_always_false)
/// - per-allocation, not per-object (is_last_ref_per_allocation)
/// - share to rc=3, drop two, third sees true (is_last_ref_after_dropping_other_handles)

#[test]
fn class_with_drop_body() {
    // Simple class with drop body that prints a field.
    // Verify drop body runs on scope exit.
    crate::assert_interpret!(
        {
            class Data {
                x: Int;

                drop {
                    print(self.x^);
                }
            }

            struct Main {
                fn main(^ self) -> () {
                    let d: ^ Data = new Data(42);
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d : ^ Data = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   () ;
            Output: Trace:   drop Data
            Output: Trace:     print(self . x ^) ;
            Output: ----->     42
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

#[test]
fn drop_body_runs_on_give() {
    // The drop body should run at an explicit drop statement.
    crate::assert_interpret!(
        {
            class Data {
                x: Int;

                drop {
                    print(self.x^);
                }
            }

            struct Main {
                fn main(^ self) -> () {
                    let d: ^ Data = new Data(99);
                    drop d;
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d : ^ Data = new Data (99) ;
            Output: Trace:   _1_d = Data { x: 99 }
            Output: Trace:   drop _1_d ;
            Output: Trace:   drop Data
            Output: Trace:     print(self . x ^) ;
            Output: ----->     99
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

#[test]
fn drop_body_runs_on_every_shared_handle() {
    // Drop body runs once per owned handle drop.
    // Data is a share class (default), so two shared copies = two drop body executions.
    // Use assert_interpret_only! because the type checker doesn't know
    // `shared Data` is shared (the type is not `shared struct Data`).
    crate::assert_interpret_only!(
        {
            struct Data {
                x: Int;

                drop {
                    print(self.x^);
                }
            }

            struct Main {
                fn main(^ self) -> () {
                    let d: ^ Data = new Data(77);
                    let s: shared Data = d^.share;
                    let s2: shared Data = s^;
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d : ^ Data = new Data (77) ;
            Output: Trace:   _1_d = Data { x: 77 }
            Output: Trace:   let _1_s : shared Data = _1_d ^ . share ;
            Output: Trace:   _1_s = shared Data { x: 77 }
            Output: Trace:   let _1_s2 : shared Data = _1_s ^ ;
            Output: Trace:   _1_s2 = shared Data { x: 77 }
            Output: Trace:   () ;
            Output: Trace:   drop Data
            Output: Trace:     print(self . x ^) ;
            Output: ----->     77
            Output: Trace:   drop Data
            Output: Trace:     print(self . x ^) ;
            Output: ----->     77
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

#[test]
fn is_last_ref_true_when_sole_owner() {
    // Boxed object with one handle — is_last_ref returns true.
    crate::assert_interpret!(
        {
            struct Main {
                fn main(^ self) -> () {
                    let a: ^ Array[Int] = array_new[Int](1);
                    print(is_last_ref[shared[a]](a.share));
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a : ^ Array[Int] = array_new [Int](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   print(is_last_ref [shared [_1_a]](_1_a . share)) ;
            Output: ----->   true
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

#[test]
fn is_last_ref_false_when_shared() {
    // Boxed object with two handles — is_last_ref returns false on first drop.
    // Share the array, creating two shared handles (rc = 2).
    crate::assert_interpret_only!(
        {
            struct Main {
                fn main(^ self) -> () {
                    let a: ^ Array[Int] = array_new[Int](1);
                    let s = a^.share;
                    let s2: shared Array[Int] = s^;
                    print(is_last_ref[shared[s2]](s2.share));
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a : ^ Array[Int] = array_new [Int](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   let _1_s = _1_a ^ . share ;
            Output: Trace:   _1_s = shared Array { flag: SharedOwned, rc: 1, ⚡ }
            Output: Trace:   let _1_s2 : shared Array[Int] = _1_s ^ ;
            Output: Trace:   _1_s2 = shared Array { flag: SharedOwned, rc: 2, ⚡ }
            Output: Trace:   print(is_last_ref [shared [_1_s2]](_1_s2 . share)) ;
            Output: ----->   false
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

#[test]
fn drop_body_with_is_last_ref() {
    // Vec-like class that uses is_last_ref to conditionally clean up.
    crate::assert_interpret!(
        {
            class Container {
                data: Array[Int];
                len: Int;

                drop {
                    if is_last_ref[shared[self.data]](self.data.share) {
                        print(99);
                        array_drop[Int, ^, shared[self.data]](self.data.share, 0, self.len^);
                    } else {
                        print(0);
                    };
                }
            }

            struct Main {
                fn main(^ self) -> () {
                    let c: ^ Container = new Container(array_new[Int](2), 0);
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_c : ^ Container = new Container (array_new [Int](2), 0) ;
            Output: Trace:   _1_c = Container { data: Array { flag: Given, rc: 1, ⚡, ⚡ }, len: 0 }
            Output: Trace:   () ;
            Output: Trace:   drop Container
            Output: Trace:     if is_last_ref [shared [self . data]](self . data . share) { print(99) ; array_drop [Int, ^, shared [self . data]](self . data . share , 0 , self . len ^) ; } else { print(0) ; } ;
            Output: Trace:     print(99) ;
            Output: ----->     99
            Output: Trace:     array_drop [Int, ^, shared [self . data]](self . data . share , 0 , self . len ^) ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

#[test]
fn bool_true_false_literals() {
    crate::assert_interpret!(
        {
            struct Main {
                fn main(^ self) -> () {
                    print(true);
                    print(false);
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   print(true) ;
            Output: ----->   true
            Output: Trace:   print(false) ;
            Output: ----->   false
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

#[test]
fn comparison_operators() {
    crate::assert_interpret!(
        {
            struct Main {
                fn main(^ self) -> () {
                    print(3 >= 2);
                    print(2 >= 3);
                    print(2 >= 2);
                    print(2 <= 3);
                    print(3 <= 2);
                    print(3 == 3);
                    print(3 != 4);
                    print(3 != 3);
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   print(3 >= 2) ;
            Output: ----->   true
            Output: Trace:   print(2 >= 3) ;
            Output: ----->   false
            Output: Trace:   print(2 >= 2) ;
            Output: ----->   true
            Output: Trace:   print(2 <= 3) ;
            Output: ----->   true
            Output: Trace:   print(3 <= 2) ;
            Output: ----->   false
            Output: Trace:   print(3 == 3) ;
            Output: ----->   true
            Output: Trace:   print(3 != 4) ;
            Output: ----->   true
            Output: Trace:   print(3 != 3) ;
            Output: ----->   false
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

#[test]
fn subtraction() {
    crate::assert_interpret!(
        {
            struct Main {
                fn main(^ self) -> Int {
                    5 - 3;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   5 - 3 ;
            Output: Trace: exit Main.main => 2
            Result: Ok: 2
            Alloc 0x04: [Int(2)]"#]]
    );
}

#[test]
fn partially_moved_class_drops_remaining_fields() {
    // Move one field out of a class. The class is no longer "whole", so
    // its drop body should NOT run. But remaining fields should be dropped.
    // Data has an array field (boxed) so we can see it in the heap.
    crate::assert_interpret!(
        {
            class Pair {
                a: Array[Int];
                b: Array[Int];

                drop {
                    print(99);
                }
            }

            struct Main {
                fn main(^ self) -> () {
                    let p: ^ Pair = new Pair(array_new[Int](1), array_new[Int](1));
                    let moved_a = p.a^;
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_p : ^ Pair = new Pair (array_new [Int](1), array_new [Int](1)) ;
            Output: Trace:   _1_p = Pair { a: Array { flag: Given, rc: 1, ⚡ }, b: Array { flag: Given, rc: 1, ⚡ } }
            Output: Trace:   let _1_moved_a = _1_p . a ^ ;
            Output: Trace:   _1_moved_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

#[test]
fn partial_move_then_read_other_field() {
    // Move one field, then read a sibling field. This is the pattern
    // Iterator.drop relies on.
    crate::assert_interpret_only!(
        {
            struct Pair {
                x: Int;
                y: Int;
            }

            struct Main {
                fn main(^ self) -> Int {
                    let p: ^ Pair = new Pair(10, 20);
                    let x = p.x^;
                    p.y^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_p : ^ Pair = new Pair (10, 20) ;
            Output: Trace:   _1_p = Pair { x: 10, y: 20 }
            Output: Trace:   let _1_x = _1_p . x ^ ;
            Output: Trace:   _1_x = 10
            Output: Trace:   _1_p . y ^ ;
            Output: Trace: exit Main.main => 20
            Result: Ok: 20
            Alloc 0x08: [Int(20)]"#]]
    );
}

#[test]
fn drop_body_accesses_class_generics() {
    // Drop body can use the class's type parameters.
    crate::assert_interpret!(
        {
            class Wrapper[ty T] {
                data: Array[T];
                len: Int;

                drop {
                    array_drop[T, ^, shared[self.data]](self.data.share, 0, self.len^);
                }
            }

            class Item {
                val: Int;

                drop {
                    print(self.val^);
                }
            }

            struct Main {
                fn main(^ self) -> () {
                    let w: ^ Wrapper[Item] = new Wrapper[Item](array_new[Item](2), 0);
                    array_write[Item, ![w.data]](w.data!, 0, new Item(111));
                    w.len = 1;
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_w : ^ Wrapper[Item] = new Wrapper [Item] (array_new [Item](2), 0) ;
            Output: Trace:   _1_w = Wrapper { data: Array { flag: Given, rc: 1, Item { val: ⚡ }, Item { val: ⚡ } }, len: 0 }
            Output: Trace:   array_write [Item, ! [_1_w . data]](_1_w . data ! , 0 , new Item (111)) ;
            Output: Trace:   _1_w . len = 1 ;
            Output: Trace:   _1_w . len = 1
            Output: Trace:   () ;
            Output: Trace:   drop Wrapper
            Output: Trace:     array_drop [Item, ^, shared [self . data]](self . data . share , 0 , self . len ^) ;
            Output: Trace:     drop Item
            Output: Trace:       print(self . val ^) ;
            Output: ----->       111
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

// ---------------------------------------------------------------
// is_last_ref edge cases
// ---------------------------------------------------------------

#[test]
fn ref_handle_does_not_run_drop_body() {
    // A borrowed (place sharing) handle is not owned, so dropping it should NOT
    // execute the drop body. Only ^/shared handles run the drop body.
    // Here we create d (owned) and r (place sharing to d). At end of scope, both are
    // dropped. The drop body should run exactly once — for d, not for r.
    crate::assert_interpret_only!(
        {
            struct Data {
                x: Int;

                drop {
                    print(self.x^);
                }
            }

            struct Main {
                fn main(^ self) -> () {
                    let d: ^ Data = new Data(42);
                    let r: shared[d] Data = d.share;
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d : ^ Data = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   let _1_r : shared [_1_d] Data = _1_d . share ;
            Output: Trace:   _1_r = shared [_1_d] Data { x: 42 }
            Output: Trace:   () ;
            Output: Trace:   drop Data
            Output: Trace:     print(self . x ^) ;
            Output: ----->     42
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

#[test]
fn is_last_ref_sequential_drops_only_last_cleans() {
    // Create a Container with is_last_ref guarded cleanup.
    // Share it into 3 handles. Drop them one by one.
    // Only the last drop should print 99 (cleanup), earlier drops print 0.
    crate::assert_interpret_only!(
        {
            struct Container {
                data: Array[Int];
                len: Int;

                drop {
                    if is_last_ref[shared[self.data]](self.data.share) {
                        print(99);
                    } else {
                        print(0);
                    };
                }
            }

            struct Main {
                fn main(^ self) -> () {
                    let c: ^ Container = new Container(array_new[Int](2), 0);
                    let s: shared Container = c^.share;
                    let s2: shared Container = s^;
                    let s3: shared Container = s^;
                    drop s3;
                    drop s2;
                    drop s;
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_c : ^ Container = new Container (array_new [Int](2), 0) ;
            Output: Trace:   _1_c = Container { data: Array { flag: Given, rc: 1, ⚡, ⚡ }, len: 0 }
            Output: Trace:   let _1_s : shared Container = _1_c ^ . share ;
            Output: Trace:   _1_s = shared Container { data: Array { flag: SharedOwned, rc: 1, ⚡, ⚡ }, len: 0 }
            Output: Trace:   let _1_s2 : shared Container = _1_s ^ ;
            Output: Trace:   _1_s2 = shared Container { data: Array { flag: SharedOwned, rc: 2, ⚡, ⚡ }, len: 0 }
            Output: Trace:   let _1_s3 : shared Container = _1_s ^ ;
            Output: Trace:   _1_s3 = shared Container { data: Array { flag: SharedOwned, rc: 3, ⚡, ⚡ }, len: 0 }
            Output: Trace:   drop _1_s3 ;
            Output: Trace:   drop Container
            Output: Trace:     if is_last_ref [shared [self . data]](self . data . share) { print(99) ; } else { print(0) ; } ;
            Output: Trace:     print(0) ;
            Output: ----->     0
            Output: Trace:   drop _1_s2 ;
            Output: Trace:   drop Container
            Output: Trace:     if is_last_ref [shared [self . data]](self . data . share) { print(99) ; } else { print(0) ; } ;
            Output: Trace:     print(0) ;
            Output: ----->     0
            Output: Trace:   drop _1_s ;
            Output: Trace:   drop Container
            Output: Trace:     if is_last_ref [shared [self . data]](self . data . share) { print(99) ; } else { print(0) ; } ;
            Output: Trace:     print(99) ;
            Output: ----->     99
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

#[test]
fn is_last_ref_non_boxed_always_false() {
    // is_last_ref on a non-boxed type always returns false.
    // There is no reference count to check.
    crate::assert_interpret!(
        {
            struct Data {
                x: Int;
            }

            struct Main {
                fn main(^ self) -> () {
                    let d: ^ Data = new Data(42);
                    print(is_last_ref[shared[d]](d.share));
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d : ^ Data = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   print(is_last_ref [shared [_1_d]](_1_d . share)) ;
            Output: ----->   false
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

#[test]
fn is_last_ref_per_allocation() {
    // is_last_ref is per-allocation, not per-object.
    // A class holding two arrays: one shared (rc=2), one sole (rc=1).
    // is_last_ref returns different answers for each.
    crate::assert_interpret_only!(
        {
            struct TwoArrays {
                a: Array[Int];
                b: Array[Int];
            }

            struct Main {
                fn main(^ self) -> () {
                    let arr_a: ^ Array[Int] = array_new[Int](1);
                    let shared_a: shared Array[Int] = arr_a^.share;
                    let extra_handle: shared Array[Int] = shared_a^;
                    let obj: ^ TwoArrays = new TwoArrays(shared_a^, array_new[Int](1));
                    print(is_last_ref[shared[obj.a]](obj.a.share));
                    print(is_last_ref[shared[obj.b]](obj.b.share));
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_arr_a : ^ Array[Int] = array_new [Int](1) ;
            Output: Trace:   _1_arr_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   let _1_shared_a : shared Array[Int] = _1_arr_a ^ . share ;
            Output: Trace:   _1_shared_a = shared Array { flag: SharedOwned, rc: 1, ⚡ }
            Output: Trace:   let _1_extra_handle : shared Array[Int] = _1_shared_a ^ ;
            Output: Trace:   _1_extra_handle = shared Array { flag: SharedOwned, rc: 2, ⚡ }
            Output: Trace:   let _1_obj : ^ TwoArrays = new TwoArrays (_1_shared_a ^, array_new [Int](1)) ;
            Output: Trace:   _1_obj = TwoArrays { a: Array { flag: SharedOwned, rc: 3, ⚡ }, b: Array { flag: Given, rc: 1, ⚡ } }
            Output: Trace:   print(is_last_ref [shared [_1_obj . a]](_1_obj . a . share)) ;
            Output: ----->   false
            Output: Trace:   print(is_last_ref [shared [_1_obj . b]](_1_obj . b . share)) ;
            Output: ----->   true
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

#[test]
fn is_last_ref_after_dropping_other_handles() {
    // Start with rc=3 (share into 3 handles). Drop two handles (no drop body
    // on the array itself). Then check is_last_ref on the remaining handle.
    // Should return true since rc is back to 1.
    crate::assert_interpret_only!(
        {
            struct Main {
                fn main(^ self) -> () {
                    let a: ^ Array[Int] = array_new[Int](1);
                    let s: shared Array[Int] = a^.share;
                    let s2: shared Array[Int] = s^;
                    let s3: shared Array[Int] = s^;
                    drop s2;
                    drop s3;
                    print(is_last_ref[shared[s]](s.share));
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a : ^ Array[Int] = array_new [Int](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   let _1_s : shared Array[Int] = _1_a ^ . share ;
            Output: Trace:   _1_s = shared Array { flag: SharedOwned, rc: 1, ⚡ }
            Output: Trace:   let _1_s2 : shared Array[Int] = _1_s ^ ;
            Output: Trace:   _1_s2 = shared Array { flag: SharedOwned, rc: 2, ⚡ }
            Output: Trace:   let _1_s3 : shared Array[Int] = _1_s ^ ;
            Output: Trace:   _1_s3 = shared Array { flag: SharedOwned, rc: 3, ⚡ }
            Output: Trace:   drop _1_s2 ;
            Output: Trace:   drop _1_s3 ;
            Output: Trace:   print(is_last_ref [shared [_1_s]](_1_s . share)) ;
            Output: ----->   true
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}
