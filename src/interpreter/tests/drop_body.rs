/// Tests for drop body (custom destructor) execution,
/// Bool type, comparison operators, subtraction, and is_last_ref.
///
/// is_last_ref coverage:
/// - sole owner: true (is_last_ref_true_when_sole_owner)
/// - two shared handles: false (is_last_ref_false_when_shared)
/// - conditional cleanup in drop body (drop_body_with_is_last_ref)
/// - ref handle doesn't run drop body (ref_handle_does_not_run_drop_body)
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
                    print(self.x.give);
                }
            }

            class Main {
                fn main(given self) -> () {
                    let d: given Data = new Data(42);
                    ();
                }
            }
        },
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d : given Data = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   () ;
            Output: Trace:   drop Data
            Output: Trace:     print(self . x . give) ;
            Output: ----->     42
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]])
    );
}

#[test]
fn drop_body_runs_on_give() {
    // The drop body should run when a value is explicitly dropped via .drop
    crate::assert_interpret!(
        {
            class Data {
                x: Int;

                drop {
                    print(self.x.give);
                }
            }

            class Main {
                fn main(given self) -> () {
                    let d: given Data = new Data(99);
                    d.drop;
                    ();
                }
            }
        },
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d : given Data = new Data (99) ;
            Output: Trace:   _1_d = Data { x: 99 }
            Output: Trace:   _1_d . drop ;
            Output: Trace:   drop Data
            Output: Trace:     print(self . x . give) ;
            Output: ----->     99
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]])
    );
}

#[test]
fn drop_body_runs_on_every_shared_handle() {
    // Drop body runs once per owned handle drop.
    // Data is a share class (default), so two shared copies = two drop body executions.
    crate::assert_interpret!(
        {
            class Data {
                x: Int;

                drop {
                    print(self.x.give);
                }
            }

            class Main {
                fn main(given self) -> () {
                    let d: given Data = new Data(77);
                    let s: shared Data = d.give.share;
                    let s2: shared Data = s.give;
                    ();
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d : given Data = new Data (77) ;
            Output: Trace:   _1_d = Data { x: 77 }
            Output: Trace:   let _1_s : shared Data = _1_d . give . share ;
            Output: Trace:   _1_s = shared Data { x: 77 }
            Output: Trace:   let _1_s2 : shared Data = _1_s . give ;
            Output: Trace:   _1_s2 = shared Data { x: 77 }
            Output: Trace:   () ;
            Output: Trace:   drop Data
            Output: Trace:     print(self . x . give) ;
            Output: ----->     77
            Output: Trace:   drop Data
            Output: Trace:     print(self . x . give) ;
            Output: ----->     77
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]])
    );
}

#[test]
fn is_last_ref_true_when_sole_owner() {
    // Boxed object with one handle — is_last_ref returns true.
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> () {
                    let a: given Array[Int] = array_new[Int](1);
                    print(is_last_ref[ref[a]](a.ref));
                    ();
                }
            }
        },
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a : given Array[Int] = array_new [Int](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   print(is_last_ref [ref [_1_a]](_1_a . ref)) ;
            Output: ----->   true
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]])
    );
}

#[test]
fn is_last_ref_false_when_shared() {
    // Boxed object with two handles — is_last_ref returns false on first drop.
    // Share the array, creating two shared handles (rc = 2).
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> () {
                    let a: given Array[Int] = array_new[Int](1);
                    let s = a.give.share;
                    let s2: shared Array[Int] = s.give;
                    print(is_last_ref[ref[s2]](s2.ref));
                    ();
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a : given Array[Int] = array_new [Int](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   let _1_s = _1_a . give . share ;
            Output: Trace:   _1_s = shared Array { flag: Shared, rc: 1, ⚡ }
            Output: Trace:   let _1_s2 : shared Array[Int] = _1_s . give ;
            Output: Trace:   _1_s2 = shared Array { flag: Shared, rc: 2, ⚡ }
            Output: Trace:   print(is_last_ref [ref [_1_s2]](_1_s2 . ref)) ;
            Output: ----->   false
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]])
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
                    if is_last_ref[ref[self.data]](self.data.ref) {
                        print(99);
                        array_drop[Int, given, ref[self.data]](self.data.ref, 0, self.len.give);
                    } else {
                        print(0);
                    };
                }
            }

            class Main {
                fn main(given self) -> () {
                    let c: given Container = new Container(array_new[Int](2), 0);
                    ();
                }
            }
        },
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_c : given Container = new Container (array_new [Int](2), 0) ;
            Output: Trace:   _1_c = Container { data: Array { flag: Given, rc: 1, ⚡, ⚡ }, len: 0 }
            Output: Trace:   () ;
            Output: Trace:   drop Container
            Output: Trace:     if is_last_ref [ref [self . data]](self . data . ref) { print(99) ; array_drop [Int, given, ref [self . data]](self . data . ref , 0 , self . len . give) ; } else { print(0) ; } ;
            Output: Trace:     print(99) ;
            Output: ----->     99
            Output: Trace:     array_drop [Int, given, ref [self . data]](self . data . ref , 0 , self . len . give) ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]])
    );
}

#[test]
fn bool_true_false_literals() {
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> () {
                    print(true);
                    print(false);
                    ();
                }
            }
        },
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   print(true) ;
            Output: ----->   true
            Output: Trace:   print(false) ;
            Output: ----->   false
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]])
    );
}

#[test]
fn comparison_operators() {
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> () {
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
         type: ok, interpret: ok(expect_test::expect![[r#"
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
            Result: Ok: ()"#]])
    );
}

#[test]
fn subtraction() {
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    5 - 3;
                }
            }
        },
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   5 - 3 ;
            Output: Trace: exit Main.main => 2
            Result: Ok: 2
            Alloc 0x04: [Int(2)]"#]])
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

            class Main {
                fn main(given self) -> () {
                    let p: given Pair = new Pair(array_new[Int](1), array_new[Int](1));
                    let moved_a = p.a.give;
                    ();
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_p : given Pair = new Pair (array_new [Int](1), array_new [Int](1)) ;
            Output: Trace:   _1_p = Pair { a: Array { flag: Given, rc: 1, ⚡ }, b: Array { flag: Given, rc: 1, ⚡ } }
            Output: Trace:   let _1_moved_a = _1_p . a . give ;
            Output: Trace:   _1_moved_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]])
    );
}

#[test]
fn partial_move_then_read_other_field() {
    // Move one field, then read a sibling field. This is the pattern
    // Iterator.drop relies on.
    crate::assert_interpret!(
        {
            class Pair {
                x: Int;
                y: Int;
            }

            class Main {
                fn main(given self) -> Int {
                    let p: given Pair = new Pair(10, 20);
                    let x = p.x.give;
                    p.y.give;
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_p : given Pair = new Pair (10, 20) ;
            Output: Trace:   _1_p = Pair { x: 10, y: 20 }
            Output: Trace:   let _1_x = _1_p . x . give ;
            Output: Trace:   _1_x = 10
            Output: Trace:   _1_p . y . give ;
            Output: Trace: exit Main.main => 20
            Result: Ok: 20
            Alloc 0x08: [Int(20)]"#]])
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
                    array_drop[T, given, ref[self.data]](self.data.ref, 0, self.len.give);
                }
            }

            class Item {
                val: Int;

                drop {
                    print(self.val.give);
                }
            }

            class Main {
                fn main(given self) -> () {
                    let w: given Wrapper[Item] = new Wrapper[Item](array_new[Item](2), 0);
                    array_write[Item, mut[w.data]](w.data.mut, 0, new Item(111));
                    w.len = 1;
                    ();
                }
            }
        },
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_w : given Wrapper[Item] = new Wrapper [Item] (array_new [Item](2), 0) ;
            Output: Trace:   _1_w = Wrapper { data: Array { flag: Given, rc: 1, Item { val: ⚡ }, Item { val: ⚡ } }, len: 0 }
            Output: Trace:   array_write [Item, mut [_1_w . data]](_1_w . data . mut , 0 , new Item (111)) ;
            Output: Trace:   _1_w . len = 1 ;
            Output: Trace:   _1_w . len = 1
            Output: Trace:   () ;
            Output: Trace:   drop Wrapper
            Output: Trace:     array_drop [Item, given, ref [self . data]](self . data . ref , 0 , self . len . give) ;
            Output: Trace:     drop Item
            Output: Trace:       print(self . val . give) ;
            Output: ----->       111
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]])
    );
}

// ---------------------------------------------------------------
// is_last_ref edge cases
// ---------------------------------------------------------------

#[test]
fn ref_handle_does_not_run_drop_body() {
    // A borrowed (ref) handle is not owned, so dropping it should NOT
    // execute the drop body. Only given/shared handles run the drop body.
    // Here we create d (owned) and r (ref to d). At end of scope, both are
    // dropped. The drop body should run exactly once — for d, not for r.
    crate::assert_interpret!(
        {
            class Data {
                x: Int;

                drop {
                    print(self.x.give);
                }
            }

            class Main {
                fn main(given self) -> () {
                    let d: given Data = new Data(42);
                    let r: ref[d] Data = d.ref;
                    ();
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d : given Data = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   let _1_r : ref [_1_d] Data = _1_d . ref ;
            Output: Trace:   _1_r = ref [_1_d] Data { x: 42 }
            Output: Trace:   () ;
            Output: Trace:   drop Data
            Output: Trace:     print(self . x . give) ;
            Output: ----->     42
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]])
    );
}

#[test]
fn is_last_ref_sequential_drops_only_last_cleans() {
    // Create a Container with is_last_ref guarded cleanup.
    // Share it into 3 handles. Drop them one by one.
    // Only the last drop should print 99 (cleanup), earlier drops print 0.
    crate::assert_interpret!(
        {
            class Container {
                data: Array[Int];
                len: Int;

                drop {
                    if is_last_ref[ref[self.data]](self.data.ref) {
                        print(99);
                    } else {
                        print(0);
                    };
                }
            }

            class Main {
                fn main(given self) -> () {
                    let c: given Container = new Container(array_new[Int](2), 0);
                    let s: shared Container = c.give.share;
                    let s2: shared Container = s.give;
                    let s3: shared Container = s.give;
                    s3.drop;
                    s2.drop;
                    s.drop;
                    ();
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_c : given Container = new Container (array_new [Int](2), 0) ;
            Output: Trace:   _1_c = Container { data: Array { flag: Given, rc: 1, ⚡, ⚡ }, len: 0 }
            Output: Trace:   let _1_s : shared Container = _1_c . give . share ;
            Output: Trace:   _1_s = shared Container { data: Array { flag: Shared, rc: 1, ⚡, ⚡ }, len: 0 }
            Output: Trace:   let _1_s2 : shared Container = _1_s . give ;
            Output: Trace:   _1_s2 = shared Container { data: Array { flag: Shared, rc: 2, ⚡, ⚡ }, len: 0 }
            Output: Trace:   let _1_s3 : shared Container = _1_s . give ;
            Output: Trace:   _1_s3 = shared Container { data: Array { flag: Shared, rc: 3, ⚡, ⚡ }, len: 0 }
            Output: Trace:   _1_s3 . drop ;
            Output: Trace:   drop Container
            Output: Trace:     if is_last_ref [ref [self . data]](self . data . ref) { print(99) ; } else { print(0) ; } ;
            Output: Trace:     print(0) ;
            Output: ----->     0
            Output: Trace:   _1_s2 . drop ;
            Output: Trace:   drop Container
            Output: Trace:     if is_last_ref [ref [self . data]](self . data . ref) { print(99) ; } else { print(0) ; } ;
            Output: Trace:     print(0) ;
            Output: ----->     0
            Output: Trace:   _1_s . drop ;
            Output: Trace:   drop Container
            Output: Trace:     if is_last_ref [ref [self . data]](self . data . ref) { print(99) ; } else { print(0) ; } ;
            Output: Trace:     print(99) ;
            Output: ----->     99
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]])
    );
}

#[test]
fn is_last_ref_non_boxed_always_false() {
    // is_last_ref on a non-boxed type always returns false.
    // There is no refcount to check.
    crate::assert_interpret!(
        {
            class Data {
                x: Int;
            }

            class Main {
                fn main(given self) -> () {
                    let d: given Data = new Data(42);
                    print(is_last_ref[ref[d]](d.ref));
                    ();
                }
            }
        },
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d : given Data = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   print(is_last_ref [ref [_1_d]](_1_d . ref)) ;
            Output: ----->   false
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]])
    );
}

#[test]
fn is_last_ref_per_allocation() {
    // is_last_ref is per-allocation, not per-object.
    // A class holding two arrays: one shared (rc=2), one sole (rc=1).
    // is_last_ref returns different answers for each.
    crate::assert_interpret!(
        {
            class TwoArrays {
                a: shared Array[Int];
                b: shared Array[Int];
            }

            class Main {
                fn main(given self) -> () {
                    let arr_a: given Array[Int] = array_new[Int](1);
                    let shared_a: shared Array[Int] = arr_a.give.share;
                    let extra_handle: shared Array[Int] = shared_a.give;
                    let obj: given TwoArrays = new TwoArrays(shared_a.give, array_new[Int](1).share);
                    print(is_last_ref[ref[obj.a]](obj.a.ref));
                    print(is_last_ref[ref[obj.b]](obj.b.ref));
                    ();
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_arr_a : given Array[Int] = array_new [Int](1) ;
            Output: Trace:   _1_arr_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   let _1_shared_a : shared Array[Int] = _1_arr_a . give . share ;
            Output: Trace:   _1_shared_a = shared Array { flag: Shared, rc: 1, ⚡ }
            Output: Trace:   let _1_extra_handle : shared Array[Int] = _1_shared_a . give ;
            Output: Trace:   _1_extra_handle = shared Array { flag: Shared, rc: 2, ⚡ }
            Output: Trace:   let _1_obj : given TwoArrays = new TwoArrays (_1_shared_a . give, array_new [Int](1) . share) ;
            Output: Trace:   _1_obj = TwoArrays { a: shared Array { flag: Shared, rc: 3, ⚡ }, b: shared Array { flag: Shared, rc: 1, ⚡ } }
            Output: Trace:   print(is_last_ref [ref [_1_obj . a]](_1_obj . a . ref)) ;
            Output: ----->   false
            Output: Trace:   print(is_last_ref [ref [_1_obj . b]](_1_obj . b . ref)) ;
            Output: ----->   true
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]])
    );
}

#[test]
fn is_last_ref_after_dropping_other_handles() {
    // Start with rc=3 (share into 3 handles). Drop two handles (no drop body
    // on the array itself). Then check is_last_ref on the remaining handle.
    // Should return true since rc is back to 1.
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> () {
                    let a: given Array[Int] = array_new[Int](1);
                    let s: shared Array[Int] = a.give.share;
                    let s2: shared Array[Int] = s.give;
                    let s3: shared Array[Int] = s.give;
                    s2.drop;
                    s3.drop;
                    print(is_last_ref[ref[s]](s.ref));
                    ();
                }
            }
        },
        type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a : given Array[Int] = array_new [Int](1) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   let _1_s : shared Array[Int] = _1_a . give . share ;
            Output: Trace:   _1_s = shared Array { flag: Shared, rc: 1, ⚡ }
            Output: Trace:   let _1_s2 : shared Array[Int] = _1_s . give ;
            Output: Trace:   _1_s2 = shared Array { flag: Shared, rc: 2, ⚡ }
            Output: Trace:   let _1_s3 : shared Array[Int] = _1_s . give ;
            Output: Trace:   _1_s3 = shared Array { flag: Shared, rc: 3, ⚡ }
            Output: Trace:   _1_s2 . drop ;
            Output: Trace:   _1_s3 . drop ;
            Output: Trace:   print(is_last_ref [ref [_1_s]](_1_s . ref)) ;
            Output: ----->   true
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]])
    );
}
