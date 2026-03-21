/// Tests for drop body (custom destructor) execution,
/// Bool type, comparison operators, subtraction, and is_last_ref.

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
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let d : given Data = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   () ;
            Output: Trace:   drop Data
            Output: Trace:     print(self . x . give) ;
            Output: ----->     42
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
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
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let d : given Data = new Data (99) ;
            Output: Trace:   d = Data { x: 99 }
            Output: Trace:   d . drop ;
            Output: Trace:   drop Data
            Output: Trace:     print(self . x . give) ;
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
    // `shared Data` is copy (the type is not `shared class Data`).
    crate::assert_interpret_only!(
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
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let d : given Data = new Data (77) ;
            Output: Trace:   d = Data { x: 77 }
            Output: Trace:   let s : shared Data = d . give . share ;
            Output: Trace:   s = shared Data { x: 77 }
            Output: Trace:   let s2 : shared Data = s . give ;
            Output: Trace:   s2 = shared Data { x: 77 }
            Output: Trace:   () ;
            Output: Trace:   drop Data
            Output: Trace:     print(self . x . give) ;
            Output: ----->     77
            Output: Trace:   drop Data
            Output: Trace:     print(self . x . give) ;
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
            class Main {
                fn main(given self) -> () {
                    let a: given Array[Int] = array_new[Int](1);
                    print(is_last_ref[ref[a]](a.ref));
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a : given Array[Int] = array_new [Int](1) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   print(is_last_ref [ref [a]](a . ref)) ;
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
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a : given Array[Int] = array_new [Int](1) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   let s = a . give . share ;
            Output: Trace:   s = shared Array { flag: Shared, rc: 1, ⚡ }
            Output: Trace:   let s2 : shared Array[Int] = s . give ;
            Output: Trace:   s2 = shared Array { flag: Shared, rc: 2, ⚡ }
            Output: Trace:   print(is_last_ref [ref [s2]](s2 . ref)) ;
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
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let c : given Container = new Container (array_new [Int](2), 0) ;
            Output: Trace:   c = Container { data: Array { flag: Given, rc: 1, ⚡, ⚡ }, len: 0 }
            Output: Trace:   () ;
            Output: Trace:   drop Container
            Output: Trace:     if is_last_ref [ref [self . data]](self . data . ref) { print(99) ; array_drop [Int, given, ref [self . data]](self . data . ref , 0 , self . len . give) ; } else { print(0) ; } ;
            Output: Trace:     print(99) ;
            Output: ----->     99
            Output: Trace:     array_drop [Int, given, ref [self . data]](self . data . ref , 0 , self . len . give) ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
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
            class Main {
                fn main(given self) -> () {
                    print(3 >= 2);
                    print(2 >= 3);
                    print(2 >= 2);
                    print(1 < 2);
                    print(2 < 1);
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
            Output: Trace:   print(1 < 2) ;
            Output: ----->   true
            Output: Trace:   print(2 < 1) ;
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
            class Main {
                fn main(given self) -> Int {
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
    crate::assert_interpret_only!(
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
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let p : given Pair = new Pair (array_new [Int](1), array_new [Int](1)) ;
            Output: Trace:   p = Pair { a: Array { flag: Given, rc: 1, ⚡ }, b: Array { flag: Given, rc: 1, ⚡ } }
            Output: Trace:   let moved_a = p . a . give ;
            Output: Trace:   moved_a = Array { flag: Given, rc: 1, ⚡ }
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
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let p : given Pair = new Pair (10, 20) ;
            Output: Trace:   p = Pair { x: 10, y: 20 }
            Output: Trace:   let x = p . x . give ;
            Output: Trace:   x = 10
            Output: Trace:   p . y . give ;
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
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let w : given Wrapper[Item] = new Wrapper [Item] (array_new [Item](2), 0) ;
            Output: Trace:   w = Wrapper { data: Array { flag: Given, rc: 1, Item { val: ⚡ }, Item { val: ⚡ } }, len: 0 }
            Output: Trace:   array_write [Item, mut [w . data]](w . data . mut , 0 , new Item (111)) ;
            Output: Trace:   w . len = 1 ;
            Output: Trace:   w . len = 1
            Output: Trace:   () ;
            Output: Trace:   drop Wrapper
            Output: Trace:     array_drop [Item, given, ref [self . data]](self . data . ref , 0 , self . len . give) ;
            Output: Trace:     drop Item
            Output: Trace:       print(self . val . give) ;
            Output: ----->       111
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}
