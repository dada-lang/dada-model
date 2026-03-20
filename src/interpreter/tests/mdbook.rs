/// Tests extracted from the mdbook interpreter chapter.
/// Each test is wrapped in ANCHOR comments so the mdbook-judgment
/// preprocessor can include them in the rendered book.

#[test]
fn interp_point_example() {
    // ANCHOR: interp_point_example
    crate::assert_interpret!(
        {
            class Point {
                x: Int;
                y: Int;
            }

            class Main {
                fn main(given self) -> Point {
                    let p = new Point(22, 44);
                    p.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let p = new Point (22, 44) ;
            Output: Trace:   p = Point { x: 22, y: 44 }
            Output: Trace:   p . give ;
            Output: Trace: exit Main.main => Point { x: 22, y: 44 }
            Result: Ok: Point { x: 22, y: 44 }
            Alloc 0x06: [Int(22), Int(44)]"#]]
    );
    // ANCHOR_END: interp_point_example
}

#[test]
fn interp_arithmetic() {
    // ANCHOR: interp_arithmetic
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    let x = 10;
                    let y = 20;
                    x.give + y.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let x = 10 ;
            Output: Trace:   x = 10
            Output: Trace:   let y = 20 ;
            Output: Trace:   y = 20
            Output: Trace:   x . give + y . give ;
            Output: Trace: exit Main.main => 30
            Result: Ok: 30
            Alloc 0x08: [Int(30)]"#]]
    );
    // ANCHOR_END: interp_arithmetic
}

#[test]
fn interp_method_calls() {
    // ANCHOR: interp_method_calls
    crate::assert_interpret!(
        {
            class Adder {
                a: Int;
                b: Int;

                fn sum(given self) -> Int {
                    self.a.give + self.b.give;
                }
            }

            class Main {
                fn main(given self) -> Int {
                    let adder = new Adder(3, 4);
                    adder.give.sum();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let adder = new Adder (3, 4) ;
            Output: Trace:   adder = Adder { a: 3, b: 4 }
            Output: Trace:   adder . give . sum () ;
            Output: Trace:   enter Adder.sum
            Output: Trace:     self . a . give + self . b . give ;
            Output: Trace:   exit Adder.sum => 7
            Output: Trace: exit Main.main => 7
            Result: Ok: 7
            Alloc 0x0a: [Int(7)]"#]]
    );
    // ANCHOR_END: interp_method_calls
}

#[test]
fn interp_give_given() {
    // ANCHOR: interp_give_given
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    d.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   d . give ;
            Output: Trace: exit Main.main => Data { x: 42 }
            Result: Ok: Data { x: 42 }
            Alloc 0x05: [Int(42)]"#]]
    );
    // ANCHOR_END: interp_give_given
}

#[test]
fn interp_give_shared() {
    // ANCHOR: interp_give_shared
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    let s = d.give.share;
                    let x1 = s.give;
                    let x2 = s.give;
                    print(x1.give);
                    x2.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   let s = d . give . share ;
            Output: Trace:   s = shared Data { x: 42 }
            Output: Trace:   let x1 = s . give ;
            Output: Trace:   x1 = shared Data { x: 42 }
            Output: Trace:   let x2 = s . give ;
            Output: Trace:   x2 = shared Data { x: 42 }
            Output: Trace:   print(x1 . give) ;
            Output: ----->   shared Data { x: 42 }
            Output: Trace:   x2 . give ;
            Output: Trace: exit Main.main => shared Data { x: 42 }
            Result: Ok: shared Data { x: 42 }
            Alloc 0x0d: [Int(42)]"#]]
    );
    // ANCHOR_END: interp_give_shared
}

#[test]
fn interp_ref_given() {
    // ANCHOR: interp_ref_given
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    print(d.ref);
                    d.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   print(d . ref) ;
            Output: ----->   ref [d] Data { x: 42 }
            Output: Trace:   d . give ;
            Output: Trace: exit Main.main => Data { x: 42 }
            Result: Ok: Data { x: 42 }
            Alloc 0x07: [Int(42)]"#]]
    );
    // ANCHOR_END: interp_ref_given
}

#[test]
fn interp_ref_shared() {
    // ANCHOR: interp_ref_shared
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    let s = d.give.share;
                    s.ref;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   let s = d . give . share ;
            Output: Trace:   s = shared Data { x: 42 }
            Output: Trace:   s . ref ;
            Output: Trace: exit Main.main => shared Data { x: 42 }
            Result: Ok: shared Data { x: 42 }
            Alloc 0x07: [Int(42)]"#]]
    );
    // ANCHOR_END: interp_ref_shared
}

#[test]
fn interp_share_recursive() {
    // ANCHOR: interp_share_recursive
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(given self) -> Outer {
                    let o = new Outer(new Inner(1));
                    o.give.share;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let o = new Outer (new Inner (1)) ;
            Output: Trace:   o = Outer { inner: Inner { x: 1 } }
            Output: Trace:   o . give . share ;
            Output: Trace: exit Main.main => shared Outer { inner: Inner { x: 1 } }
            Result: Ok: shared Outer { inner: Inner { x: 1 } }
            Alloc 0x06: [Int(1)]"#]]
    );
    // ANCHOR_END: interp_share_recursive
}

#[test]
fn interp_drop_borrowed_noop() {
    // ANCHOR: interp_drop_borrowed_noop
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    let r = d.ref;
                    r.drop;
                    r.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   let r = d . ref ;
            Output: Trace:   r = ref [d] Data { x: 42 }
            Output: Trace:   r . drop ;
            Output: Trace:   r . give ;
            Output: Trace: exit Main.main => ref [d] Data { x: 42 }
            Result: Ok: ref [d] Data { x: 42 }
            Alloc 0x08: [Int(42)]"#]]
    );
    // ANCHOR_END: interp_drop_borrowed_noop
}

#[test]
fn interp_conditional_true() {
    // ANCHOR: interp_conditional_true
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    let result = 0;
                    if 1 { result = 42; } else { result = 0; };
                    result.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let result = 0 ;
            Output: Trace:   result = 0
            Output: Trace:   if 1 { result = 42 ; } else { result = 0 ; } ;
            Output: Trace:   result = 42 ;
            Output: Trace:   result = 42
            Output: Trace:   result . give ;
            Output: Trace: exit Main.main => 42
            Result: Ok: 42
            Alloc 0x08: [Int(42)]"#]]
    );
    // ANCHOR_END: interp_conditional_true
}

#[test]
fn interp_conditional_false() {
    // ANCHOR: interp_conditional_false
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    let result = 0;
                    if 0 { result = 42; } else { result = 99; };
                    result.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let result = 0 ;
            Output: Trace:   result = 0
            Output: Trace:   if 0 { result = 42 ; } else { result = 99 ; } ;
            Output: Trace:   result = 99 ;
            Output: Trace:   result = 99
            Output: Trace:   result . give ;
            Output: Trace: exit Main.main => 99
            Result: Ok: 99
            Alloc 0x08: [Int(99)]"#]]
    );
    // ANCHOR_END: interp_conditional_false
}

// ---------------------------------------------------------------
// Array[T] examples for the interpreter chapter
// ---------------------------------------------------------------

#[test]
fn interp_array_new_and_get() {
    // ANCHOR: interp_array_new_and_get
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](3);
                    array_write[Int](a.mut, 0, 10);
                    array_write[Int](a.mut, 1, 20);
                    array_write[Int](a.mut, 2, 30);
                    print(array_give[Int](a.ref, 0));
                    print(array_give[Int](a.ref, 1));
                    array_give[Int](a.give, 2);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](3) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡, ⚡ }
            Output: Trace:   array_write [Int](a . mut , 0 , 10) ;
            Output: Trace:   array_write [Int](a . mut , 1 , 20) ;
            Output: Trace:   array_write [Int](a . mut , 2 , 30) ;
            Output: Trace:   print(array_give [Int](a . ref , 0)) ;
            Output: ----->   10
            Output: Trace:   print(array_give [Int](a . ref , 1)) ;
            Output: ----->   20
            Output: Trace:   array_give [Int](a . give , 2) ;
            Output: Trace: exit Main.main => 30
            Result: Ok: 30
            Alloc 0x1c: [Int(30)]"#]]
    );
    // ANCHOR_END: interp_array_new_and_get
}

#[test]
fn interp_array_class_elements() {
    // ANCHOR: interp_array_class_elements
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let a = array_new[Data](2);
                    array_write[Data](a.mut, 0, new Data(42));
                    array_write[Data](a.mut, 1, new Data(99));
                    print(array_give[Data](a.ref, 0));
                    array_give[Data](a.give, 1);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Data](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, Data { x: ⚡ }, Data { x: ⚡ } }
            Output: Trace:   array_write [Data](a . mut , 0 , new Data (42)) ;
            Output: Trace:   array_write [Data](a . mut , 1 , new Data (99)) ;
            Output: Trace:   print(array_give [Data](a . ref , 0)) ;
            Output: ----->   ref [a] Data { x: 42 }
            Output: Trace:   array_give [Data](a . give , 1) ;
            Output: Trace: exit Main.main => Data { x: 99 }
            Result: Ok: Data { x: 99 }
            Alloc 0x16: [Int(99)]"#]]
    );
    // ANCHOR_END: interp_array_class_elements
}

#[test]
fn interp_array_int_is_copy() {
    // ANCHOR: interp_array_int_is_copy
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](1);
                    array_write[Int](a.mut, 0, 42);
                    let x = array_give[Int](a.ref, 0);
                    let y = array_give[Int](a.ref, 0);
                    print(x.give);
                    y.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](1) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   array_write [Int](a . mut , 0 , 42) ;
            Output: Trace:   let x = array_give [Int](a . ref , 0) ;
            Output: Trace:   x = 42
            Output: Trace:   let y = array_give [Int](a . ref , 0) ;
            Output: Trace:   y = 42
            Output: Trace:   print(x . give) ;
            Output: ----->   42
            Output: Trace:   y . give ;
            Output: Trace: exit Main.main => 42
            Result: Ok: 42
            Alloc 0x14: [Int(42)]"#]]
    );
    // ANCHOR_END: interp_array_int_is_copy
}

#[test]
fn interp_array_class_shared_no_move() {
    // ANCHOR: interp_array_class_shared_no_move
    // Shared array: class elements are accessed with shared semantics —
    // giving an element produces a shared copy, element remains available.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let a = array_new[Data](1);
                    array_write[Data](a.mut, 0, new Data(42));
                    let s = a.give.share;
                    let x = array_give[Data](s.ref, 0);
                    print(x.give);
                    // Element still available — shared, no move.
                    array_give[Data](s.give, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Data](1) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, Data { x: ⚡ } }
            Output: Trace:   array_write [Data](a . mut , 0 , new Data (42)) ;
            Output: Trace:   let s = a . give . share ;
            Output: Trace:   s = shared Array { flag: Shared, rc: 1, Data { x: 42 } }
            Output: Trace:   let x = array_give [Data](s . ref , 0) ;
            Output: Trace:   x = ref [s] shared Data { x: 42 }
            Output: Trace:   print(x . give) ;
            Output: ----->   ref [s] shared Data { x: 42 }
            Output: Trace:   array_give [Data](s . give , 0) ;
            Output: Trace: exit Main.main => shared Data { x: 42 }
            Result: Ok: shared Data { x: 42 }
            Alloc 0x15: [Int(42)]"#]]
    );
    // ANCHOR_END: interp_array_class_shared_no_move
}

#[test]
fn interp_array_shared_refcount() {
    // ANCHOR: interp_array_shared_refcount
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_write[Int](a.mut, 0, 10);
                    array_write[Int](a.mut, 1, 20);
                    let s = a.give.share;
                    let b = s.give;
                    s.drop;
                    print(array_give[Int](b.ref, 0));
                    array_give[Int](b.give, 1);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int](a . mut , 0 , 10) ;
            Output: Trace:   array_write [Int](a . mut , 1 , 20) ;
            Output: Trace:   let s = a . give . share ;
            Output: Trace:   s = shared Array { flag: Shared, rc: 1, 10, 20 }
            Output: Trace:   let b = s . give ;
            Output: Trace:   b = shared Array { flag: Shared, rc: 2, 10, 20 }
            Output: Trace:   s . drop ;
            Output: Trace:   print(array_give [Int](b . ref , 0)) ;
            Output: ----->   10
            Output: Trace:   array_give [Int](b . give , 1) ;
            Output: Trace: exit Main.main => 20
            Result: Ok: 20
            Alloc 0x19: [Int(20)]"#]]
    );
    // ANCHOR_END: interp_array_shared_refcount
}

#[test]
fn interp_array_given_move() {
    // ANCHOR: interp_array_given_move
    crate::assert_interpret_only!(
        {
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Int](2);
                    array_write[Int](a.mut, 0, 10);
                    array_write[Int](a.mut, 1, 20);
                    let b = a.give;
                    array_give[Int](b.give, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Int](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, ⚡, ⚡ }
            Output: Trace:   array_write [Int](a . mut , 0 , 10) ;
            Output: Trace:   array_write [Int](a . mut , 1 , 20) ;
            Output: Trace:   let b = a . give ;
            Output: Trace:   b = Array { flag: Given, rc: 1, 10, 20 }
            Output: Trace:   array_give [Int](b . give , 0) ;
            Output: Trace: exit Main.main => 10
            Result: Ok: 10
            Alloc 0x12: [Int(10)]"#]]
    );
    // ANCHOR_END: interp_array_given_move
}

#[test]
fn interp_array_drop_frees() {
    // ANCHOR: interp_array_drop_frees
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Data](2);
                    array_write[Data](a.mut, 0, new Data(1));
                    array_write[Data](a.mut, 1, new Data(2));
                    a.drop;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let a = array_new [Data](2) ;
            Output: Trace:   a = Array { flag: Given, rc: 1, Data { x: ⚡ }, Data { x: ⚡ } }
            Output: Trace:   array_write [Data](a . mut , 0 , new Data (1)) ;
            Output: Trace:   array_write [Data](a . mut , 1 , new Data (2)) ;
            Output: Trace:   a . drop ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x11: [Int(0)]"#]]
    );
    // ANCHOR_END: interp_array_drop_frees
}
