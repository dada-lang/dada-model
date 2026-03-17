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
            Result: Point { x: 22, y: 44 }
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
            Result: 30
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
            Result: 7
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
            Result: Data { x: 42 }
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
            Output: shared Data { x: 42 }
            Result: shared Data { x: 42 }
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
            Output: ref [d] Data { x: 42 }
            Result: Data { x: 42 }
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
            Result: shared Data { x: 42 }
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
            Result: shared Outer { inner: Inner { x: 1 } }
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
            Result: ref [d] Data { x: 42 }
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
            Result: 42
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
            Result: 99
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
                    let a = array_new[Int](3).share;
                    array_set[Int](a.give, 0, 10);
                    array_set[Int](a.give, 1, 20);
                    array_set[Int](a.give, 2, 30);
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
            Alloc 0x1f: [Int(30)]"#]]
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
                    let a = array_new[Data](2).share;
                    array_set[Data](a.give, 0, new Data(42));
                    array_set[Data](a.give, 1, new Data(99));
                    print(array_give[Data](a.give, 0));
                    array_give[Data](a.give, 1);
                }
            }
        },
        expect_test::expect![[r#"
            Output: shared Data { x: 42 }
            Result: shared Data { x: 99 }
            Alloc 0x18: [Int(99)]"#]]
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
                    let a = array_new[Int](1).share;
                    array_set[Int](a.give, 0, 42);
                    let x = array_give[Int](a.give, 0);
                    let y = array_give[Int](a.give, 0);
                    print(x.give);
                    y.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: 42
            Result: 42
            Alloc 0x15: [Int(42)]"#]]
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
                    let a = array_new[Data](1).share;
                    array_set[Data](a.give, 0, new Data(42));
                    let x = array_give[Data](a.give, 0);
                    print(x.give);
                    // Element still available — shared, no move.
                    array_give[Data](a.give, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Output: shared Data { x: 42 }
            Result: shared Data { x: 42 }
            Alloc 0x14: [Int(42)]"#]]
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
                    let a = array_new[Int](2).share;
                    array_set[Int](a.give, 0, 10);
                    array_set[Int](a.give, 1, 20);
                    let b = a.give;
                    a.drop;
                    print(array_give[Int](b.give, 0));
                    array_give[Int](b.give, 1);
                }
            }
        },
        expect_test::expect![[r#"
            Output: 10
            Result: 20
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
                    array_set[Int](a.ref, 0, 10);
                    array_set[Int](a.ref, 1, 20);
                    let b = a.give;
                    array_give[Int](b.give, 0);
                }
            }
        },
        expect_test::expect![[r#"
            Result: 10
            Alloc 0x14: [Int(10)]"#]]
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
                    let a = array_new[Data](2).share;
                    array_set[Data](a.give, 0, new Data(1));
                    array_set[Data](a.give, 1, new Data(2));
                    a.drop;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Result: 0
            Alloc 0x13: [Int(0)]"#]]
    );
    // ANCHOR_END: interp_array_drop_frees
}
