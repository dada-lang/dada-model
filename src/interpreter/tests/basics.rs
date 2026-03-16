#[test]
fn return_int() {
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    22;
                }
            }
        },
        expect_test::expect![[r#"
            Result: 22
            Alloc 0x02: [Int(22)]"#]]
    );
}

#[test]
fn return_object() {
    crate::assert_interpret!(
        {
            class Point {
                x: Int;
                y: Int;
            }
            class Main {
                fn main(given self) -> Point {
                    new Point(22, 44);
                }
            }
        },
        expect_test::expect![[r#"
            Result: Point { x: 22, y: 44 }
            Alloc 0x04: [Int(22), Int(44)]"#]]
    );
}

#[test]
fn give_and_return() {
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
            Result: Point { flag: Given, x: 22, y: 44 }
            Alloc 0x06: [Flags(Given), Int(22), Int(44)]"#]]
    );
}

#[test]
fn arithmetic() {
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
}

#[test]
fn method_call() {
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
}

#[test]
fn ref_creates_copy() {
    // After taking a ref, the original can still be given away.
    // The ref is an independent copy.
    crate::assert_interpret!(
        {
            class Data { }

            class Pair {
                a: Data;
                b: Data;
            }

            class Main {
                fn main(given self) -> Data {
                    let p = new Pair(new Data(), new Data());
                    let r = p.ref;
                    p.a.give;
                }
            }
        },
        expect_test::expect!["Result: Data {  }"]
    );
}

#[test]
fn if_then_else() {
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
}

#[test]
fn if_false_branch() {
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
}

#[test]
fn print_int() {
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    print(42);
                    print(1 + 2);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: 42
            Output: 3
            Result: 0
            Alloc 0x08: [Int(0)]"#]]
    );
}

#[test]
fn print_object() {
    crate::assert_interpret!(
        {
            class Point {
                x: Int;
                y: Int;
            }
            class Main {
                fn main(given self) -> Int {
                    let p = new Point(10, 20);
                    print(p.ref);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: ref [p] Point { x: 10, y: 20 }
            Result: 0
            Alloc 0x08: [Int(0)]"#]]
    );
}

#[test]
fn loop_body_value_is_freed() {
    // Regression test: the loop body may produce Outcome::Value on non-breaking
    // iterations. That value must be freed, not silently dropped.
    //
    // Loop structure:
    //   - Iter 1: else branch sets stop=1; last expr `new Point(1,2)` is the body value
    //             → without the fix this Point allocation would be leaked.
    //   - Iter 2: if-branch breaks; loop exits.
    //
    // With the fix applied, the heap contains only the final return value.
    // Uses assert_interpret_only! because the type checker lacks Loop/Break rules.
    crate::assert_interpret_only!(
        {
            class Point { x: Int; y: Int; }

            class Main {
                fn main(given self) -> Int {
                    let stop = 0;
                    loop {
                        {
                            if stop.give { break; } else { stop = 1; };
                            new Point(1, 2);
                        }
                    }
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Result: 0
            Alloc 0x10: [Int(0)]"#]]
    );
}
