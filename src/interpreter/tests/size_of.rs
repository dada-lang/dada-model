#[test]
fn size_of_int() {
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    size_of[Int]();
                }
            }
        },
        expect_test::expect![[r#"
            Result: Ok: 1
            Alloc 0x02: [Int(1)]"#]]
    );
}

#[test]
fn size_of_class_with_fields() {
    // Point has 2 Int fields + 1 flags word = 3
    crate::assert_interpret!(
        {
            class Point {
                x: Int;
                y: Int;
            }
            class Main {
                fn main(given self) -> Int {
                    size_of[Point]();
                }
            }
        },
        expect_test::expect![[r#"
            Result: Ok: 2
            Alloc 0x02: [Int(2)]"#]]
    );
}

#[test]
fn size_of_struct_class() {
    // shared classes have no flags word: just 2 Int fields = 2
    crate::assert_interpret!(
        {
            shared class Pair {
                x: Int;
                y: Int;
            }
            class Main {
                fn main(given self) -> Int {
                    size_of[Pair]();
                }
            }
        },
        expect_test::expect![[r#"
            Result: Ok: 2
            Alloc 0x02: [Int(2)]"#]]
    );
}

#[test]
fn size_of_empty_class() {
    // Empty class with just a flags word = 1
    crate::assert_interpret!(
        {
            class Empty { }
            class Main {
                fn main(given self) -> Int {
                    size_of[Empty]();
                }
            }
        },
        expect_test::expect![[r#"
            Result: Ok: 0
            Alloc 0x02: [Int(0)]"#]]
    );
}

#[test]
fn size_of_nested_class() {
    // Inner: 1 (flags) + 1 (Int) = 2
    // Outer: 1 (flags) + 2 (Inner) = 3
    crate::assert_interpret!(
        {
            class Inner {
                val: Int;
            }
            class Outer {
                inner: Inner;
            }
            class Main {
                fn main(given self) -> Int {
                    size_of[Outer]();
                }
            }
        },
        expect_test::expect![[r#"
            Result: Ok: 1
            Alloc 0x02: [Int(1)]"#]]
    );
}

#[test]
fn size_of_in_arithmetic() {
    // Can use size_of in expressions
    crate::assert_interpret!(
        {
            class Point {
                x: Int;
                y: Int;
            }
            class Main {
                fn main(given self) -> Int {
                    size_of[Point]() + size_of[Int]();
                }
            }
        },
        expect_test::expect![[r#"
            Result: Ok: 3
            Alloc 0x04: [Int(3)]"#]]
    );
}
