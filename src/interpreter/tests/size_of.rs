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
        return "1"
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
        return "3"
    );
}

#[test]
fn size_of_struct_class() {
    // struct (shared) classes have no flags word: just 2 Int fields = 2
    crate::assert_interpret!(
        {
            struct class Pair {
                x: Int;
                y: Int;
            }
            class Main {
                fn main(given self) -> Int {
                    size_of[Pair]();
                }
            }
        },
        return "2"
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
        return "1"
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
        return "3"
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
        return "4"
    );
}
