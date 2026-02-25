#[test]
fn generic_struct_copy_param() {
    // A struct class with a copy type parameter is itself copy.
    // Box[Int] should have flag: Shared and be giveable twice.
    crate::assert_interpret!(
        {
            struct class Box[ty T] {
                value: T;
            }
            class Main {
                fn main(given self) -> Box[Int] {
                    let b: Box[Int] = new Box[Int](42);
                    let a = b.give;
                    b.give;
                }
            }
        },
        return "Box { value: 42 }"
    );
}

#[test]
fn generic_struct_move_param() {
    // A struct class with a move type parameter is itself move.
    // Box[Data] should have flag: Given and be consumed on give.
    crate::assert_interpret!(
        {
            class Data {
                x: Int;
            }
            struct class Box[ty T] {
                value: T;
            }
            class Main {
                fn main(given self) -> Box[Data] {
                    let b: Box[Data] = new Box[Data](new Data(1));
                    b.give;
                }
            }
        },
        return "Box { flag: Given, value: Data { flag: Given, x: 1 } }"
    );
}

#[test]
fn generic_method_dispatch() {
    // A generic class with a method that operates on the type parameter.
    // Monomorphization substitutes Int for T in the method body.
    crate::assert_interpret!(
        {
            struct class Box[ty T] {
                value: T;

                fn get(given self) -> T {
                    self.value.give;
                }
            }
            class Main {
                fn main(given self) -> Int {
                    let b: Box[Int] = new Box[Int](42);
                    b.give.get();
                }
            }
        },
        return "42"
    );
}

#[test]
fn struct_pair_of_ints_is_copy() {
    // Pair[Int] — struct with copy param — is copy.
    // Give it twice, both succeed.
    crate::assert_interpret!(
        {
            struct class Pair[ty T] {
                a: T;
                b: T;
            }
            class Main {
                fn main(given self) -> Pair[Int] {
                    let p: Pair[Int] = new Pair[Int](1, 2);
                    let c = p.give;
                    p.give;
                }
            }
        },
        return "Pair { a: 1, b: 2 }"
    );
}

#[test]
fn nested_struct_move_poisons() {
    // Pair[Data] — Data is move, so Pair[Data] is also move
    // even though Pair itself is a struct class.
    crate::assert_interpret!(
        {
            class Data {
                x: Int;
            }
            struct class Pair[ty T] {
                a: T;
                b: T;
            }
            class Main {
                fn main(given self) -> Pair[Data] {
                    let p: Pair[Data] = new Pair[Data](new Data(1), new Data(2));
                    p.give;
                }
            }
        },
        return "Pair { flag: Given, a: Data { flag: Given, x: 1 }, b: Data { flag: Given, x: 2 } }"
    );
}

#[test]
fn struct_move_param_give_consumes() {
    // A struct class Box[Data] is move because Data is move.
    // Giving it transfers ownership — the result has flag: Given.
    crate::assert_interpret!(
        {
            class Data {
                x: Int;
            }
            struct class Box[ty T] {
                value: T;
            }
            class Main {
                fn main(given self) -> Box[Data] {
                    let b: Box[Data] = new Box[Data](new Data(99));
                    b.give;
                }
            }
        },
        return "Box { flag: Given, value: Data { flag: Given, x: 99 } }"
    );
}

#[test]
fn struct_move_param_give_twice_faults() {
    // Box[Data] is move — giving it twice faults at runtime.
    crate::assert_interpret_fault!(
        {
            class Data {
                x: Int;
            }
            struct class Box[ty T] {
                value: T;
            }
            class Main {
                fn main(given self) -> Box[Data] {
                    let b: Box[Data] = new Box[Data](new Data(99));
                    let c = b.give;
                    b.give;
                }
            }
        },
        "give of uninitialized value"
    );
}

#[test]
fn struct_move_param_ref_borrows() {
    // A struct class Box[Data] is move — taking a ref should produce
    // a copy with flag: Borrowed, leaving original usable.
    crate::assert_interpret!(
        {
            class Data {
                x: Int;
            }
            struct class Box[ty T] {
                value: T;
            }
            class Main {
                fn main(given self) -> Box[Data] {
                    let b: Box[Data] = new Box[Data](new Data(42));
                    print(b.ref);
                    b.give;
                }
            }
        },
        print "Box { flag: Borrowed, value: Data { flag: Given, x: 42 } }",
        return "Box { flag: Given, value: Data { flag: Given, x: 42 } }"
    );
}
