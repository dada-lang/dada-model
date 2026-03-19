#[test]
fn generic_struct_copy_param() {
    // A shared class with a copy type parameter is itself copy.
    // Box[Int] should have flag: Shared and be giveable twice.
    crate::assert_interpret!(
        {
            shared class Box[ty T] {
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
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let b : Box[Int] = new Box [Int] (42) ;
            Output: Trace:   b = Box { value: 42 }
            Output: Trace:   let a = b . give ;
            Output: Trace:   a = Box { value: 42 }
            Output: Trace:   b . give ;
            Output: Trace: exit Main.main => Box { value: 42 }
            Result: Ok: Box { value: 42 }
            Alloc 0x07: [Int(42)]"#]]
    );
}

#[test]
fn generic_struct_move_param() {
    // A shared class with a move type parameter is itself move.
    // Box[Data] should have flag: Given and be consumed on give.
    crate::assert_interpret!(
        {
            class Data {
                x: Int;
            }
            shared class Box[ty T] {
                value: T;
            }
            class Main {
                fn main(given self) -> Box[Data] {
                    let b: Box[Data] = new Box[Data](new Data(1));
                    b.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let b : Box[Data] = new Box [Data] (new Data (1)) ;
            Output: Trace:   b = Box { value: Data { x: 1 } }
            Output: Trace:   b . give ;
            Output: Trace: exit Main.main => Box { value: Data { x: 1 } }
            Result: Ok: Box { value: Data { x: 1 } }
            Alloc 0x06: [Int(1)]"#]]
    );
}

#[test]
fn generic_method_dispatch() {
    // A generic class with a method that operates on the type parameter.
    // Monomorphization substitutes Int for T in the method body.
    crate::assert_interpret!(
        {
            shared class Box[ty T] {
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
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let b : Box[Int] = new Box [Int] (42) ;
            Output: Trace:   b = Box { value: 42 }
            Output: Trace:   b . give . get () ;
            Output: Trace:   enter Box.get
            Output: Trace:     self . value . give ;
            Output: Trace:   exit Box.get => 42
            Output: Trace: exit Main.main => 42
            Result: Ok: 42
            Alloc 0x07: [Int(42)]"#]]
    );
}

#[test]
fn struct_pair_of_ints_is_copy() {
    // Pair[Int] — shared class with copy param — is copy.
    // Give it twice, both succeed.
    crate::assert_interpret!(
        {
            shared class Pair[ty T] {
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
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let p : Pair[Int] = new Pair [Int] (1, 2) ;
            Output: Trace:   p = Pair { a: 1, b: 2 }
            Output: Trace:   let c = p . give ;
            Output: Trace:   c = Pair { a: 1, b: 2 }
            Output: Trace:   p . give ;
            Output: Trace: exit Main.main => Pair { a: 1, b: 2 }
            Result: Ok: Pair { a: 1, b: 2 }
            Alloc 0x08: [Int(1), Int(2)]"#]]
    );
}

#[test]
fn nested_struct_move_poisons() {
    // Pair[Data] — Data is move, so Pair[Data] is also move
    // even though Pair itself is a shared class.
    crate::assert_interpret!(
        {
            class Data {
                x: Int;
            }
            shared class Pair[ty T] {
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
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let p : Pair[Data] = new Pair [Data] (new Data (1), new Data (2)) ;
            Output: Trace:   p = Pair { a: Data { x: 1 }, b: Data { x: 2 } }
            Output: Trace:   p . give ;
            Output: Trace: exit Main.main => Pair { a: Data { x: 1 }, b: Data { x: 2 } }
            Result: Ok: Pair { a: Data { x: 1 }, b: Data { x: 2 } }
            Alloc 0x08: [Int(1), Int(2)]"#]]
    );
}

#[test]
fn struct_move_param_give_consumes() {
    // A shared class Box[Data] is move because Data is move.
    // Giving it transfers ownership — the result has flag: Given.
    crate::assert_interpret!(
        {
            class Data {
                x: Int;
            }
            shared class Box[ty T] {
                value: T;
            }
            class Main {
                fn main(given self) -> Box[Data] {
                    let b: Box[Data] = new Box[Data](new Data(99));
                    b.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let b : Box[Data] = new Box [Data] (new Data (99)) ;
            Output: Trace:   b = Box { value: Data { x: 99 } }
            Output: Trace:   b . give ;
            Output: Trace: exit Main.main => Box { value: Data { x: 99 } }
            Result: Ok: Box { value: Data { x: 99 } }
            Alloc 0x06: [Int(99)]"#]]
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
            shared class Box[ty T] {
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
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let b : Box[Data] = new Box [Data] (new Data (99)) ;
            Output: Trace:   b = Box { value: Data { x: 99 } }
            Output: Trace:   let c = b . give ;
            Output: Trace:   c = Box { value: Data { x: 99 } }
            Output: Trace:   b . give ;
            Result: Fault: access of uninitialized value
            Alloc 0x06: [Int(99)]"#]]
    );
}

#[test]
fn struct_move_param_ref_borrows() {
    // A shared class Box[Data] is move — taking a ref should produce
    // a copy with flag: Borrowed, leaving original usable.
    crate::assert_interpret!(
        {
            class Data {
                x: Int;
            }
            shared class Box[ty T] {
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
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let b : Box[Data] = new Box [Data] (new Data (42)) ;
            Output: Trace:   b = Box { value: Data { x: 42 } }
            Output: Trace:   print(b . ref) ;
            Output: ----->   ref [b] Box { value: Data { x: 42 } }
            Output: Trace:   b . give ;
            Output: Trace: exit Main.main => Box { value: Data { x: 42 } }
            Result: Ok: Box { value: Data { x: 42 } }
            Alloc 0x08: [Int(42)]"#]]
    );
}
