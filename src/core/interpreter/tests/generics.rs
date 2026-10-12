#[test]
fn generic_struct_copy_param() {
    // A shared struct with a copy type parameter is itself copy.
    // Box[Int] should have flag: Shared and be giveable twice.
    crate::assert_interpret!(
        {
            shared struct Box[ty T] {
                value: T;
            }
            struct Main {
                fn main(given self) -> Box[Int] {
                    let b: Box[Int] = new Box[Int](42);
                    let a = b^;
                    b^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_b : Box[Int] = new Box [Int] (42) ;
            Output: Trace:   _1_b = Box { value: 42 }
            Output: Trace:   let _1_a = _1_b ^ ;
            Output: Trace:   _1_a = Box { value: 42 }
            Output: Trace:   _1_b ^ ;
            Output: Trace: exit Main.main => Box { value: 42 }
            Result: Ok: Box { value: 42 }
            Alloc 0x07: [Int(42)]"#]]
    );
}

#[test]
fn generic_struct_move_param() {
    // A shared struct with a unique type parameter is itself unique.
    // Box[Data] should have flag: Given and be consumed on give.
    crate::assert_interpret!(
        {
            struct Data {
                x: Int;
            }
            shared struct Box[ty T] {
                value: T;
            }
            struct Main {
                fn main(given self) -> Box[Data] {
                    let b: Box[Data] = new Box[Data](new Data(1));
                    b^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_b : Box[Data] = new Box [Data] (new Data (1)) ;
            Output: Trace:   _1_b = Box { value: Data { x: 1 } }
            Output: Trace:   _1_b ^ ;
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
            shared struct Box[ty T] {
                value: T;

                fn get(given self) -> T {
                    self.value^;
                }
            }
            struct Main {
                fn main(given self) -> Int {
                    let b: Box[Int] = new Box[Int](42);
                    b^.get();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_b : Box[Int] = new Box [Int] (42) ;
            Output: Trace:   _1_b = Box { value: 42 }
            Output: Trace:   _1_b ^ . get () ;
            Output: Trace:   enter Box.get
            Output: Trace:     _2_self . value ^ ;
            Output: Trace:   exit Box.get => 42
            Output: Trace: exit Main.main => 42
            Result: Ok: 42
            Alloc 0x07: [Int(42)]"#]]
    );
}

#[test]
fn struct_pair_of_ints_is_copy() {
    // Pair[Int] — shared struct with copy param — is shared.
    // Give it twice, both succeed.
    crate::assert_interpret!(
        {
            shared struct Pair[ty T] {
                a: T;
                b: T;
            }
            struct Main {
                fn main(given self) -> Pair[Int] {
                    let p: Pair[Int] = new Pair[Int](1, 2);
                    let c = p^;
                    p^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_p : Pair[Int] = new Pair [Int] (1, 2) ;
            Output: Trace:   _1_p = Pair { a: 1, b: 2 }
            Output: Trace:   let _1_c = _1_p ^ ;
            Output: Trace:   _1_c = Pair { a: 1, b: 2 }
            Output: Trace:   _1_p ^ ;
            Output: Trace: exit Main.main => Pair { a: 1, b: 2 }
            Result: Ok: Pair { a: 1, b: 2 }
            Alloc 0x08: [Int(1), Int(2)]"#]]
    );
}

#[test]
fn nested_struct_move_poisons() {
    // Pair[Data] — Data is unique, so Pair[Data] is also move
    // even though Pair itself is a shared struct.
    crate::assert_interpret!(
        {
            struct Data {
                x: Int;
            }
            shared struct Pair[ty T] {
                a: T;
                b: T;
            }
            struct Main {
                fn main(given self) -> Pair[Data] {
                    let p: Pair[Data] = new Pair[Data](new Data(1), new Data(2));
                    p^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_p : Pair[Data] = new Pair [Data] (new Data (1), new Data (2)) ;
            Output: Trace:   _1_p = Pair { a: Data { x: 1 }, b: Data { x: 2 } }
            Output: Trace:   _1_p ^ ;
            Output: Trace: exit Main.main => Pair { a: Data { x: 1 }, b: Data { x: 2 } }
            Result: Ok: Pair { a: Data { x: 1 }, b: Data { x: 2 } }
            Alloc 0x08: [Int(1), Int(2)]"#]]
    );
}

#[test]
fn struct_move_param_give_consumes() {
    // A shared struct Box[Data] is unique because Data is unique.
    // Giving it transfers ownership — the result has flag: Given.
    crate::assert_interpret!(
        {
            struct Data {
                x: Int;
            }
            shared struct Box[ty T] {
                value: T;
            }
            struct Main {
                fn main(given self) -> Box[Data] {
                    let b: Box[Data] = new Box[Data](new Data(99));
                    b^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_b : Box[Data] = new Box [Data] (new Data (99)) ;
            Output: Trace:   _1_b = Box { value: Data { x: 99 } }
            Output: Trace:   _1_b ^ ;
            Output: Trace: exit Main.main => Box { value: Data { x: 99 } }
            Result: Ok: Box { value: Data { x: 99 } }
            Alloc 0x06: [Int(99)]"#]]
    );
}

#[test]
fn struct_move_param_give_twice_faults() {
    // Box[Data] is unique — giving it twice faults at runtime.
    crate::assert_interpret_fault!(
        {
            struct Data {
                x: Int;
            }
            shared struct Box[ty T] {
                value: T;
            }
            struct Main {
                fn main(given self) -> Box[Data] {
                    let b: Box[Data] = new Box[Data](new Data(99));
                    let c = b^;
                    b^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_b : Box[Data] = new Box [Data] (new Data (99)) ;
            Output: Trace:   _1_b = Box { value: Data { x: 99 } }
            Output: Trace:   let _1_c = _1_b ^ ;
            Output: Trace:   _1_c = Box { value: Data { x: 99 } }
            Output: Trace:   _1_b ^ ;
            Result: Fault: access of uninitialized value
            Alloc 0x06: [Int(99)]"#]]
    );
}

#[test]
fn struct_move_param_ref_borrows() {
    // A shared struct Box[Data] is unique — taking a place sharing should produce
    // a copy with flag: SharedPlace, leaving original usable.
    crate::assert_interpret!(
        {
            struct Data {
                x: Int;
            }
            shared struct Box[ty T] {
                value: T;
            }
            struct Main {
                fn main(given self) -> Box[Data] {
                    let b: Box[Data] = new Box[Data](new Data(42));
                    print(b.share);
                    b^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_b : Box[Data] = new Box [Data] (new Data (42)) ;
            Output: Trace:   _1_b = Box { value: Data { x: 42 } }
            Output: Trace:   print(_1_b . share) ;
            Output: ----->   shared [_1_b] Box { value: Data { x: 42 } }
            Output: Trace:   _1_b ^ ;
            Output: Trace: exit Main.main => Box { value: Data { x: 42 } }
            Result: Ok: Box { value: Data { x: 42 } }
            Alloc 0x08: [Int(42)]"#]]
    );
}
