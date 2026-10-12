#[test]
fn return_int() {
    crate::assert_interpret!(
        {
            struct Main {
                fn main(self->) -> Int {
                    22;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   22 ;
            Output: Trace: exit Main.main => 22
            Result: Ok: 22
            Alloc 0x02: [Int(22)]"#]]
    );
}

#[test]
fn return_object() {
    crate::assert_interpret!(
        {
            struct Point {
                x: Int;
                y: Int;
            }
            struct Main {
                fn main(self->) -> Point {
                    new Point(22, 44);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   new Point (22, 44) ;
            Output: Trace: exit Main.main => Point { x: 22, y: 44 }
            Result: Ok: Point { x: 22, y: 44 }
            Alloc 0x04: [Int(22), Int(44)]"#]]
    );
}

#[test]
fn give_and_return() {
    crate::assert_interpret!(
        {
            struct Point {
                x: Int;
                y: Int;
            }
            struct Main {
                fn main(self->) -> Point {
                    let p = new Point(22, 44);
                    p->;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_p = new Point (22, 44) ;
            Output: Trace:   _1_p = Point { x: 22, y: 44 }
            Output: Trace:   _1_p -> ;
            Output: Trace: exit Main.main => Point { x: 22, y: 44 }
            Result: Ok: Point { x: 22, y: 44 }
            Alloc 0x06: [Int(22), Int(44)]"#]]
    );
}

#[test]
fn arithmetic() {
    crate::assert_interpret!(
        {
            struct Main {
                fn main(self->) -> Int {
                    let x = 10;
                    let y = 20;
                    x-> + y->;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_x = 10 ;
            Output: Trace:   _1_x = 10
            Output: Trace:   let _1_y = 20 ;
            Output: Trace:   _1_y = 20
            Output: Trace:   _1_x -> + _1_y -> ;
            Output: Trace: exit Main.main => 30
            Result: Ok: 30
            Alloc 0x08: [Int(30)]"#]]
    );
}

#[test]
fn method_call() {
    crate::assert_interpret!(
        {
            struct Adder {
                a: Int;
                b: Int;

                fn sum(self->) -> Int {
                    self.a-> + self.b->;
                }
            }

            struct Main {
                fn main(self->) -> Int {
                    let adder = new Adder(3, 4);
                    adder->.sum();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_adder = new Adder (3, 4) ;
            Output: Trace:   _1_adder = Adder { a: 3, b: 4 }
            Output: Trace:   _1_adder -> . sum () ;
            Output: Trace:   enter Adder.sum
            Output: Trace:     _2_self . a -> + _2_self . b -> ;
            Output: Trace:   exit Adder.sum => 7
            Output: Trace: exit Main.main => 7
            Result: Ok: 7
            Alloc 0x0a: [Int(7)]"#]]
    );
}

#[test]
fn ref_creates_copy() {
    // After taking a place sharing, the original can still be given away.
    // The place sharing is an independent copy.
    crate::assert_interpret!(
        {
            struct Data { }

            struct Pair {
                a: Data;
                b: Data;
            }

            struct Main {
                fn main(self->) -> Data {
                    let p = new Pair(new Data(), new Data());
                    let r = p.share;
                    p.a->;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_p = new Pair (new Data (), new Data ()) ;
            Output: Trace:   _1_p = Pair { a: Data {  }, b: Data {  } }
            Output: Trace:   let _1_r = _1_p . share ;
            Output: Trace:   _1_r = shared [_1_p] Pair { a: Data {  }, b: Data {  } }
            Output: Trace:   _1_p . a -> ;
            Output: Trace: exit Main.main => Data {  }
            Result: Ok: Data {  }"#]]
    );
}

#[test]
fn if_then_else() {
    crate::assert_interpret!(
        {
            struct Main {
                fn main(self->) -> Int {
                    let result = 0;
                    if true { result = 42; } else { result = 0; };
                    result->;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_result = 0 ;
            Output: Trace:   _1_result = 0
            Output: Trace:   if true { _1_result = 42 ; } else { _1_result = 0 ; } ;
            Output: Trace:   _1_result = 42 ;
            Output: Trace:   _1_result = 42
            Output: Trace:   _1_result -> ;
            Output: Trace: exit Main.main => 42
            Result: Ok: 42
            Alloc 0x08: [Int(42)]"#]]
    );
}

#[test]
fn if_false_branch() {
    crate::assert_interpret!(
        {
            struct Main {
                fn main(self->) -> Int {
                    let result = 0;
                    if false { result = 42; } else { result = 99; };
                    result->;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_result = 0 ;
            Output: Trace:   _1_result = 0
            Output: Trace:   if false { _1_result = 42 ; } else { _1_result = 99 ; } ;
            Output: Trace:   _1_result = 99 ;
            Output: Trace:   _1_result = 99
            Output: Trace:   _1_result -> ;
            Output: Trace: exit Main.main => 99
            Result: Ok: 99
            Alloc 0x08: [Int(99)]"#]]
    );
}

#[test]
fn print_int() {
    crate::assert_interpret!(
        {
            struct Main {
                fn main(self->) -> Int {
                    print(42);
                    print(1 + 2);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   print(42) ;
            Output: ----->   42
            Output: Trace:   print(1 + 2) ;
            Output: ----->   3
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x08: [Int(0)]"#]]
    );
}

#[test]
fn print_object() {
    crate::assert_interpret!(
        {
            struct Point {
                x: Int;
                y: Int;
            }
            struct Main {
                fn main(self->) -> Int {
                    let p = new Point(10, 20);
                    print(p.share);
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_p = new Point (10, 20) ;
            Output: Trace:   _1_p = Point { x: 10, y: 20 }
            Output: Trace:   print(_1_p . share) ;
            Output: ----->   shared [_1_p] Point { x: 10, y: 20 }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
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
            struct Point { x: Int; y: Int; }

            struct Main {
                fn main(self->) -> Int {
                    let stop = 0;
                    loop {
                        if stop-> >= 1 { break; } else { stop = 1; };
                        new Point(1, 2);
                    }
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_stop = 0 ;
            Output: Trace:   _1_stop = 0
            Output: Trace:   loop { if _1_stop -> >= 1 { break ; } else { _1_stop = 1 ; } ; new Point (1, 2) ; }
            Output: Trace:   if _1_stop -> >= 1 { break ; } else { _1_stop = 1 ; } ;
            Output: Trace:   _1_stop = 1 ;
            Output: Trace:   _1_stop = 1
            Output: Trace:   new Point (1, 2) ;
            Output: Trace:   if _1_stop -> >= 1 { break ; } else { _1_stop = 1 ; } ;
            Output: Trace:   break ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x14: [Int(0)]"#]]
    );
}
