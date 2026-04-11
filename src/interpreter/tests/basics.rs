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
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   22 ;
            Output: Trace: exit Main.main => 22
            Result: Ok: 22
            Alloc 0x02: [Int(22)]"#]])
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
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   new Point (22, 44) ;
            Output: Trace: exit Main.main => Point { x: 22, y: 44 }
            Result: Ok: Point { x: 22, y: 44 }
            Alloc 0x04: [Int(22), Int(44)]"#]])
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
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_p = new Point (22, 44) ;
            Output: Trace:   _1_p = Point { x: 22, y: 44 }
            Output: Trace:   _1_p . give ;
            Output: Trace: exit Main.main => Point { x: 22, y: 44 }
            Result: Ok: Point { x: 22, y: 44 }
            Alloc 0x06: [Int(22), Int(44)]"#]])
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
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_x = 10 ;
            Output: Trace:   _1_x = 10
            Output: Trace:   let _1_y = 20 ;
            Output: Trace:   _1_y = 20
            Output: Trace:   _1_x . give + _1_y . give ;
            Output: Trace: exit Main.main => 30
            Result: Ok: 30
            Alloc 0x08: [Int(30)]"#]])
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
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_adder = new Adder (3, 4) ;
            Output: Trace:   _1_adder = Adder { a: 3, b: 4 }
            Output: Trace:   _1_adder . give . sum () ;
            Output: Trace:   enter Adder.sum
            Output: Trace:     _2_self . a . give + _2_self . b . give ;
            Output: Trace:   exit Adder.sum => 7
            Output: Trace: exit Main.main => 7
            Result: Ok: 7
            Alloc 0x0a: [Int(7)]"#]])
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
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_p = new Pair (new Data (), new Data ()) ;
            Output: Trace:   _1_p = Pair { a: Data {  }, b: Data {  } }
            Output: Trace:   let _1_r = _1_p . ref ;
            Output: Trace:   _1_r = ref [_1_p] Pair { a: Data {  }, b: Data {  } }
            Output: Trace:   _1_p . a . give ;
            Output: Trace: exit Main.main => Data {  }
            Result: Ok: Data {  }"#]])
    );
}

#[test]
fn if_then_else() {
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    let result = 0;
                    if true { result = 42; } else { result = 0; };
                    result.give;
                }
            }
        },
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_result = 0 ;
            Output: Trace:   _1_result = 0
            Output: Trace:   if true { _1_result = 42 ; } else { _1_result = 0 ; } ;
            Output: Trace:   _1_result = 42 ;
            Output: Trace:   _1_result = 42
            Output: Trace:   _1_result . give ;
            Output: Trace: exit Main.main => 42
            Result: Ok: 42
            Alloc 0x08: [Int(42)]"#]])
    );
}

#[test]
fn if_false_branch() {
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    let result = 0;
                    if false { result = 42; } else { result = 99; };
                    result.give;
                }
            }
        },
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_result = 0 ;
            Output: Trace:   _1_result = 0
            Output: Trace:   if false { _1_result = 42 ; } else { _1_result = 99 ; } ;
            Output: Trace:   _1_result = 99 ;
            Output: Trace:   _1_result = 99
            Output: Trace:   _1_result . give ;
            Output: Trace: exit Main.main => 99
            Result: Ok: 99
            Alloc 0x08: [Int(99)]"#]])
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
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   print(42) ;
            Output: ----->   42
            Output: Trace:   print(1 + 2) ;
            Output: ----->   3
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x08: [Int(0)]"#]])
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
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_p = new Point (10, 20) ;
            Output: Trace:   _1_p = Point { x: 10, y: 20 }
            Output: Trace:   print(_1_p . ref) ;
            Output: ----->   ref [_1_p] Point { x: 10, y: 20 }
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x08: [Int(0)]"#]])
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
    crate::assert_interpret!(
        {
            class Point { x: Int; y: Int; }

            class Main {
                fn main(given self) -> Int {
                    let stop = 0;
                    loop {
                        if stop.give >= 1 { break; } else { stop = 1; };
                        new Point(1, 2);
                    }
                    0;
                }
            }
        },
        type: error(expect_test::expect![[r#"src/type_system/statements.rs:57:1: no applicable rules for type_statement { statement: loop { if stop . give >= 1 { break ; } else { stop = 1 ; } ; new Point (1, 2) ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, stop: Int}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }"#]]), interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_stop = 0 ;
            Output: Trace:   _1_stop = 0
            Output: Trace:   loop { if _1_stop . give >= 1 { break ; } else { _1_stop = 1 ; } ; new Point (1, 2) ; }
            Output: Trace:   if _1_stop . give >= 1 { break ; } else { _1_stop = 1 ; } ;
            Output: Trace:   _1_stop = 1 ;
            Output: Trace:   _1_stop = 1
            Output: Trace:   new Point (1, 2) ;
            Output: Trace:   if _1_stop . give >= 1 { break ; } else { _1_stop = 1 ; } ;
            Output: Trace:   break ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x14: [Int(0)]"#]])
    );
}
