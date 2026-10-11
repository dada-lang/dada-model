/// Tests for block-scoped variable drops.
///
/// Variables declared inside a block should be dropped when the block exits,
/// in reverse declaration order.

#[test]
fn block_scoped_drop() {
    // Variable declared in inner block is dropped when block exits,
    // before the outer block continues.
    crate::assert_interpret_only!(
        {
            class Data {
                x: Int;
                drop {
                    print(self.x.give);
                }
            }

            class Main {
                fn main(given self) -> Int {
                    {
                        let d: given Data = new Data(42);
                        ();
                    };
                    99;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   { let _1_d : given Data = new Data (42) ; () ; } ;
            Output: Trace:   let _1_d : given Data = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   () ;
            Output: Trace:   drop Data
            Output: Trace:     print(self . x . give) ;
            Output: ----->     42
            Output: Trace:   99 ;
            Output: Trace: exit Main.main => 99
            Result: Ok: 99
            Alloc 0x0a: [Int(99)]"#]]
    );
}

#[test]
fn block_scoped_drop_order() {
    // Multiple variables in a block are dropped in reverse declaration order.
    crate::assert_interpret_only!(
        {
            class Data {
                x: Int;
                drop {
                    print(self.x.give);
                }
            }

            class Main {
                fn main(given self) -> Int {
                    {
                        let a: given Data = new Data(1);
                        let b: given Data = new Data(2);
                        let c: given Data = new Data(3);
                        ();
                    };
                    99;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   { let _1_a : given Data = new Data (1) ; let _1_b : given Data = new Data (2) ; let _1_c : given Data = new Data (3) ; () ; } ;
            Output: Trace:   let _1_a : given Data = new Data (1) ;
            Output: Trace:   _1_a = Data { x: 1 }
            Output: Trace:   let _1_b : given Data = new Data (2) ;
            Output: Trace:   _1_b = Data { x: 2 }
            Output: Trace:   let _1_c : given Data = new Data (3) ;
            Output: Trace:   _1_c = Data { x: 3 }
            Output: Trace:   () ;
            Output: Trace:   drop Data
            Output: Trace:     print(self . x . give) ;
            Output: ----->     3
            Output: Trace:   drop Data
            Output: Trace:     print(self . x . give) ;
            Output: ----->     2
            Output: Trace:   drop Data
            Output: Trace:     print(self . x . give) ;
            Output: ----->     1
            Output: Trace:   99 ;
            Output: Trace: exit Main.main => 99
            Result: Ok: 99
            Alloc 0x16: [Int(99)]"#]]
    );
}

#[test]
fn nested_blocks_drop_innermost_first() {
    // Inner block vars drop before outer block continues.
    crate::assert_interpret_only!(
        {
            class Data {
                x: Int;
                drop {
                    print(self.x.give);
                }
            }

            class Main {
                fn main(given self) -> Int {
                    let outer: given Data = new Data(1);
                    {
                        let inner: given Data = new Data(2);
                        ();
                    };
                    99;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_outer : given Data = new Data (1) ;
            Output: Trace:   _1_outer = Data { x: 1 }
            Output: Trace:   { let _1_inner : given Data = new Data (2) ; () ; } ;
            Output: Trace:   let _1_inner : given Data = new Data (2) ;
            Output: Trace:   _1_inner = Data { x: 2 }
            Output: Trace:   () ;
            Output: Trace:   drop Data
            Output: Trace:     print(self . x . give) ;
            Output: ----->     2
            Output: Trace:   99 ;
            Output: Trace:   drop Data
            Output: Trace:     print(self . x . give) ;
            Output: ----->     1
            Output: Trace: exit Main.main => 99
            Result: Ok: 99
            Alloc 0x0d: [Int(99)]"#]]
    );
}

#[test]
fn block_early_break_drops_locals() {
    // `break` inside a loop drops block-local vars declared before the break.
    crate::assert_interpret_only!(
        {
            class Data {
                x: Int;
                drop {
                    print(self.x.give);
                }
            }

            class Main {
                fn main(given self) -> Int {
                    loop {
                        let d: given Data = new Data(42);
                        break;
                    }
                    99;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   loop { let _1_d : given Data = new Data (42) ; break ; }
            Output: Trace:   let _1_d : given Data = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   break ;
            Output: Trace:   drop Data
            Output: Trace:     print(self . x . give) ;
            Output: ----->     42
            Output: Trace:   99 ;
            Output: Trace: exit Main.main => 99
            Result: Ok: 99
            Alloc 0x0a: [Int(99)]"#]]
    );
}

#[test]
fn partial_move_in_block_skips_drop_body() {
    // A partially-moved variable at block exit is NOT whole, so its
    // drop body must NOT run. Uses Array (a move type) so the give
    // actually consumes the source field, making the Pair non-whole.
    crate::assert_interpret_only!(
        {
            given class Pair {
                a: Array[Int];
                b: Array[Int];

                drop {
                    print(99);
                }
            }

            class Main {
                fn main(given self) -> () {
                    {
                        let p: given Pair = new Pair(array_new[Int](1), array_new[Int](1));
                        let moved_a = p.a.give;
                        ();
                    };
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   { let _1_p : given Pair = new Pair (array_new [Int](1), array_new [Int](1)) ; let _1_moved_a = _1_p . a . give ; () ; } ;
            Output: Trace:   let _1_p : given Pair = new Pair (array_new [Int](1), array_new [Int](1)) ;
            Output: Trace:   _1_p = Pair { a: Array { flag: Given, rc: 1, ⚡ }, b: Array { flag: Given, rc: 1, ⚡ } }
            Output: Trace:   let _1_moved_a = _1_p . a . give ;
            Output: Trace:   _1_moved_a = Array { flag: Given, rc: 1, ⚡ }
            Output: Trace:   () ;
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

#[test]
fn loop_break_drops_locals() {
    // Variables declared in a loop body are dropped on each iteration
    // and on break.
    crate::assert_interpret_only!(
        {
            class Data {
                x: Int;
                drop {
                    print(self.x.give);
                }
            }

            class Main {
                fn main(given self) -> Int {
                    let stop = 0;
                    loop {
                        let d: given Data = new Data(stop.give);
                        if stop.give >= 1 { break; } else { stop = 1; };
                    }
                    99;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_stop = 0 ;
            Output: Trace:   _1_stop = 0
            Output: Trace:   loop { let _1_d : given Data = new Data (_1_stop . give) ; if _1_stop . give >= 1 { break ; } else { _1_stop = 1 ; } ; }
            Output: Trace:   let _1_d : given Data = new Data (_1_stop . give) ;
            Output: Trace:   _1_d = Data { x: 0 }
            Output: Trace:   if _1_stop . give >= 1 { break ; } else { _1_stop = 1 ; } ;
            Output: Trace:   _1_stop = 1 ;
            Output: Trace:   _1_stop = 1
            Output: Trace:   drop Data
            Output: Trace:     print(self . x . give) ;
            Output: ----->     0
            Output: Trace:   let _1_d : given Data = new Data (_1_stop . give) ;
            Output: Trace:   _1_d = Data { x: 1 }
            Output: Trace:   if _1_stop . give >= 1 { break ; } else { _1_stop = 1 ; } ;
            Output: Trace:   break ;
            Output: Trace:   drop Data
            Output: Trace:     print(self . x . give) ;
            Output: ----->     1
            Output: Trace:   99 ;
            Output: Trace: exit Main.main => 99
            Result: Ok: 99
            Alloc 0x1d: [Int(99)]"#]]
    );
}
