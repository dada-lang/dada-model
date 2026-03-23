// Method call tests for the interpreter.
// Build up from the simplest case to exercise call_method thoroughly.

/// Simplest method call: given self, no args, returns Int.
#[test]
fn method_returns_int() {
    crate::assert_interpret!(
        {
            class Foo {
                fn get(given self) -> Int {
                    42;
                }
            }
            class Main {
                fn main(given self) -> Int {
                    let f = new Foo();
                    f.give.get();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_f = new Foo () ;
            Output: Trace:   _1_f = Foo {  }
            Output: Trace:   _1_f . give . get () ;
            Output: Trace:   enter Foo.get
            Output: Trace:     42 ;
            Output: Trace:   exit Foo.get => 42
            Output: Trace: exit Main.main => 42
            Result: Ok: 42
            Alloc 0x06: [Int(42)]"#]]
    );
}

/// Method that takes an argument and returns it.
#[test]
fn method_with_arg() {
    crate::assert_interpret!(
        {
            class Foo {
                fn identity(given self, x: Int) -> Int {
                    x.give;
                }
            }
            class Main {
                fn main(given self) -> Int {
                    let f = new Foo();
                    f.give.identity(99);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_f = new Foo () ;
            Output: Trace:   _1_f = Foo {  }
            Output: Trace:   _1_f . give . identity (99) ;
            Output: Trace:   enter Foo.identity
            Output: Trace:     _2_x . give ;
            Output: Trace:   exit Foo.identity => 99
            Output: Trace: exit Main.main => 99
            Result: Ok: 99
            Alloc 0x07: [Int(99)]"#]]
    );
}

/// Method that reads a field from self.
#[test]
fn method_reads_field() {
    crate::assert_interpret!(
        {
            class Foo {
                x: Int;
                fn get_x(given self) -> Int {
                    self.x.give;
                }
            }
            class Main {
                fn main(given self) -> Int {
                    let f = new Foo(42);
                    f.give.get_x();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_f = new Foo (42) ;
            Output: Trace:   _1_f = Foo { x: 42 }
            Output: Trace:   _1_f . give . get_x () ;
            Output: Trace:   enter Foo.get_x
            Output: Trace:     _2_self . x . give ;
            Output: Trace:   exit Foo.get_x => 42
            Output: Trace: exit Main.main => 42
            Result: Ok: 42
            Alloc 0x07: [Int(42)]"#]]
    );
}

/// Method that returns a non-copy field from self.
#[test]
fn method_gives_field() {
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Wrapper {
                inner: Data;
                fn take_inner(given self) -> Data {
                    self.inner.give;
                }
            }
            class Main {
                fn main(given self) -> Data {
                    let w = new Wrapper(new Data(42));
                    w.give.take_inner();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_w = new Wrapper (new Data (42)) ;
            Output: Trace:   _1_w = Wrapper { inner: Data { x: 42 } }
            Output: Trace:   _1_w . give . take_inner () ;
            Output: Trace:   enter Wrapper.take_inner
            Output: Trace:     _2_self . inner . give ;
            Output: Trace:   exit Wrapper.take_inner => Data { x: 42 }
            Output: Trace: exit Main.main => Data { x: 42 }
            Result: Ok: Data { x: 42 }
            Alloc 0x08: [Int(42)]"#]]
    );
}

/// Method with ref self — reads an Int field through a borrow.
#[test]
fn method_ref_self() {
    crate::assert_interpret!(
        {
            class Foo {
                x: Int;
                fn peek[perm P](P self) -> P Int {
                    self.x.give;
                }
            }
            class Main {
                fn main(given self) -> Int {
                    let f = new Foo(10);
                    f.ref.peek[ref[f]]();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_f = new Foo (10) ;
            Output: Trace:   _1_f = Foo { x: 10 }
            Output: Trace:   _1_f . ref . peek [ref [_1_f]] () ;
            Output: Trace:   enter Foo.peek
            Output: Trace:     _2_self . x . give ;
            Output: Trace:   exit Foo.peek => 10
            Output: Trace: exit Main.main => 10
            Result: Ok: 10
            Alloc 0x07: [Int(10)]"#]]
    );
}

/// Chain of two method calls.
#[test]
fn chained_method_calls() {
    crate::assert_interpret!(
        {
            class Adder {
                val: Int;
                fn add(given self, n: Int) -> Adder {
                    new Adder(self.val.give + n.give);
                }
                fn result(given self) -> Int {
                    self.val.give;
                }
            }
            class Main {
                fn main(given self) -> Int {
                    let a = new Adder(0);
                    a.give.add(10).add(20).result();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = new Adder (0) ;
            Output: Trace:   _1_a = Adder { val: 0 }
            Output: Trace:   _1_a . give . add (10) . add (20) . result () ;
            Output: Trace:   enter Adder.add
            Output: Trace:     new Adder (_2_self . val . give + _2_n . give) ;
            Output: Trace:   exit Adder.add => Adder { val: 10 }
            Output: Trace:   enter Adder.add
            Output: Trace:     new Adder (_3_self . val . give + _3_n . give) ;
            Output: Trace:   exit Adder.add => Adder { val: 30 }
            Output: Trace:   enter Adder.result
            Output: Trace:     _4_self . val . give ;
            Output: Trace:   exit Adder.result => 30
            Output: Trace: exit Main.main => 30
            Result: Ok: 30
            Alloc 0x13: [Int(30)]"#]]
    );
}

/// Method with shared self — called multiple times on shared receiver.
#[test]
fn method_shared_self() {
    crate::assert_interpret!(
        {
            class Holder {
                x: Int;
                fn get_x[perm P](P self) -> P Int {
                    self.x.give;
                }
            }
            class Main {
                fn main(given self) -> Int {
                    let h = new Holder(77);
                    let s = h.give.share;
                    let a = s.give.get_x[shared]();
                    let b = s.give.get_x[shared]();
                    a.give + b.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_h = new Holder (77) ;
            Output: Trace:   _1_h = Holder { x: 77 }
            Output: Trace:   let _1_s = _1_h . give . share ;
            Output: Trace:   _1_s = shared Holder { x: 77 }
            Output: Trace:   let _1_a = _1_s . give . get_x [shared] () ;
            Output: Trace:   enter Holder.get_x
            Output: Trace:     _2_self . x . give ;
            Output: Trace:   exit Holder.get_x => 77
            Output: Trace:   _1_a = 77
            Output: Trace:   let _1_b = _1_s . give . get_x [shared] () ;
            Output: Trace:   enter Holder.get_x
            Output: Trace:     _3_self . x . give ;
            Output: Trace:   exit Holder.get_x => 77
            Output: Trace:   _1_b = 77
            Output: Trace:   _1_a . give + _1_b . give ;
            Output: Trace: exit Main.main => 154
            Result: Ok: 154
            Alloc 0x11: [Int(154)]"#]]
    );
}
