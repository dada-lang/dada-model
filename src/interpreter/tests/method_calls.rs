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
            Result: 42
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
            Result: 99
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
            Result: 42
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
            Result: Data { flag: Given, x: 42 }
            Alloc 0x08: [Flags(Given), Int(42)]"#]]
    );
}

/// Method with ref self — reads an Int field through a borrow.
/// FIXME: neither type checker nor interpreter resolve generic perm methods yet
#[test]
#[ignore]
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
                    f.ref.peek();
                }
            }
        },
        expect_test::expect![""]
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
            Result: 30
            Alloc 0x13: [Int(30)]"#]]
    );
}

/// Method with shared self — called multiple times on shared receiver.
/// FIXME: neither type checker nor interpreter resolve generic perm methods yet
#[test]
#[ignore]
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
                    let a = s.give.get_x();
                    let b = s.give.get_x();
                    a.give + b.give;
                }
            }
        },
        expect_test::expect![""]
    );
}
