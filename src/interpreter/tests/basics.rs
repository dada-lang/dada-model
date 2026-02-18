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
        return "22"
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
        return "Point { flag: Owned, x: 22, y: 44 }"
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
        return "Point { flag: Owned, x: 22, y: 44 }"
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
        return "30"
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
        return "7"
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
        return "Data { flag: Owned }"
    );
}

#[test]
fn if_then_else() {
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    let result = 0;
                    if 1 { result = 42; } else { result = 0; };
                    result.give;
                }
            }
        },
        return "42"
    );
}

#[test]
fn if_false_branch() {
    crate::assert_interpret!(
        {
            class Main {
                fn main(given self) -> Int {
                    let result = 0;
                    if 0 { result = 42; } else { result = 99; };
                    result.give;
                }
            }
        },
        return "99"
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
        print "42",
        print "3",
        return "0"
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
        print "Point { flag: Ref, x: 10, y: 20 }",
        return "0"
    );
}
