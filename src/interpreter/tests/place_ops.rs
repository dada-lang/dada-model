// Tests for flags-dependent place operations: give, ref, mut, drop.
//
// Per unsafe.md, each place operation examines the flags word
// of the source value to determine its behavior.
//
// Most tests use well-defined programs (no use-after-move/drop).
// A few UB tests (clearly marked) read dead values to verify
// uninitialize behavior — these bypass the type checker.

// ---------------------------------------------------------------
// give: flags-dependent behavior
// ---------------------------------------------------------------

#[test]
fn give_from_given() {
    // give from a Given source: copy fields, mark source Uninitialized.
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    d.give;
                }
            }
        },
        return "Data { flag: Given, x: 42 }"
    );
}

#[test]
fn give_from_given_uninitializes_source() {
    // UB test: verify that give from Given marks source Uninitialized.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    let a = d.give;
                    print(d.give);
                    a.give;
                }
            }
        },
        print "Data { flag: Uninitialized, x: 42 }",
        return "Data { flag: Given, x: 42 }"
    );
}

#[test]
fn give_from_shared() {
    // give from a Shared source: copy fields, set flags to Shared.
    // Shared values are copyable, so giving doesn't consume the source.
    // We print the give result and return the original — both are valid.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    let s = d.share;
                    print(s.give);
                    s.give;
                }
            }
        },
        print "Data { flag: Shared, x: 42 }",
        return "Data { flag: Shared, x: 42 }"
    );
}

#[test]
fn give_from_shared_nested() {
    // Giving a shared object with nested unique fields:
    // the copy should have all nested flags set to Shared
    // (the share operation is applied recursively).
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(given self) -> Outer {
                    let o = new Outer(new Inner(1));
                    let s = o.share;
                    s.give;
                }
            }
        },
        return "Outer { flag: Shared, inner: Inner { flag: Shared, x: 1 } }"
    );
}

#[test]
fn give_from_borrowed() {
    // give from a Borrowed source: copy fields, set flags to Borrowed.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    let r = d.ref;
                    r.give;
                }
            }
        },
        return "Data { flag: Borrowed, x: 42 }"
    );
}

#[test]
fn give_shared_multiple_times() {
    // A shared value is copyable — giving it repeatedly works,
    // each copy gets flag: Shared.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    let s = d.share;
                    let x1 = s.give;
                    let x2 = s.give;
                    print(x1.give);
                    print(x2.give);
                    s.give;
                }
            }
        },
        print "Data { flag: Shared, x: 42 }",
        print "Data { flag: Shared, x: 42 }",
        return "Data { flag: Shared, x: 42 }"
    );
}

#[test]
fn give_shared_nested_subfield() {
    // Share an Outer, then access its inner field via give.
    // The inner field should be Shared (share op recursed),
    // and therefore copyable — give it twice.
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(given self) -> Inner {
                    let o = new Outer(new Inner(99));
                    let s = o.share;
                    let i1 = s.inner.give;
                    let i2 = s.inner.give;
                    print(i1.give);
                    i2.give;
                }
            }
        },
        print "Inner { flag: Shared, x: 99 }",
        return "Inner { flag: Shared, x: 99 }"
    );
}

// ---------------------------------------------------------------
// ref: flags-dependent behavior
// ---------------------------------------------------------------

#[test]
fn ref_from_given() {
    // ref from a Given source: copy fields, set flags to Borrowed.
    // Source remains Given — print the ref, then return the original.
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    print(d.ref);
                    d.give;
                }
            }
        },
        print "Data { flag: Borrowed, x: 42 }",
        return "Data { flag: Given, x: 42 }"
    );
}

#[test]
fn ref_from_shared() {
    // ref from a Shared source: copy fields, set flags to Shared
    // (not Borrowed — shared stays shared).
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    let s = d.share;
                    s.ref;
                }
            }
        },
        return "Data { flag: Shared, x: 42 }"
    );
}

#[test]
fn ref_from_shared_nested() {
    // Ref from a shared object with nested fields:
    // result should have Shared flags throughout (not Borrowed).
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(given self) -> Outer {
                    let o = new Outer(new Inner(1));
                    let s = o.share;
                    s.ref;
                }
            }
        },
        return "Outer { flag: Shared, inner: Inner { flag: Shared, x: 1 } }"
    );
}

#[test]
fn ref_from_shared_nested_subfield() {
    // Ref a shared Outer, then give its inner field.
    // The inner was made Shared by the recursive share op,
    // so giving it produces a Shared copy — and it's repeatable.
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(given self) -> Inner {
                    let o = new Outer(new Inner(7));
                    let s = o.share;
                    let r = s.ref;
                    let i1 = r.inner.give;
                    let i2 = r.inner.give;
                    print(i1.give);
                    i2.give;
                }
            }
        },
        print "Inner { flag: Shared, x: 7 }",
        return "Inner { flag: Shared, x: 7 }"
    );
}

#[test]
fn ref_from_borrowed() {
    // ref from a Borrowed source: copy fields, set flags to Borrowed.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    let r = d.ref;
                    r.ref;
                }
            }
        },
        return "Data { flag: Borrowed, x: 42 }"
    );
}

// ---------------------------------------------------------------
// drop: flags-dependent behavior
// ---------------------------------------------------------------

#[test]
fn drop_given() {
    // drop on a Given value: print it first, then drop.
    // The drop itself shouldn't fault.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Int {
                    let d = new Data(42);
                    print(d.ref);
                    d.drop;
                    0;
                }
            }
        },
        print "Data { flag: Borrowed, x: 42 }",
        return "0"
    );
}

#[test]
fn drop_given_nested() {
    // Drop on a Given object with nested Given fields: recursive drop.
    // Print before dropping to confirm value was live.
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(given self) -> Int {
                    let o = new Outer(new Inner(1));
                    print(o.ref);
                    o.drop;
                    0;
                }
            }
        },
        print "Outer { flag: Borrowed, inner: Inner { flag: Given, x: 1 } }",
        return "0"
    );
}

#[test]
fn drop_given_nested_uninitializes() {
    // UB test: verify that drop Given recursively uninitializes nested fields.
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(given self) -> Outer {
                    let o = new Outer(new Inner(1));
                    o.drop;
                    o.give;
                }
            }
        },
        return "Outer { flag: Uninitialized, inner: Inner { flag: Uninitialized, x: 1 } }"
    );
}

#[test]
fn drop_borrowed_is_noop() {
    // drop on a Borrowed value: no-op. The value remains usable.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    let r = d.ref;
                    r.drop;
                    r.give;
                }
            }
        },
        return "Data { flag: Borrowed, x: 42 }"
    );
}

#[test]
fn drop_shared() {
    // drop on a Shared value: applies "drop shared" operation.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Int {
                    let d = new Data(42);
                    let s = d.share;
                    print(s.ref);
                    s.drop;
                    0;
                }
            }
        },
        print "Data { flag: Borrowed, x: 42 }",
        return "0"
    );
}

#[test]
fn drop_shared_nested() {
    // Drop a shared object with nested classes — drop-shared recurses.
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(given self) -> Int {
                    let o = new Outer(new Inner(1));
                    let s = o.share;
                    print(s.ref);
                    s.drop;
                    0;
                }
            }
        },
        print "Outer { flag: Borrowed, inner: Inner { flag: Given, x: 1 } }",
        return "0"
    );
}

// ---------------------------------------------------------------
// share (value.share): recursive behavior
// ---------------------------------------------------------------

#[test]
fn share_nested_objects() {
    // Sharing an object with a nested unique field should recursively
    // set all flags to Shared.
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(given self) -> Outer {
                    let o = new Outer(new Inner(1));
                    o.share;
                }
            }
        },
        return "Outer { flag: Shared, inner: Inner { flag: Shared, x: 1 } }"
    );
}

#[test]
fn share_already_shared_is_noop() {
    // Sharing a value that's already Shared should be a no-op.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    let s = d.share;
                    s.share;
                }
            }
        },
        return "Data { flag: Shared, x: 42 }"
    );
}

#[test]
fn share_borrowed_is_noop() {
    // Sharing a Borrowed value is a no-op — it stays Borrowed.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    let r = d.ref;
                    r.share;
                }
            }
        },
        return "Data { flag: Borrowed, x: 42 }"
    );
}

// ---------------------------------------------------------------
// mut: creates MutRef (requires Word::MutRef)
// ---------------------------------------------------------------

// TODO: mut tests — requires adding Word::MutRef(Pointer) to the
// Word enum and updating display. Deferred until we implement mut.
//
// #[test]
// fn mut_from_given() {
//     // mut from a Given source: create a MutRef pointing at the source.
// }
//
// #[test]
// fn mut_from_shared_faults() {
//     // mut from a Shared source: interpreter fault.
// }
//
// #[test]
// fn mut_from_borrowed_faults() {
//     // mut from a Borrowed source: interpreter fault.
// }
