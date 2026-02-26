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
        expect_test::expect![[r#"
            Result: Data { flag: Given, x: 42 }
            Alloc 0x05: [Flags(Given), Int(42)]"#]]
    );
}

#[test]
fn give_from_given_uninitializes_source() {
    // UB test: giving a moved value faults at runtime.
    crate::assert_interpret_fault!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    let a = d.give;
                    d.give;
                }
            }
        },
        "give of uninitialized value"
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
                    let s = d.give.share;
                    print(s.give);
                    s.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: shared Data { flag: Shared, x: 42 }
            Result: shared Data { flag: Shared, x: 42 }
            Alloc 0x09: [Flags(Shared), Int(42)]"#]]
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
                    let s = o.give.share;
                    s.give;
                }
            }
        },
        expect_test::expect![[r#"
            Result: shared Outer { flag: Shared, inner: Inner { flag: Shared, x: 1 } }
            Alloc 0x08: [Flags(Shared), Flags(Shared), Int(1)]"#]]
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
        expect_test::expect![[r#"
            Result: ref [d] Data { flag: Borrowed, x: 42 }
            Alloc 0x07: [Flags(Borrowed), Int(42)]"#]]
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
                    let s = d.give.share;
                    let x1 = s.give;
                    let x2 = s.give;
                    print(x1.give);
                    print(x2.give);
                    s.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: shared Data { flag: Shared, x: 42 }
            Output: shared Data { flag: Shared, x: 42 }
            Result: shared Data { flag: Shared, x: 42 }
            Alloc 0x0f: [Flags(Shared), Int(42)]"#]]
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
                    let s = o.give.share;
                    let i1 = s.inner.give;
                    let i2 = s.inner.give;
                    print(i1.give);
                    i2.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: shared Inner { flag: Shared, x: 99 }
            Result: shared Inner { flag: Shared, x: 99 }
            Alloc 0x0e: [Flags(Shared), Int(99)]"#]]
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
        expect_test::expect![[r#"
            Output: ref [d] Data { flag: Borrowed, x: 42 }
            Result: Data { flag: Given, x: 42 }
            Alloc 0x07: [Flags(Given), Int(42)]"#]]
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
                    let s = d.give.share;
                    s.ref;
                }
            }
        },
        expect_test::expect![[r#"
            Result: ref [s] Data { flag: Shared, x: 42 }
            Alloc 0x07: [Flags(Shared), Int(42)]"#]]
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
                    let s = o.give.share;
                    s.ref;
                }
            }
        },
        expect_test::expect![[r#"
            Result: ref [s] Outer { flag: Shared, inner: Inner { flag: Shared, x: 1 } }
            Alloc 0x08: [Flags(Shared), Flags(Shared), Int(1)]"#]]
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
                    let s = o.give.share;
                    let r = s.ref;
                    let i1 = r.inner.give;
                    let i2 = r.inner.give;
                    print(i1.give);
                    i2.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: ref [s] Inner { flag: Borrowed, x: 7 }
            Result: ref [s] Inner { flag: Borrowed, x: 7 }
            Alloc 0x10: [Flags(Borrowed), Int(7)]"#]]
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
        expect_test::expect![[r#"
            Result: ref [r] Data { flag: Borrowed, x: 42 }
            Alloc 0x07: [Flags(Borrowed), Int(42)]"#]]
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
        expect_test::expect![[r#"
            Output: ref [d] Data { flag: Borrowed, x: 42 }
            Result: 0
            Alloc 0x08: [Int(0)]"#]]
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
        expect_test::expect![[r#"
            Output: ref [o] Outer { flag: Borrowed, inner: Inner { flag: Given, x: 1 } }
            Result: 0
            Alloc 0x09: [Int(0)]"#]]
    );
}

#[test]
fn drop_given_nested_uninitializes() {
    // UB test: giving a dropped value faults at runtime.
    crate::assert_interpret_fault!(
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
        "give of uninitialized value"
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
        expect_test::expect![[r#"
            Result: ref [d] Data { flag: Borrowed, x: 42 }
            Alloc 0x08: [Flags(Borrowed), Int(42)]"#]]
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
                    let s = d.give.share;
                    print(s.ref);
                    s.drop;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: ref [s] Data { flag: Shared, x: 42 }
            Result: 0
            Alloc 0x0a: [Int(0)]"#]]
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
                    let s = o.give.share;
                    print(s.ref);
                    s.drop;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: ref [s] Outer { flag: Shared, inner: Inner { flag: Shared, x: 1 } }
            Result: 0
            Alloc 0x0b: [Int(0)]"#]]
    );
}

// ---------------------------------------------------------------
// share (value.give.share): recursive behavior
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
                    o.give.share;
                }
            }
        },
        expect_test::expect![[r#"
            Result: shared Outer { flag: Shared, inner: Inner { flag: Shared, x: 1 } }
            Alloc 0x06: [Flags(Shared), Flags(Shared), Int(1)]"#]]
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
                    let s = d.give.share;
                    s.give.share;
                }
            }
        },
        expect_test::expect![[r#"
            Result: shared Data { flag: Shared, x: 42 }
            Alloc 0x07: [Flags(Shared), Int(42)]"#]]
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
                    r.give.share;
                }
            }
        },
        expect_test::expect![[r#"
            Result: shared Data { flag: Borrowed, x: 42 }
            Alloc 0x07: [Flags(Borrowed), Int(42)]"#]]
    );
}

// ---------------------------------------------------------------
// place resolution: field access through borrowed/shared paths
// ---------------------------------------------------------------
// These tests verify that accessing a field through a borrowed or shared
// path produces the correct effective permission. The type in the output
// should reflect the accumulated permission from the traversal path.

#[test]
fn give_field_through_borrowed_path() {
    // Ref an Outer, then give its inner field.
    // The inner's own flags are Given, but we traversed through Borrowed,
    // so the effective permission should be Borrowed — no move, source intact.
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(given self) -> Inner {
                    let o = new Outer(new Inner(42));
                    let r = o.ref;
                    let stolen = r.inner.give;
                    print(stolen.give);
                    // Original should still be intact since we went through a ref
                    o.inner.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: ref [o] Inner { flag: Borrowed, x: 42 }
            Result: Inner { flag: Given, x: 42 }
            Alloc 0x0c: [Flags(Given), Int(42)]"#]]
    );
}

#[test]
fn ref_field_through_borrowed_path() {
    // Ref an Outer, then ref its inner field.
    // Traversing through Borrowed, inner should be Borrowed regardless of own flags.
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(given self) -> Inner {
                    let o = new Outer(new Inner(42));
                    let r = o.ref;
                    r.inner.ref;
                }
            }
        },
        expect_test::expect![[r#"
            Result: ref [r . inner] Inner { flag: Borrowed, x: 42 }
            Alloc 0x08: [Flags(Borrowed), Int(42)]"#]]
    );
}

#[test]
fn give_field_through_shared_path() {
    // Share an Outer, then give its inner field.
    // Traversing through Shared — inner should come out Shared,
    // and giving should be repeatable (shared is copyable).
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(given self) -> Inner {
                    let o = new Outer(new Inner(42));
                    let s = o.give.share;
                    let i1 = s.inner.give;
                    let i2 = s.inner.give;
                    print(i1.give);
                    i2.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: shared Inner { flag: Shared, x: 42 }
            Result: shared Inner { flag: Shared, x: 42 }
            Alloc 0x0e: [Flags(Shared), Int(42)]"#]]
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
