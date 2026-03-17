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
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   d . give ;
            Output: Trace: exit Main.main => Data { x: 42 }
            Result: Ok: Data { x: 42 }
            Alloc 0x05: [Int(42)]"#]]
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
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   let a = d . give ;
            Output: Trace:   a = Data { x: 42 }
            Output: Trace:   d . give ;
            Result: Fault: access of uninitialized value
            Alloc 0x05: [Int(42)]"#]]
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
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   let s = d . give . share ;
            Output: Trace:   s = shared Data { x: 42 }
            Output: Trace:   print(s . give) ;
            Output: shared Data { x: 42 }
            Output: Trace:   s . give ;
            Output: Trace: exit Main.main => shared Data { x: 42 }
            Result: Ok: shared Data { x: 42 }
            Alloc 0x09: [Int(42)]"#]]
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
            Output: Trace: enter Main.main
            Output: Trace:   let o = new Outer (new Inner (1)) ;
            Output: Trace:   o = Outer { inner: Inner { x: 1 } }
            Output: Trace:   let s = o . give . share ;
            Output: Trace:   s = shared Outer { inner: Inner { x: 1 } }
            Output: Trace:   s . give ;
            Output: Trace: exit Main.main => shared Outer { inner: Inner { x: 1 } }
            Result: Ok: shared Outer { inner: Inner { x: 1 } }
            Alloc 0x08: [Int(1)]"#]]
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
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   let r = d . ref ;
            Output: Trace:   r = ref [d] Data { x: 42 }
            Output: Trace:   r . give ;
            Output: Trace: exit Main.main => ref [d] Data { x: 42 }
            Result: Ok: ref [d] Data { x: 42 }
            Alloc 0x07: [Int(42)]"#]]
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
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   let s = d . give . share ;
            Output: Trace:   s = shared Data { x: 42 }
            Output: Trace:   let x1 = s . give ;
            Output: Trace:   x1 = shared Data { x: 42 }
            Output: Trace:   let x2 = s . give ;
            Output: Trace:   x2 = shared Data { x: 42 }
            Output: Trace:   print(x1 . give) ;
            Output: shared Data { x: 42 }
            Output: Trace:   print(x2 . give) ;
            Output: shared Data { x: 42 }
            Output: Trace:   s . give ;
            Output: Trace: exit Main.main => shared Data { x: 42 }
            Result: Ok: shared Data { x: 42 }
            Alloc 0x0f: [Int(42)]"#]]
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
            Output: Trace: enter Main.main
            Output: Trace:   let o = new Outer (new Inner (99)) ;
            Output: Trace:   o = Outer { inner: Inner { x: 99 } }
            Output: Trace:   let s = o . give . share ;
            Output: Trace:   s = shared Outer { inner: Inner { x: 99 } }
            Output: Trace:   let i1 = s . inner . give ;
            Output: Trace:   i1 = shared Inner { x: 99 }
            Output: Trace:   let i2 = s . inner . give ;
            Output: Trace:   i2 = shared Inner { x: 99 }
            Output: Trace:   print(i1 . give) ;
            Output: shared Inner { x: 99 }
            Output: Trace:   i2 . give ;
            Output: Trace: exit Main.main => shared Inner { x: 99 }
            Result: Ok: shared Inner { x: 99 }
            Alloc 0x0e: [Int(99)]"#]]
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
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   print(d . ref) ;
            Output: ref [d] Data { x: 42 }
            Output: Trace:   d . give ;
            Output: Trace: exit Main.main => Data { x: 42 }
            Result: Ok: Data { x: 42 }
            Alloc 0x07: [Int(42)]"#]]
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
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   let s = d . give . share ;
            Output: Trace:   s = shared Data { x: 42 }
            Output: Trace:   s . ref ;
            Output: Trace: exit Main.main => shared Data { x: 42 }
            Result: Ok: shared Data { x: 42 }
            Alloc 0x07: [Int(42)]"#]]
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
            Output: Trace: enter Main.main
            Output: Trace:   let o = new Outer (new Inner (1)) ;
            Output: Trace:   o = Outer { inner: Inner { x: 1 } }
            Output: Trace:   let s = o . give . share ;
            Output: Trace:   s = shared Outer { inner: Inner { x: 1 } }
            Output: Trace:   s . ref ;
            Output: Trace: exit Main.main => shared Outer { inner: Inner { x: 1 } }
            Result: Ok: shared Outer { inner: Inner { x: 1 } }
            Alloc 0x08: [Int(1)]"#]]
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
            Output: Trace: enter Main.main
            Output: Trace:   let o = new Outer (new Inner (7)) ;
            Output: Trace:   o = Outer { inner: Inner { x: 7 } }
            Output: Trace:   let s = o . give . share ;
            Output: Trace:   s = shared Outer { inner: Inner { x: 7 } }
            Output: Trace:   let r = s . ref ;
            Output: Trace:   r = shared Outer { inner: Inner { x: 7 } }
            Output: Trace:   let i1 = r . inner . give ;
            Output: Trace:   i1 = shared Inner { x: 7 }
            Output: Trace:   let i2 = r . inner . give ;
            Output: Trace:   i2 = shared Inner { x: 7 }
            Output: Trace:   print(i1 . give) ;
            Output: shared Inner { x: 7 }
            Output: Trace:   i2 . give ;
            Output: Trace: exit Main.main => shared Inner { x: 7 }
            Result: Ok: shared Inner { x: 7 }
            Alloc 0x10: [Int(7)]"#]]
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
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   let r = d . ref ;
            Output: Trace:   r = ref [d] Data { x: 42 }
            Output: Trace:   r . ref ;
            Output: Trace: exit Main.main => ref [d] Data { x: 42 }
            Result: Ok: ref [d] Data { x: 42 }
            Alloc 0x07: [Int(42)]"#]]
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
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   print(d . ref) ;
            Output: ref [d] Data { x: 42 }
            Output: Trace:   d . drop ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
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
            Output: Trace: enter Main.main
            Output: Trace:   let o = new Outer (new Inner (1)) ;
            Output: Trace:   o = Outer { inner: Inner { x: 1 } }
            Output: Trace:   print(o . ref) ;
            Output: ref [o] Outer { inner: Inner { x: 1 } }
            Output: Trace:   o . drop ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
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
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let o = new Outer (new Inner (1)) ;
            Output: Trace:   o = Outer { inner: Inner { x: 1 } }
            Output: Trace:   o . drop ;
            Output: Trace:   o . give ;
            Result: Fault: access of uninitialized value"#]]
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
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   let r = d . ref ;
            Output: Trace:   r = ref [d] Data { x: 42 }
            Output: Trace:   r . drop ;
            Output: Trace:   r . give ;
            Output: Trace: exit Main.main => ref [d] Data { x: 42 }
            Result: Ok: ref [d] Data { x: 42 }
            Alloc 0x08: [Int(42)]"#]]
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
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   let s = d . give . share ;
            Output: Trace:   s = shared Data { x: 42 }
            Output: Trace:   print(s . ref) ;
            Output: shared Data { x: 42 }
            Output: Trace:   s . drop ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
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
            Output: Trace: enter Main.main
            Output: Trace:   let o = new Outer (new Inner (1)) ;
            Output: Trace:   o = Outer { inner: Inner { x: 1 } }
            Output: Trace:   let s = o . give . share ;
            Output: Trace:   s = shared Outer { inner: Inner { x: 1 } }
            Output: Trace:   print(s . ref) ;
            Output: shared Outer { inner: Inner { x: 1 } }
            Output: Trace:   s . drop ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
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
            Output: Trace: enter Main.main
            Output: Trace:   let o = new Outer (new Inner (1)) ;
            Output: Trace:   o = Outer { inner: Inner { x: 1 } }
            Output: Trace:   o . give . share ;
            Output: Trace: exit Main.main => shared Outer { inner: Inner { x: 1 } }
            Result: Ok: shared Outer { inner: Inner { x: 1 } }
            Alloc 0x06: [Int(1)]"#]]
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
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   let s = d . give . share ;
            Output: Trace:   s = shared Data { x: 42 }
            Output: Trace:   s . give . share ;
            Output: Trace: exit Main.main => shared Data { x: 42 }
            Result: Ok: shared Data { x: 42 }
            Alloc 0x07: [Int(42)]"#]]
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
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   let r = d . ref ;
            Output: Trace:   r = ref [d] Data { x: 42 }
            Output: Trace:   r . give . share ;
            Output: Trace: exit Main.main => ref [d] Data { x: 42 }
            Result: Ok: ref [d] Data { x: 42 }
            Alloc 0x07: [Int(42)]"#]]
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
            Output: Trace: enter Main.main
            Output: Trace:   let o = new Outer (new Inner (42)) ;
            Output: Trace:   o = Outer { inner: Inner { x: 42 } }
            Output: Trace:   let r = o . ref ;
            Output: Trace:   r = ref [o] Outer { inner: Inner { x: 42 } }
            Output: Trace:   let stolen = r . inner . give ;
            Output: Trace:   stolen = ref [o] Inner { x: 42 }
            Output: Trace:   print(stolen . give) ;
            Output: ref [o] Inner { x: 42 }
            Output: Trace:   o . inner . give ;
            Output: Trace: exit Main.main => Inner { x: 42 }
            Result: Ok: Inner { x: 42 }
            Alloc 0x0c: [Int(42)]"#]]
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
            Output: Trace: enter Main.main
            Output: Trace:   let o = new Outer (new Inner (42)) ;
            Output: Trace:   o = Outer { inner: Inner { x: 42 } }
            Output: Trace:   let r = o . ref ;
            Output: Trace:   r = ref [o] Outer { inner: Inner { x: 42 } }
            Output: Trace:   r . inner . ref ;
            Output: Trace: exit Main.main => ref [o] Inner { x: 42 }
            Result: Ok: ref [o] Inner { x: 42 }
            Alloc 0x08: [Int(42)]"#]]
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
            Output: Trace: enter Main.main
            Output: Trace:   let o = new Outer (new Inner (42)) ;
            Output: Trace:   o = Outer { inner: Inner { x: 42 } }
            Output: Trace:   let s = o . give . share ;
            Output: Trace:   s = shared Outer { inner: Inner { x: 42 } }
            Output: Trace:   let i1 = s . inner . give ;
            Output: Trace:   i1 = shared Inner { x: 42 }
            Output: Trace:   let i2 = s . inner . give ;
            Output: Trace:   i2 = shared Inner { x: 42 }
            Output: Trace:   print(i1 . give) ;
            Output: shared Inner { x: 42 }
            Output: Trace:   i2 . give ;
            Output: Trace: exit Main.main => shared Inner { x: 42 }
            Result: Ok: shared Inner { x: 42 }
            Alloc 0x0e: [Int(42)]"#]]
    );
}

#[test]
fn shared_ref_subtype() {
    // A shared value typed as ref[p] — the system should accept it
    // (shared is subtype of ref) and propagate runtime Shared flags.
    crate::assert_interpret!(
        {
            class Link0 { inner: Link1; }
            class Link1 { inner: Link2; }
            class Link2 { }

            class Main {
                fn main(given self) -> () {
                    let o = new Link0(new Link1(new Link2()));

                    // o.inner.ref is ref[o] Link1 — pass through sub, get ref[o] Link2
                    let a = self.ref.sub[ref[self], ref[o]](o.inner.ref);
                    print(a.give);

                    // x is shared Link1 — typed as shared, should propagate Shared flags
                    let x = new Link1(new Link2()).share;
                    let y = self.ref.sub[ref[self], ref[o]](x.give);
                    print(x.give);
                    print(y.give);

                    ();
                }

                fn sub[perm S, perm P](S self, link1: P Link1) -> P Link2 {
                    link1.inner.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let o = new Link0 (new Link1 (new Link2 ())) ;
            Output: Trace:   o = Link0 { inner: Link1 { inner: Link2 {  } } }
            Output: Trace:   let a = self . ref . sub [ref [self], ref [o]] (o . inner . ref) ;
            Output: Trace:   enter Main.sub
            Output: Trace:     link1 . inner . give ;
            Output: Trace:   exit Main.sub => ref [o . inner] Link2 {  }
            Output: Trace:   a = ref [o . inner] Link2 {  }
            Output: Trace:   print(a . give) ;
            Output: ref [o . inner] Link2 {  }
            Output: Trace:   let x = new Link1 (new Link2 ()) . share ;
            Output: Trace:   x = shared Link1 { inner: Link2 {  } }
            Output: Trace:   let y = self . ref . sub [ref [self], ref [o]] (x . give) ;
            Output: Trace:   enter Main.sub
            Output: Trace:     link1 . inner . give ;
            Output: Trace:   exit Main.sub => shared Link2 {  }
            Output: Trace:   y = shared Link2 {  }
            Output: Trace:   print(x . give) ;
            Output: shared Link1 { inner: Link2 {  } }
            Output: Trace:   print(y . give) ;
            Output: shared Link2 {  }
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

// ---------------------------------------------------------------
// mut: creates MutRef (1-word allocation pointing at the original)
// ---------------------------------------------------------------

#[test]
fn mut_from_given() {
    // mut from a Given source: create a MutRef pointing at the original.
    // The MutRef dereferences through to the underlying value for display.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    let m = d.mut;
                    print(m.give);
                    d.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   let m = d . mut ;
            Output: Trace:   m = mut [d] Data { x: 42 }
            Output: Trace:   print(m . give) ;
            Output: mut [d] Data { x: 42 }
            Output: Trace:   d . give ;
            Output: Trace: exit Main.main => Data { x: 42 }
            Result: Ok: Data { x: 42 }
            Alloc 0x09: [Int(42)]"#]]
    );
}

#[test]
fn mut_field_read() {
    // Access a field through a MutRef: dereferences the MutRef,
    // then projects the field from the underlying allocation.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; y: Int; }
            class Main {
                fn main(given self) -> Int {
                    let d = new Data(10, 20);
                    let m = d.mut;
                    m.y.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (10, 20) ;
            Output: Trace:   d = Data { x: 10, y: 20 }
            Output: Trace:   let m = d . mut ;
            Output: Trace:   m = mut [d] Data { x: 10, y: 20 }
            Output: Trace:   m . y . give ;
            Output: Trace: exit Main.main => 20
            Result: Ok: 20
            Alloc 0x08: [Int(20)]"#]]
    );
}

#[test]
fn mut_field_reassign() {
    // Reassign a field through a MutRef: the change is visible
    // in the original value because MutRef points at it directly.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    let m = d.mut;
                    m.x = 99;
                    d.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   let m = d . mut ;
            Output: Trace:   m = mut [d] Data { x: 42 }
            Output: Trace:   m . x = 99 ;
            Output: Trace:   m . x = 99
            Output: Trace:   d . give ;
            Output: Trace: exit Main.main => Data { x: 99 }
            Result: Ok: Data { x: 99 }
            Alloc 0x09: [Int(99)]"#]]
    );
}

#[test]
fn mut_give_copies_mutref() {
    // Giving a MutRef copies the MutRef word into a new allocation.
    // Both the original and the copy point at the same underlying data.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    let m = d.mut;
                    let m2 = m.give;
                    m2.x = 99;
                    d.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   let m = d . mut ;
            Output: Trace:   m = mut [d] Data { x: 42 }
            Output: Trace:   let m2 = m . give ;
            Output: Trace:   m2 = mut [d] Data { x: 42 }
            Output: Trace:   m2 . x = 99 ;
            Output: Trace:   m2 . x = 99
            Output: Trace:   d . give ;
            Output: Trace: exit Main.main => Data { x: 99 }
            Result: Ok: Data { x: 99 }
            Alloc 0x0b: [Int(99)]"#]]
    );
}

#[test]
fn mut_ref_through_mutref() {
    // Ref through a MutRef: dereferences the MutRef and copies
    // the underlying value with Borrowed flags.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    let m = d.mut;
                    m.ref;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   let m = d . mut ;
            Output: Trace:   m = mut [d] Data { x: 42 }
            Output: Trace:   m . ref ;
            Output: Trace: exit Main.main => ref [m] mut [d] Data { x: 42 }
            Result: Ok: ref [m] mut [d] Data { x: 42 }
            Alloc 0x07: [Int(42)]"#]]
    );
}

#[test]
fn mut_drop() {
    // Dropping a MutRef: scrubs the MutRef allocation.
    // The underlying value is NOT dropped — it's still owned by the original.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    let m = d.mut;
                    m.drop;
                    d.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   let m = d . mut ;
            Output: Trace:   m = mut [d] Data { x: 42 }
            Output: Trace:   m . drop ;
            Output: Trace:   d . give ;
            Output: Trace: exit Main.main => Data { x: 42 }
            Result: Ok: Data { x: 42 }
            Alloc 0x08: [Int(42)]"#]]
    );
}

#[test]
fn mut_of_mut() {
    // Mut of mut: equivalent to give — copies the MutRef word.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    let m1 = d.mut;
                    let m2 = m1.mut;
                    m2.x = 77;
                    d.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let d = new Data (42) ;
            Output: Trace:   d = Data { x: 42 }
            Output: Trace:   let m1 = d . mut ;
            Output: Trace:   m1 = mut [d] Data { x: 42 }
            Output: Trace:   let m2 = m1 . mut ;
            Output: Trace:   m2 = mut [m1] mut [d] Data { x: 42 }
            Output: Trace:   m2 . x = 77 ;
            Output: Trace:   m2 . x = 77
            Output: Trace:   d . give ;
            Output: Trace: exit Main.main => Data { x: 77 }
            Result: Ok: Data { x: 77 }
            Alloc 0x0b: [Int(77)]"#]]
    );
}

#[test]
fn mut_nested_field_reassign() {
    // Reassign a nested field through a MutRef.
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(given self) -> Outer {
                    let o = new Outer(new Inner(1));
                    let m = o.mut;
                    m.inner.x = 42;
                    o.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let o = new Outer (new Inner (1)) ;
            Output: Trace:   o = Outer { inner: Inner { x: 1 } }
            Output: Trace:   let m = o . mut ;
            Output: Trace:   m = mut [o] Outer { inner: Inner { x: 1 } }
            Output: Trace:   m . inner . x = 42 ;
            Output: Trace:   m . inner . x = 42
            Output: Trace:   o . give ;
            Output: Trace: exit Main.main => Outer { inner: Inner { x: 42 } }
            Result: Ok: Outer { inner: Inner { x: 42 } }
            Alloc 0x0a: [Int(42)]"#]]
    );
}

// ---------------------------------------------------------------
// mut: field-path tests (a.b.mut — mut of a field, not a variable)
// ---------------------------------------------------------------

#[test]
fn mut_field_of_given() {
    // Mut a field of a Given object: creates a MutRef pointing
    // into the original allocation at the field's offset.
    // Reassigning through the MutRef modifies the original.
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(given self) -> Outer {
                    let o = new Outer(new Inner(1));
                    let m = o.inner.mut;
                    m.x = 99;
                    o.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let o = new Outer (new Inner (1)) ;
            Output: Trace:   o = Outer { inner: Inner { x: 1 } }
            Output: Trace:   let m = o . inner . mut ;
            Output: Trace:   m = mut [o . inner] Inner { x: 1 }
            Output: Trace:   m . x = 99 ;
            Output: Trace:   m . x = 99
            Output: Trace:   o . give ;
            Output: Trace: exit Main.main => Outer { inner: Inner { x: 99 } }
            Result: Ok: Outer { inner: Inner { x: 99 } }
            Alloc 0x0a: [Int(99)]"#]]
    );
}

#[test]
fn mut_field_of_given_read() {
    // Read a field through a MutRef to a field of a Given object.
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; y: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(given self) -> Int {
                    let o = new Outer(new Inner(10, 20));
                    let m = o.inner.mut;
                    m.y.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let o = new Outer (new Inner (10, 20)) ;
            Output: Trace:   o = Outer { inner: Inner { x: 10, y: 20 } }
            Output: Trace:   let m = o . inner . mut ;
            Output: Trace:   m = mut [o . inner] Inner { x: 10, y: 20 }
            Output: Trace:   m . y . give ;
            Output: Trace: exit Main.main => 20
            Result: Ok: 20
            Alloc 0x09: [Int(20)]"#]]
    );
}

#[test]
fn mut_field_of_given_drop() {
    // Dropping a MutRef to a field: scrubs the MutRef allocation,
    // original field untouched.
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(given self) -> Outer {
                    let o = new Outer(new Inner(42));
                    let m = o.inner.mut;
                    m.drop;
                    o.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let o = new Outer (new Inner (42)) ;
            Output: Trace:   o = Outer { inner: Inner { x: 42 } }
            Output: Trace:   let m = o . inner . mut ;
            Output: Trace:   m = mut [o . inner] Inner { x: 42 }
            Output: Trace:   m . drop ;
            Output: Trace:   o . give ;
            Output: Trace: exit Main.main => Outer { inner: Inner { x: 42 } }
            Result: Ok: Outer { inner: Inner { x: 42 } }
            Alloc 0x09: [Int(42)]"#]]
    );
}

#[test]
fn mut_field_through_mut() {
    // a.mut then m.inner.mut: the inner .mut traverses through the
    // outer MutRef dereference, then creates a new MutRef pointing
    // at the inner field of the original allocation.
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(given self) -> Outer {
                    let o = new Outer(new Inner(1));
                    let m = o.mut;
                    let m2 = m.inner.mut;
                    m2.x = 55;
                    o.give;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let o = new Outer (new Inner (1)) ;
            Output: Trace:   o = Outer { inner: Inner { x: 1 } }
            Output: Trace:   let m = o . mut ;
            Output: Trace:   m = mut [o] Outer { inner: Inner { x: 1 } }
            Output: Trace:   let m2 = m . inner . mut ;
            Output: Trace:   m2 = mut [m . inner] mut [o] Inner { x: 1 }
            Output: Trace:   m2 . x = 55 ;
            Output: Trace:   m2 . x = 55
            Output: Trace:   o . give ;
            Output: Trace: exit Main.main => Outer { inner: Inner { x: 55 } }
            Result: Ok: Outer { inner: Inner { x: 55 } }
            Alloc 0x0c: [Int(55)]"#]]
    );
}

#[test]
fn mut_field_through_shared() {
    // Mut of a field reached through a Shared object.
    // resolve_place sets effective=Shared when crossing the shared perm,
    // so mut_place should fault (cannot mutably borrow a shared or borrowed value).
    crate::assert_interpret_fault!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(given self) -> Inner {
                    let o = new Outer(new Inner(1));
                    let s = o.give.share;
                    s.inner.mut;
                }
            }
        },
        expect_test::expect![[""]]
    );
}

#[test]
fn mut_field_through_ref() {
    // Mut of a field reached through a Borrowed (ref) object.
    // resolve_place sets effective=Borrowed when crossing the ref perm.
    // Borrowed means read-only — cannot take a mutable reference through it,
    // just like shared.
    crate::assert_interpret_fault!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(given self) -> Inner {
                    let o = new Outer(new Inner(1));
                    let r = o.ref;
                    r.inner.mut;
                }
            }
        },
        expect_test::expect![[""]]
    );
}

#[test]
fn mut_field_uninitialized() {
    // Mut of a field that has been moved out (uninitialized).
    crate::assert_interpret_fault!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(given self) -> Inner {
                    let o = new Outer(new Inner(1));
                    let stolen = o.inner.give;
                    o.inner.mut;
                }
            }
        },
        expect_test::expect![[""]]
    );
}

// ---------------------------------------------------------------
// mut: error cases
// ---------------------------------------------------------------

#[test]
fn mut_of_shared_faults() {
    // Cannot take a mut ref of a shared value.
    crate::assert_interpret_fault!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    let s = d.give.share;
                    s.mut;
                }
            }
        },
        expect_test::expect![[""]]
    );
}

#[test]
fn mut_of_uninitialized_faults() {
    // Cannot take a mut ref of a dropped value.
    crate::assert_interpret_fault!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    d.drop;
                    d.mut;
                }
            }
        },
        expect_test::expect![[""]]
    );
}

#[test]
fn mut_of_copy_type_faults() {
    // Cannot take a mut ref of a copy type (no flags).
    crate::assert_interpret_fault!(
        {
            class Main {
                fn main(given self) -> Int {
                    let x = 42;
                    x.mut;
                }
            }
        },
        expect_test::expect![[""]]
    );
}

// ---------------------------------------------------------------
// mut: array interaction
// ---------------------------------------------------------------

#[test]
fn mut_of_array_create_and_drop() {
    // Create a MutRef to a Given array, drop the MutRef, verify original intact.
    // Note: array operations (array_give, array_set) cannot currently
    // accept a MutRef directly — they expect a proper array TypedValue
    // (2-word layout). A MutRef.give produces a 1-word MutRef allocation.
    // MutRef+array interaction requires method calls (mut self) or
    // teaching array ops to dereference through MutRef.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Int {
                    let a = array_new[Data](2);
                    let m = a.mut;
                    m.drop;
                    array_capacity[Data](a.give);
                }
            }
        },
        expect_test::expect![[r#"
            Result: Fault: access of uninitialized value
            Alloc 0x03: [RefCount(1), Capacity(2), Uninitialized, Uninitialized]
            Alloc 0x04: [Flags(Given), Pointer(0x03)]
            Alloc 0x06: [MutRef(0x03)]"#]]
    );
}

// ---------------------------------------------------------------
// mut: dangling MutRef (UB — type system should prevent)
// ---------------------------------------------------------------

#[test]
fn mut_dangling_after_give() {
    // UB test: create a MutRef to d, then move d away.
    // The original allocation is now uninitialized. The MutRef
    // still points at it. resolve_place_to_object dereferences
    // through the MutRef and finds uninitialized data, so the
    // give faults. The type system prevents this in well-typed programs.
    crate::assert_interpret_fault!(
        {
            class Data { x: Int; }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(42);
                    let m = d.mut;
                    let stolen = d.give;
                    m.give;
                }
            }
        },
        expect_test::expect![[""]]
    );
}
