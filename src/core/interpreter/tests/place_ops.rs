// Tests for flags-dependent place operations: give, place sharing, mut, drop.
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
                fn main(^ self) -> Data {
                    let d = new Data(42);
                    d^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   _1_d ^ ;
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
                fn main(^ self) -> Data {
                    let d = new Data(42);
                    let a = d^;
                    d^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   let _1_a = _1_d ^ ;
            Output: Trace:   _1_a = Data { x: 42 }
            Output: Trace:   _1_d ^ ;
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
                fn main(^ self) -> Data {
                    let d = new Data(42);
                    let s = d^.share;
                    print(s^);
                    s^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   let _1_s = _1_d ^ . share ;
            Output: Trace:   _1_s = shared Data { x: 42 }
            Output: Trace:   print(_1_s ^) ;
            Output: ----->   shared Data { x: 42 }
            Output: Trace:   _1_s ^ ;
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
                fn main(^ self) -> Outer {
                    let o = new Outer(new Inner(1));
                    let s = o^.share;
                    s^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_o = new Outer (new Inner (1)) ;
            Output: Trace:   _1_o = Outer { inner: Inner { x: 1 } }
            Output: Trace:   let _1_s = _1_o ^ . share ;
            Output: Trace:   _1_s = shared Outer { inner: Inner { x: 1 } }
            Output: Trace:   _1_s ^ ;
            Output: Trace: exit Main.main => shared Outer { inner: Inner { x: 1 } }
            Result: Ok: shared Outer { inner: Inner { x: 1 } }
            Alloc 0x08: [Int(1)]"#]]
    );
}

#[test]
fn give_from_borrowed() {
    // give from a SharedPlace source: copy fields, set flags to SharedPlace.
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Main {
                fn main(^ self) -> () {
                    let d = new Data(42);
                    let r = d.share;
                    print(r^);
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   let _1_r = _1_d . share ;
            Output: Trace:   _1_r = shared [_1_d] Data { x: 42 }
            Output: Trace:   print(_1_r ^) ;
            Output: ----->   shared [_1_d] Data { x: 42 }
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

#[test]
fn give_shared_multiple_times() {
    // A shared value is duplicable — giving it repeatedly works,
    // each copy gets flag: Shared.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(^ self) -> Data {
                    let d = new Data(42);
                    let s = d^.share;
                    let x1 = s^;
                    let x2 = s^;
                    print(x1^);
                    print(x2^);
                    s^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   let _1_s = _1_d ^ . share ;
            Output: Trace:   _1_s = shared Data { x: 42 }
            Output: Trace:   let _1_x1 = _1_s ^ ;
            Output: Trace:   _1_x1 = shared Data { x: 42 }
            Output: Trace:   let _1_x2 = _1_s ^ ;
            Output: Trace:   _1_x2 = shared Data { x: 42 }
            Output: Trace:   print(_1_x1 ^) ;
            Output: ----->   shared Data { x: 42 }
            Output: Trace:   print(_1_x2 ^) ;
            Output: ----->   shared Data { x: 42 }
            Output: Trace:   _1_s ^ ;
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
                fn main(^ self) -> Inner {
                    let o = new Outer(new Inner(99));
                    let s = o^.share;
                    let i1 = s.inner^;
                    let i2 = s.inner^;
                    print(i1^);
                    i2^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_o = new Outer (new Inner (99)) ;
            Output: Trace:   _1_o = Outer { inner: Inner { x: 99 } }
            Output: Trace:   let _1_s = _1_o ^ . share ;
            Output: Trace:   _1_s = shared Outer { inner: Inner { x: 99 } }
            Output: Trace:   let _1_i1 = _1_s . inner ^ ;
            Output: Trace:   _1_i1 = shared Inner { x: 99 }
            Output: Trace:   let _1_i2 = _1_s . inner ^ ;
            Output: Trace:   _1_i2 = shared Inner { x: 99 }
            Output: Trace:   print(_1_i1 ^) ;
            Output: ----->   shared Inner { x: 99 }
            Output: Trace:   _1_i2 ^ ;
            Output: Trace: exit Main.main => shared Inner { x: 99 }
            Result: Ok: shared Inner { x: 99 }
            Alloc 0x0e: [Int(99)]"#]]
    );
}

// ---------------------------------------------------------------
// place sharing: flags-dependent behavior
// ---------------------------------------------------------------

#[test]
fn ref_from_given() {
    // place sharing from a Given source: copy fields, set flags to SharedPlace.
    // Source remains Given — print the place sharing, then return the original.
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Main {
                fn main(^ self) -> Data {
                    let d = new Data(42);
                    print(d.share);
                    d^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   print(_1_d . share) ;
            Output: ----->   shared [_1_d] Data { x: 42 }
            Output: Trace:   _1_d ^ ;
            Output: Trace: exit Main.main => Data { x: 42 }
            Result: Ok: Data { x: 42 }
            Alloc 0x07: [Int(42)]"#]]
    );
}

#[test]
fn ref_from_shared() {
    // place sharing from a Shared source: copy fields, set flags to Shared
    // (not SharedPlace — shared stays shared).
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(^ self) -> Data {
                    let d = new Data(42);
                    let s = d^.share;
                    s.share;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   let _1_s = _1_d ^ . share ;
            Output: Trace:   _1_s = shared Data { x: 42 }
            Output: Trace:   _1_s . share ;
            Output: Trace: exit Main.main => shared Data { x: 42 }
            Result: Ok: shared Data { x: 42 }
            Alloc 0x07: [Int(42)]"#]]
    );
}

#[test]
fn ref_from_shared_nested() {
    // Ref from a shared object with nested fields:
    // result should have Shared flags throughout (not SharedPlace).
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(^ self) -> Outer {
                    let o = new Outer(new Inner(1));
                    let s = o^.share;
                    s.share;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_o = new Outer (new Inner (1)) ;
            Output: Trace:   _1_o = Outer { inner: Inner { x: 1 } }
            Output: Trace:   let _1_s = _1_o ^ . share ;
            Output: Trace:   _1_s = shared Outer { inner: Inner { x: 1 } }
            Output: Trace:   _1_s . share ;
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
                fn main(^ self) -> Inner {
                    let o = new Outer(new Inner(7));
                    let s = o^.share;
                    let r = s.share;
                    let i1 = r.inner^;
                    let i2 = r.inner^;
                    print(i1^);
                    i2^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_o = new Outer (new Inner (7)) ;
            Output: Trace:   _1_o = Outer { inner: Inner { x: 7 } }
            Output: Trace:   let _1_s = _1_o ^ . share ;
            Output: Trace:   _1_s = shared Outer { inner: Inner { x: 7 } }
            Output: Trace:   let _1_r = _1_s . share ;
            Output: Trace:   _1_r = shared Outer { inner: Inner { x: 7 } }
            Output: Trace:   let _1_i1 = _1_r . inner ^ ;
            Output: Trace:   _1_i1 = shared Inner { x: 7 }
            Output: Trace:   let _1_i2 = _1_r . inner ^ ;
            Output: Trace:   _1_i2 = shared Inner { x: 7 }
            Output: Trace:   print(_1_i1 ^) ;
            Output: ----->   shared Inner { x: 7 }
            Output: Trace:   _1_i2 ^ ;
            Output: Trace: exit Main.main => shared Inner { x: 7 }
            Result: Ok: shared Inner { x: 7 }
            Alloc 0x10: [Int(7)]"#]]
    );
}

#[test]
fn ref_from_borrowed() {
    // place sharing from a SharedPlace source: copy fields, set flags to SharedPlace.
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Main {
                fn main(^ self) -> () {
                    let d = new Data(42);
                    let r = d.share;
                    print(r.share);
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   let _1_r = _1_d . share ;
            Output: Trace:   _1_r = shared [_1_d] Data { x: 42 }
            Output: Trace:   print(_1_r . share) ;
            Output: ----->   shared [_1_d] Data { x: 42 }
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
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
                fn main(^ self) -> Int {
                    let d = new Data(42);
                    print(d.share);
                    d.drop;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   print(_1_d . share) ;
            Output: ----->   shared [_1_d] Data { x: 42 }
            Output: Trace:   _1_d . drop ;
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
                fn main(^ self) -> Int {
                    let o = new Outer(new Inner(1));
                    print(o.share);
                    o.drop;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_o = new Outer (new Inner (1)) ;
            Output: Trace:   _1_o = Outer { inner: Inner { x: 1 } }
            Output: Trace:   print(_1_o . share) ;
            Output: ----->   shared [_1_o] Outer { inner: Inner { x: 1 } }
            Output: Trace:   _1_o . drop ;
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
                fn main(^ self) -> Outer {
                    let o = new Outer(new Inner(1));
                    o.drop;
                    o^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_o = new Outer (new Inner (1)) ;
            Output: Trace:   _1_o = Outer { inner: Inner { x: 1 } }
            Output: Trace:   _1_o . drop ;
            Output: Trace:   _1_o ^ ;
            Result: Fault: access of uninitialized value"#]]
    );
}

#[test]
fn drop_borrowed_is_noop() {
    // drop on a SharedPlace value: no-op. The value remains usable.
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Main {
                fn main(^ self) -> () {
                    let d = new Data(42);
                    let r = d.share;
                    r.drop;
                    print(r^);
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   let _1_r = _1_d . share ;
            Output: Trace:   _1_r = shared [_1_d] Data { x: 42 }
            Output: Trace:   _1_r . drop ;
            Output: Trace:   print(_1_r ^) ;
            Output: ----->   shared [_1_d] Data { x: 42 }
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

#[test]
fn drop_shared() {
    // drop on a Shared value: applies "drop shared" operation.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(^ self) -> Int {
                    let d = new Data(42);
                    let s = d^.share;
                    print(s.share);
                    s.drop;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   let _1_s = _1_d ^ . share ;
            Output: Trace:   _1_s = shared Data { x: 42 }
            Output: Trace:   print(_1_s . share) ;
            Output: ----->   shared Data { x: 42 }
            Output: Trace:   _1_s . drop ;
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
                fn main(^ self) -> Int {
                    let o = new Outer(new Inner(1));
                    let s = o^.share;
                    print(s.share);
                    s.drop;
                    0;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_o = new Outer (new Inner (1)) ;
            Output: Trace:   _1_o = Outer { inner: Inner { x: 1 } }
            Output: Trace:   let _1_s = _1_o ^ . share ;
            Output: Trace:   _1_s = shared Outer { inner: Inner { x: 1 } }
            Output: Trace:   print(_1_s . share) ;
            Output: ----->   shared Outer { inner: Inner { x: 1 } }
            Output: Trace:   _1_s . drop ;
            Output: Trace:   0 ;
            Output: Trace: exit Main.main => 0
            Result: Ok: 0
            Alloc 0x0b: [Int(0)]"#]]
    );
}

// ---------------------------------------------------------------
// share (value^.share): recursive behavior
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
                fn main(^ self) -> Outer {
                    let o = new Outer(new Inner(1));
                    o^.share;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_o = new Outer (new Inner (1)) ;
            Output: Trace:   _1_o = Outer { inner: Inner { x: 1 } }
            Output: Trace:   _1_o ^ . share ;
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
                fn main(^ self) -> Data {
                    let d = new Data(42);
                    let s = d^.share;
                    s^.share;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   let _1_s = _1_d ^ . share ;
            Output: Trace:   _1_s = shared Data { x: 42 }
            Output: Trace:   _1_s ^ . share ;
            Output: Trace: exit Main.main => shared Data { x: 42 }
            Result: Ok: shared Data { x: 42 }
            Alloc 0x07: [Int(42)]"#]]
    );
}

#[test]
fn share_borrowed_is_noop() {
    // Sharing a SharedPlace value is a no-op — it stays SharedPlace.
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Main {
                fn main(^ self) -> () {
                    let d = new Data(42);
                    let r = d.share;
                    print(r^.share);
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   let _1_r = _1_d . share ;
            Output: Trace:   _1_r = shared [_1_d] Data { x: 42 }
            Output: Trace:   print(_1_r ^ . share) ;
            Output: ----->   shared [_1_d] Data { x: 42 }
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
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
    // The inner's own flags are Given, but we traversed through SharedPlace,
    // so the effective permission should be SharedPlace — no move, source intact.
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(^ self) -> Inner {
                    let o = new Outer(new Inner(42));
                    let r = o.share;
                    let stolen = r.inner^;
                    print(stolen^);
                    // Original should still be intact since we went through a place sharing
                    o.inner^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_o = new Outer (new Inner (42)) ;
            Output: Trace:   _1_o = Outer { inner: Inner { x: 42 } }
            Output: Trace:   let _1_r = _1_o . share ;
            Output: Trace:   _1_r = shared [_1_o] Outer { inner: Inner { x: 42 } }
            Output: Trace:   let _1_stolen = _1_r . inner ^ ;
            Output: Trace:   _1_stolen = shared [_1_o] Inner { x: 42 }
            Output: Trace:   print(_1_stolen ^) ;
            Output: ----->   shared [_1_o] Inner { x: 42 }
            Output: Trace:   _1_o . inner ^ ;
            Output: Trace: exit Main.main => Inner { x: 42 }
            Result: Ok: Inner { x: 42 }
            Alloc 0x0c: [Int(42)]"#]]
    );
}

#[test]
fn ref_field_through_borrowed_path() {
    // Ref an Outer, then place sharing its inner field.
    // Traversing through SharedPlace, inner should be SharedPlace regardless of own flags.
    crate::assert_interpret!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(^ self) -> () {
                    let o = new Outer(new Inner(42));
                    let r = o.share;
                    print(r.inner.share);
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_o = new Outer (new Inner (42)) ;
            Output: Trace:   _1_o = Outer { inner: Inner { x: 42 } }
            Output: Trace:   let _1_r = _1_o . share ;
            Output: Trace:   _1_r = shared [_1_o] Outer { inner: Inner { x: 42 } }
            Output: Trace:   print(_1_r . inner . share) ;
            Output: ----->   shared [_1_o] Inner { x: 42 }
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

#[test]
fn give_field_through_shared_path() {
    // Share an Outer, then give its inner field.
    // Traversing through Shared — inner should come out Shared,
    // and giving should be repeatable (shared is duplicable).
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(^ self) -> Inner {
                    let o = new Outer(new Inner(42));
                    let s = o^.share;
                    let i1 = s.inner^;
                    let i2 = s.inner^;
                    print(i1^);
                    i2^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_o = new Outer (new Inner (42)) ;
            Output: Trace:   _1_o = Outer { inner: Inner { x: 42 } }
            Output: Trace:   let _1_s = _1_o ^ . share ;
            Output: Trace:   _1_s = shared Outer { inner: Inner { x: 42 } }
            Output: Trace:   let _1_i1 = _1_s . inner ^ ;
            Output: Trace:   _1_i1 = shared Inner { x: 42 }
            Output: Trace:   let _1_i2 = _1_s . inner ^ ;
            Output: Trace:   _1_i2 = shared Inner { x: 42 }
            Output: Trace:   print(_1_i1 ^) ;
            Output: ----->   shared Inner { x: 42 }
            Output: Trace:   _1_i2 ^ ;
            Output: Trace: exit Main.main => shared Inner { x: 42 }
            Result: Ok: shared Inner { x: 42 }
            Alloc 0x0e: [Int(42)]"#]]
    );
}

#[test]
fn shared_ref_subtype() {
    // A shared value typed as shared[p] — the system should accept it
    // (shared is subtype of place sharing) and propagate runtime Shared flags.
    crate::assert_interpret!(
        {
            class Link0 { inner: Link1; }
            class Link1 { inner: Link2; }
            class Link2 { }

            class Main {
                fn main(^ self) -> () {
                    let o = new Link0(new Link1(new Link2()));

                    // o.inner.share is shared[o] Link1 — pass through sub, get shared[o] Link2
                    let a = self.share.sub[shared[self], shared[o]](o.inner.share);
                    print(a^);

                    // x is shared Link1 — typed as shared, should propagate Shared flags
                    let x = new Link1(new Link2()).share;
                    let y = self.share.sub[shared[self], shared[o]](x^);
                    print(x^);
                    print(y^);

                    ();
                }

                fn sub[perm S, perm P](S self, link1: P Link1) -> P Link2 {
                    link1.inner^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_o = new Link0 (new Link1 (new Link2 ())) ;
            Output: Trace:   _1_o = Link0 { inner: Link1 { inner: Link2 {  } } }
            Output: Trace:   let _1_a = _1_self . share . sub [shared [_1_self], shared [_1_o]] (_1_o . inner . share) ;
            Output: Trace:   enter Main.sub
            Output: Trace:     _2_link1 . inner ^ ;
            Output: Trace:   exit Main.sub => shared [_1_o . inner] Link2 {  }
            Output: Trace:   _1_a = shared [_1_o . inner] Link2 {  }
            Output: Trace:   print(_1_a ^) ;
            Output: ----->   shared [_1_o . inner] Link2 {  }
            Output: Trace:   let _1_x = new Link1 (new Link2 ()) . share ;
            Output: Trace:   _1_x = shared Link1 { inner: Link2 {  } }
            Output: Trace:   let _1_y = _1_self . share . sub [shared [_1_self], shared [_1_o]] (_1_x ^) ;
            Output: Trace:   enter Main.sub
            Output: Trace:     _3_link1 . inner ^ ;
            Output: Trace:   exit Main.sub => shared Link2 {  }
            Output: Trace:   _1_y = shared Link2 {  }
            Output: Trace:   print(_1_x ^) ;
            Output: ----->   shared Link1 { inner: Link2 {  } }
            Output: Trace:   print(_1_y ^) ;
            Output: ----->   shared Link2 {  }
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

// ---------------------------------------------------------------
// mut: creates Lease (1-word allocation pointing at the original)
// ---------------------------------------------------------------

#[test]
fn mut_from_given() {
    // mut from a Given source: create a Lease pointing at the original.
    // The Lease dereferences through to the underlying value for display.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(^ self) -> Data {
                    let d = new Data(42);
                    let m = d!;
                    print(m^);
                    d^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   let _1_m = _1_d ! ;
            Output: Trace:   _1_m = ! [_1_d] Data { x: 42 }
            Output: Trace:   print(_1_m ^) ;
            Output: ----->   ! [_1_d] Data { x: 42 }
            Output: Trace:   _1_d ^ ;
            Output: Trace: exit Main.main => Data { x: 42 }
            Result: Ok: Data { x: 42 }
            Alloc 0x09: [Int(42)]"#]]
    );
}

#[test]
fn mut_field_read() {
    // Access a field through a Lease: dereferences the Lease,
    // then projects the field from the underlying allocation.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; y: Int; }
            class Main {
                fn main(^ self) -> Int {
                    let d = new Data(10, 20);
                    let m = d!;
                    m.y^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (10, 20) ;
            Output: Trace:   _1_d = Data { x: 10, y: 20 }
            Output: Trace:   let _1_m = _1_d ! ;
            Output: Trace:   _1_m = ! [_1_d] Data { x: 10, y: 20 }
            Output: Trace:   _1_m . y ^ ;
            Output: Trace: exit Main.main => 20
            Result: Ok: 20
            Alloc 0x08: [Int(20)]"#]]
    );
}

#[test]
fn mut_field_reassign() {
    // Reassign a field through a Lease: the change is visible
    // in the original value because Lease points at it directly.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(^ self) -> Data {
                    let d = new Data(42);
                    let m = d!;
                    m.x = 99;
                    d^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   let _1_m = _1_d ! ;
            Output: Trace:   _1_m = ! [_1_d] Data { x: 42 }
            Output: Trace:   _1_m . x = 99 ;
            Output: Trace:   _1_m . x = 99
            Output: Trace:   _1_d ^ ;
            Output: Trace: exit Main.main => Data { x: 99 }
            Result: Ok: Data { x: 99 }
            Alloc 0x09: [Int(99)]"#]]
    );
}

#[test]
fn mut_give_copies_mutref() {
    // Giving a Lease copies the Lease word into a new allocation.
    // Both the original and the copy point at the same underlying data.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(^ self) -> Data {
                    let d = new Data(42);
                    let m = d!;
                    let m2 = m^;
                    m2.x = 99;
                    d^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   let _1_m = _1_d ! ;
            Output: Trace:   _1_m = ! [_1_d] Data { x: 42 }
            Output: Trace:   let _1_m2 = _1_m ^ ;
            Output: Trace:   _1_m2 = ! [_1_d] Data { x: 42 }
            Output: Trace:   _1_m2 . x = 99 ;
            Output: Trace:   _1_m2 . x = 99
            Output: Trace:   _1_d ^ ;
            Output: Trace: exit Main.main => Data { x: 99 }
            Result: Ok: Data { x: 99 }
            Alloc 0x0b: [Int(99)]"#]]
    );
}

#[test]
fn mut_ref_through_mutref() {
    // Ref through a Lease: dereferences the Lease and copies
    // the underlying value with SharedPlace flags.
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Main {
                fn main(^ self) -> () {
                    let d = new Data(42);
                    let m = d!;
                    print(m.share);
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   let _1_m = _1_d ! ;
            Output: Trace:   _1_m = ! [_1_d] Data { x: 42 }
            Output: Trace:   print(_1_m . share) ;
            Output: ----->   shared [_1_m] ! [_1_d] Data { x: 42 }
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

#[test]
fn mut_drop() {
    // Dropping a Lease: scrubs the Lease allocation.
    // The underlying value is NOT dropped — it's still owned by the original.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(^ self) -> Data {
                    let d = new Data(42);
                    let m = d!;
                    m.drop;
                    d^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   let _1_m = _1_d ! ;
            Output: Trace:   _1_m = ! [_1_d] Data { x: 42 }
            Output: Trace:   _1_m . drop ;
            Output: Trace:   _1_d ^ ;
            Output: Trace: exit Main.main => Data { x: 42 }
            Result: Ok: Data { x: 42 }
            Alloc 0x08: [Int(42)]"#]]
    );
}

#[test]
fn mut_of_mut() {
    // Mut of mut: equivalent to give — copies the Lease word.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(^ self) -> Data {
                    let d = new Data(42);
                    let m1 = d!;
                    let m2 = m1!;
                    m2.x = 77;
                    d^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   let _1_m1 = _1_d ! ;
            Output: Trace:   _1_m1 = ! [_1_d] Data { x: 42 }
            Output: Trace:   let _1_m2 = _1_m1 ! ;
            Output: Trace:   _1_m2 = ! [_1_m1] ! [_1_d] Data { x: 42 }
            Output: Trace:   _1_m2 . x = 77 ;
            Output: Trace:   _1_m2 . x = 77
            Output: Trace:   _1_d ^ ;
            Output: Trace: exit Main.main => Data { x: 77 }
            Result: Ok: Data { x: 77 }
            Alloc 0x0b: [Int(77)]"#]]
    );
}

#[test]
fn mut_nested_field_reassign() {
    // Reassign a nested field through a Lease.
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(^ self) -> Outer {
                    let o = new Outer(new Inner(1));
                    let m = o!;
                    m.inner.x = 42;
                    o^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_o = new Outer (new Inner (1)) ;
            Output: Trace:   _1_o = Outer { inner: Inner { x: 1 } }
            Output: Trace:   let _1_m = _1_o ! ;
            Output: Trace:   _1_m = ! [_1_o] Outer { inner: Inner { x: 1 } }
            Output: Trace:   _1_m . inner . x = 42 ;
            Output: Trace:   _1_m . inner . x = 42
            Output: Trace:   _1_o ^ ;
            Output: Trace: exit Main.main => Outer { inner: Inner { x: 42 } }
            Result: Ok: Outer { inner: Inner { x: 42 } }
            Alloc 0x0a: [Int(42)]"#]]
    );
}

// ---------------------------------------------------------------
// mut: field-path tests (a.b! — mut of a field, not a variable)
// ---------------------------------------------------------------

#[test]
fn mut_field_of_given() {
    // Mut a field of a Given object: creates a Lease pointing
    // into the original allocation at the field's offset.
    // Reassigning through the Lease modifies the original.
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(^ self) -> Outer {
                    let o = new Outer(new Inner(1));
                    let m = o.inner!;
                    m.x = 99;
                    o^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_o = new Outer (new Inner (1)) ;
            Output: Trace:   _1_o = Outer { inner: Inner { x: 1 } }
            Output: Trace:   let _1_m = _1_o . inner ! ;
            Output: Trace:   _1_m = ! [_1_o . inner] Inner { x: 1 }
            Output: Trace:   _1_m . x = 99 ;
            Output: Trace:   _1_m . x = 99
            Output: Trace:   _1_o ^ ;
            Output: Trace: exit Main.main => Outer { inner: Inner { x: 99 } }
            Result: Ok: Outer { inner: Inner { x: 99 } }
            Alloc 0x0a: [Int(99)]"#]]
    );
}

#[test]
fn mut_field_of_given_read() {
    // Read a field through a Lease to a field of a Given object.
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; y: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(^ self) -> Int {
                    let o = new Outer(new Inner(10, 20));
                    let m = o.inner!;
                    m.y^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_o = new Outer (new Inner (10, 20)) ;
            Output: Trace:   _1_o = Outer { inner: Inner { x: 10, y: 20 } }
            Output: Trace:   let _1_m = _1_o . inner ! ;
            Output: Trace:   _1_m = ! [_1_o . inner] Inner { x: 10, y: 20 }
            Output: Trace:   _1_m . y ^ ;
            Output: Trace: exit Main.main => 20
            Result: Ok: 20
            Alloc 0x09: [Int(20)]"#]]
    );
}

#[test]
fn mut_field_of_given_drop() {
    // Dropping a Lease to a field: scrubs the Lease allocation,
    // original field untouched.
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(^ self) -> Outer {
                    let o = new Outer(new Inner(42));
                    let m = o.inner!;
                    m.drop;
                    o^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_o = new Outer (new Inner (42)) ;
            Output: Trace:   _1_o = Outer { inner: Inner { x: 42 } }
            Output: Trace:   let _1_m = _1_o . inner ! ;
            Output: Trace:   _1_m = ! [_1_o . inner] Inner { x: 42 }
            Output: Trace:   _1_m . drop ;
            Output: Trace:   _1_o ^ ;
            Output: Trace: exit Main.main => Outer { inner: Inner { x: 42 } }
            Result: Ok: Outer { inner: Inner { x: 42 } }
            Alloc 0x09: [Int(42)]"#]]
    );
}

#[test]
fn mut_field_through_mut() {
    // a! then m.inner!: the inner ! traverses through the
    // outer Lease dereference, then creates a new Lease pointing
    // at the inner field of the original allocation.
    crate::assert_interpret_only!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(^ self) -> Outer {
                    let o = new Outer(new Inner(1));
                    let m = o!;
                    let m2 = m.inner!;
                    m2.x = 55;
                    o^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_o = new Outer (new Inner (1)) ;
            Output: Trace:   _1_o = Outer { inner: Inner { x: 1 } }
            Output: Trace:   let _1_m = _1_o ! ;
            Output: Trace:   _1_m = ! [_1_o] Outer { inner: Inner { x: 1 } }
            Output: Trace:   let _1_m2 = _1_m . inner ! ;
            Output: Trace:   _1_m2 = ! [_1_m . inner] ! [_1_o] Inner { x: 1 }
            Output: Trace:   _1_m2 . x = 55 ;
            Output: Trace:   _1_m2 . x = 55
            Output: Trace:   _1_o ^ ;
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
                fn main(^ self) -> Inner {
                    let o = new Outer(new Inner(1));
                    let s = o^.share;
                    s.inner!;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_o = new Outer (new Inner (1)) ;
            Output: Trace:   _1_o = Outer { inner: Inner { x: 1 } }
            Output: Trace:   let _1_s = _1_o ^ . share ;
            Output: Trace:   _1_s = shared Outer { inner: Inner { x: 1 } }
            Output: Trace:   _1_s . inner ! ;
            Result: Fault: cannot take mutable reference to shared value
            Alloc 0x06: [Int(1)]"#]]
    );
}

#[test]
fn mut_field_through_ref() {
    // Mut of a field reached through a SharedPlace (place sharing) object.
    // resolve_place sets effective=SharedPlace when crossing the place sharing perm.
    // SharedPlace means read-only — cannot take a mutable reference through it,
    // just like shared.
    crate::assert_interpret_fault!(
        {
            class Inner { x: Int; }
            class Outer { inner: Inner; }
            class Main {
                fn main(^ self) -> Inner {
                    let o = new Outer(new Inner(1));
                    let r = o.share;
                    r.inner!;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_o = new Outer (new Inner (1)) ;
            Output: Trace:   _1_o = Outer { inner: Inner { x: 1 } }
            Output: Trace:   let _1_r = _1_o . share ;
            Output: Trace:   _1_r = shared [_1_o] Outer { inner: Inner { x: 1 } }
            Output: Trace:   _1_r . inner ! ;
            Result: Fault: cannot take mutable reference to borrowed value
            Alloc 0x04: [Int(1)]
            Alloc 0x06: [Int(1)]"#]]
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
                fn main(^ self) -> Inner {
                    let o = new Outer(new Inner(1));
                    let stolen = o.inner^;
                    o.inner!;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_o = new Outer (new Inner (1)) ;
            Output: Trace:   _1_o = Outer { inner: Inner { x: 1 } }
            Output: Trace:   let _1_stolen = _1_o . inner ^ ;
            Output: Trace:   _1_stolen = Inner { x: 1 }
            Output: Trace:   _1_o . inner ! ;
            Result: Fault: access of uninitialized value
            Alloc 0x06: [Int(1)]"#]]
    );
}

// ---------------------------------------------------------------
// mut: error cases
// ---------------------------------------------------------------

#[test]
fn mut_of_shared_faults() {
    // Cannot take a mut place sharing of a shared value.
    crate::assert_interpret_fault!(
        {
            class Data { x: Int; }
            class Main {
                fn main(^ self) -> Data {
                    let d = new Data(42);
                    let s = d^.share;
                    s!;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   let _1_s = _1_d ^ . share ;
            Output: Trace:   _1_s = shared Data { x: 42 }
            Output: Trace:   _1_s ! ;
            Result: Fault: cannot take mutable reference to shared value
            Alloc 0x05: [Int(42)]"#]]
    );
}

#[test]
fn mut_of_uninitialized_faults() {
    // Cannot take a mut place sharing of a dropped value.
    crate::assert_interpret_fault!(
        {
            class Data { x: Int; }
            class Main {
                fn main(^ self) -> Data {
                    let d = new Data(42);
                    d.drop;
                    d!;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   _1_d . drop ;
            Output: Trace:   _1_d ! ;
            Result: Fault: access of uninitialized value"#]]
    );
}

#[test]
fn mut_of_copy_type_faults() {
    // Cannot take a mut place sharing of a copy type (no flags).
    crate::assert_interpret_fault!(
        {
            class Main {
                fn main(^ self) -> Int {
                    let x = 42;
                    x!;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_x = 42 ;
            Output: Trace:   _1_x = 42
            Output: Trace:   _1_x ! ;
            Result: Fault: cannot take mutable reference to shared value
            Alloc 0x02: [Int(42)]"#]]
    );
}

// ---------------------------------------------------------------
// mut: array interaction
// ---------------------------------------------------------------

#[test]
fn mut_of_array_create_and_drop() {
    // Create a Lease to a Given array, drop the Lease, verify original intact.
    // Note: array operations (array_give, array_write) cannot currently
    // accept a Lease directly — they expect a proper array TypedValue
    // (2-word layout). A Lease^ produces a 1-word Lease allocation.
    // Lease+array interaction requires method calls (mut self) or
    // teaching array ops to dereference through Lease.
    crate::assert_interpret_only!(
        {
            class Data { x: Int; }
            class Main {
                fn main(^ self) -> Int {
                    let a = array_new[Data](2);
                    let m = a!;
                    m.drop;
                    array_capacity[Data, ^](a^);
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_a = array_new [Data](2) ;
            Output: Trace:   _1_a = Array { flag: Given, rc: 1, Data { x: ⚡ }, Data { x: ⚡ } }
            Output: Trace:   let _1_m = _1_a ! ;
            Output: Trace:   _1_m = ! [_1_a] <unexpected: RefCount(1)>
            Output: Trace:   _1_m . drop ;
            Output: Trace:   array_capacity [Data, ^](_1_a ^) ;
            Output: Trace: exit Main.main => 2
            Result: Ok: 2
            Alloc 0x0a: [Int(2)]"#]]
    );
}

// ---------------------------------------------------------------
// mut: dangling Lease (UB — type system should prevent)
// ---------------------------------------------------------------

#[test]
fn mut_dangling_after_give() {
    // UB test: create a Lease to d, then move d away.
    // The original allocation is now uninitialized. The Lease
    // still points at it. resolve_place_to_object dereferences
    // through the Lease and finds uninitialized data, so the
    // give faults. The type system prevents this in well-typed programs.
    crate::assert_interpret_fault!(
        {
            class Data { x: Int; }
            class Main {
                fn main(^ self) -> Data {
                    let d = new Data(42);
                    let m = d!;
                    let stolen = d^;
                    m^;
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   let _1_m = _1_d ! ;
            Output: Trace:   _1_m = ! [_1_d] Data { x: 42 }
            Output: Trace:   let _1_stolen = _1_d ^ ;
            Output: Trace:   _1_stolen = Data { x: 42 }
            Output: Trace:   _1_m ^ ;
            Result: Fault: access of uninitialized value
            Alloc 0x05: [Lease(0x03)]
            Alloc 0x07: [Int(42)]"#]]
    );
}
