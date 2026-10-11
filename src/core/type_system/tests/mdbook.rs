/// Tests extracted from the mdbook chapters.
/// Each test is wrapped in ANCHOR comments so the mdbook-judgment
/// preprocessor can include them in the rendered book.

// =========================================================================
// Chapter: Classes
// =========================================================================

#[test]
fn classes_point_example() {
    // ANCHOR: classes_point_example
    crate::assert_ok!(
        {
            class Point {
                x: Int;
                y: Int;
            }

            class Main {
                fn test(^ self) -> Int {
                    let p = new Point(22, 44);
                    p.x^;
                }
            }
        }
    );
    // ANCHOR_END: classes_point_example
}

// =========================================================================
// Chapter: A simple function
// =========================================================================

#[test]
fn simple_function_example() {
    // ANCHOR: simple_function_example
    crate::assert_ok!(
        {
            class Point {
                x: Int;
                y: Int;
            }

            class Main {
                fn test(^ self) -> Int {
                    let p = new Point(22, 44);
                    0;
                }
            }
        }
    );
    // ANCHOR_END: simple_function_example
}

// =========================================================================
// Chapter: Giving
// =========================================================================

#[test]
fn giving_a_value() {
    // ANCHOR: giving_a_value
    crate::assert_ok!(
        {
            class Data { }

            class Main {
                fn test(^ self) -> Data {
                    let d = new Data();
                    d^;
                }
            }
        }
    );
    // ANCHOR_END: giving_a_value
}

#[test]
fn giving_a_value_twice_is_error() {
    // ANCHOR: giving_a_value_twice_is_error
    crate::assert_err!(
        {
            class Data { }

            class Main {
                fn test(^ self) -> Data {
                    let d = new Data();
                    d^;
                    d^;
                }
            }
        },
        expect_test::expect![[r#"
            the rule "give" at (expressions.rs) failed because
              condition evaluted to false: `!live_after.is_live(place)`
                live_after = LivePlaces { accessed: {d}, traversed: {} }
                place = d"#]]
    );
    // ANCHOR_END: giving_a_value_twice_is_error
}

#[test]
fn giving_a_field() {
    // ANCHOR: giving_a_field
    crate::assert_ok!(
        {
            class Data { }

            class Pair {
                a: Data;
                b: Data;
            }

            class Main {
                fn test(^ self) -> Data {
                    let p = new Pair(new Data(), new Data());
                    p.a^;
                    p.b^;
                }
            }
        }
    );
    // ANCHOR_END: giving_a_field
}

#[test]
fn giving_field_then_whole_is_error() {
    // ANCHOR: giving_field_then_whole_is_error
    crate::assert_err!(
        {
            class Data { }

            class Pair {
                a: Data;
                b: Data;
            }

            class Main {
                fn test(^ self) -> Pair {
                    let p = new Pair(new Data(), new Data());
                    p.a^;
                    p^;
                }
            }
        },
        expect_test::expect![[r#"
            the rule "give" at (expressions.rs) failed because
              condition evaluted to false: `!live_after.is_live(place)`
                live_after = LivePlaces { accessed: {p}, traversed: {} }
                place = p . a"#]]
    );
    // ANCHOR_END: giving_field_then_whole_is_error
}

#[test]
fn giving_whole_then_field_is_error() {
    // ANCHOR: giving_whole_then_field_is_error
    crate::assert_err!(
        {
            class Data { }

            class Pair {
                a: Data;
                b: Data;
            }

            class Main {
                fn test(^ self) -> Data {
                    let p = new Pair(new Data(), new Data());
                    p^;
                    p.a^;
                }
            }
        },
        expect_test::expect![[r#"
            the rule "give" at (expressions.rs) failed because
              condition evaluted to false: `!live_after.is_live(place)`
                live_after = LivePlaces { accessed: {p . a}, traversed: {} }
                place = p"#]]
    );
    // ANCHOR_END: giving_whole_then_field_is_error
}

#[test]
fn shared_classes_are_copyable() {
    // ANCHOR: shared_classes_are_copyable
    crate::assert_ok!(
        {
            class Main {
                fn test(^ self) -> Int {
                    let x = 22;
                    x^;
                    x^;
                }
            }
        }
    );
    // ANCHOR_END: shared_classes_are_copyable
}

// =========================================================================
// Chapter: Sharing
// =========================================================================

#[test]
fn sharing_a_value() {
    // ANCHOR: sharing_a_value
    crate::assert_ok!(
        {
            class Data { }

            class Main {
                fn test(^ self) -> shared Data {
                    let d = new Data();
                    let s = d^.share;
                    s^;
                    s^;
                }
            }
        }
    );
    // ANCHOR_END: sharing_a_value
}

#[test]
fn shared_classes_always_shared() {
    // ANCHOR: shared_classes_always_shared
    crate::assert_ok!(
        {
            shared class Point {
                x: Int;
                y: Int;
            }

            class Main {
                fn test(^ self) -> Point {
                    let p = new Point(22, 44);
                    p^;
                    p^;
                }
            }
        }
    );
    // ANCHOR_END: shared_classes_always_shared
}

#[test]
fn given_classes_cannot_be_shared() {
    // ANCHOR: given_classes_cannot_be_shared
    crate::assert_err!(
        {
            given class Resource { }

            class Main {
                fn test(^ self) -> shared Resource {
                    let r = new Resource();
                    r^.share;
                }
            }
        },
        expect_test::expect![[r#"
            the rule "share class" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]
    );
    // ANCHOR_END: given_classes_cannot_be_shared
}

#[test]
fn sharing_is_idempotent() {
    // ANCHOR: sharing_is_idempotent
    crate::assert_ok!(
        {
            class Data { }

            class Main {
                fn test(^ self) -> shared Data {
                    let d = new Data();
                    d^.share.share;
                }
            }
        }
    );
    // ANCHOR_END: sharing_is_idempotent
}

// =========================================================================
// Chapter: Borrowing
// =========================================================================

#[test]
fn simple_borrow() {
    // ANCHOR: simple_borrow
    crate::assert_ok!(
        {
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn test(^ self) {
                    let foo = new Foo(new Data());
                    let bar = foo.ref;
                    let i = foo.i.ref;
                    bar^;
                    ();
                }
            }
        }
    );
    // ANCHOR_END: simple_borrow
}

#[test]
fn mutation_through_ref_is_error() {
    // ANCHOR: mutation_through_ref_is_error
    crate::assert_err!(
        {
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn test(^ self) {
                    let foo = new Foo(new Data());
                    let bar = foo.ref;
                    let i = foo.i!;
                    bar^;
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            the rule "share-mutation" at (accesses.rs) failed because
              condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
                accessed_place = foo . i
                shared_place = foo"#]]
    );
    // ANCHOR_END: mutation_through_ref_is_error
}

#[test]
fn giving_field_while_refd_is_error() {
    // ANCHOR: giving_field_while_refd_is_error
    crate::assert_err!(
        {
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn test(^ self) {
                    let foo = new Foo(new Data());
                    let bar = foo.ref;
                    let i = foo.i^;
                    bar^;
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            the rule "share-give" at (accesses.rs) failed because
              condition evaluted to false: `place_disjoint_from_or_prefix_of(accessed_place, shared_place)`
                accessed_place = foo . i
                shared_place = foo"#]]
    );
    // ANCHOR_END: giving_field_while_refd_is_error
}

#[test]
fn liveness_cancels_restrictions() {
    // ANCHOR: liveness_cancels_restrictions
    crate::assert_ok!(
        {
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn test(^ self) {
                    let foo = new Foo(new Data());
                    let bar = foo!;
                    let i = foo.i.ref;
                    ();
                }
            }
        }
    );
    // ANCHOR_END: liveness_cancels_restrictions
}

#[test]
fn mut_borrow_blocks_read() {
    // ANCHOR: mut_borrow_blocks_read
    crate::assert_err!(
        {
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn test(^ self) {
                    let foo = new Foo(new Data());
                    let bar = foo!;
                    let i = foo.i.ref;
                    bar^;
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            the rule "lease-mutation" at (accesses.rs) failed because
              condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
                accessed_place = foo . i
                leased_place = foo"#]]
    );
    // ANCHOR_END: mut_borrow_blocks_read
}

#[test]
fn disjoint_access_is_fine() {
    // ANCHOR: disjoint_access_is_fine
    crate::assert_ok!(
        {
            class Data { }

            class Main {
                fn test(^ self) {
                    let foo = new Data();
                    let other = new Data();
                    let bar = foo.ref;
                    other^;
                    bar^;
                    ();
                }
            }
        }
    );
    // ANCHOR_END: disjoint_access_is_fine
}

#[test]
fn transitive_restrictions() {
    // ANCHOR: transitive_restrictions
    crate::assert_err!(
        {
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn test(^ self) {
                    let p = new Foo(new Data());
                    let q = p!;
                    let r = q.ref;
                    let i = p.i.ref;
                    r^;
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            the rule "lease-mutation" at (accesses.rs) failed because
              condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
                accessed_place = p . i
                leased_place = p"#]]
    );
    // ANCHOR_END: transitive_restrictions
}

// =========================================================================
// Chapter: Subtyping
// =========================================================================

#[test]
fn subtyping_given_invisible() {
    // ANCHOR: subtyping_given_invisible
    crate::assert_ok!(
        {
            class Data { }

            class Main {
                fn test(^ self) -> Data {
                    let d: ^ Data = new Data();
                    d^;
                }
            }
        }
    );
    // ANCHOR_END: subtyping_given_invisible
}

#[test]
fn subtyping_ref_composition_given() {
    // ANCHOR: subtyping_ref_composition_given
    crate::assert_ok!(
        {
            class Data { }

            class Main {
                fn test(^ self, d: ^ Data) -> shared[d] Data {
                    d.ref;
                }
            }
        }
    );
    // ANCHOR_END: subtyping_ref_composition_given
}

#[test]
fn subtyping_field_through_ref() {
    // ANCHOR: subtyping_field_through_ref
    crate::assert_ok!(
        {
            class Inner { }

            class Outer {
                i: Inner;
            }

            class Main {
                fn test(^ self, d: ^ Outer) -> shared[d] Inner {
                    let r: shared[d] Outer = d.ref;
                    r.i^;
                }
            }
        }
    );
    // ANCHOR_END: subtyping_field_through_ref
}

#[test]
fn subtyping_ref_shared_absorbs() {
    // ANCHOR: subtyping_ref_shared_absorbs
    crate::assert_ok!(
        {
            shared class Point {
                x: Int;
                y: Int;
            }

            class Wrapper {
                p: Point;
            }

            class Main {
                fn test(^ self, w: ^ Wrapper) -> Point {
                    let r: shared[w] Wrapper = w.ref;
                    r.p^;
                }
            }
        }
    );
    // ANCHOR_END: subtyping_ref_shared_absorbs
}

#[test]
fn subtyping_ref_through_mut() {
    // ANCHOR: subtyping_ref_through_mut
    crate::assert_ok!(
        {
            class Data { }

            class Main {
                fn test(^ self) {
                    let d: ^ Data = new Data();
                    let p: ![d] Data = d!;
                    let q: shared[p] ![d] Data = p.ref;
                    ();
                }
            }
        }
    );
    // ANCHOR_END: subtyping_ref_through_mut
}

#[test]
fn subtyping_motivating_example() {
    // ANCHOR: subtyping_motivating_example
    crate::assert_ok!(
        {
            class Data { }

            class Main {
                fn test(^ self) -> shared[self] Data {
                    let d: shared Data = new Data().share;
                    d^;
                }
            }
        }
    );
    // ANCHOR_END: subtyping_motivating_example
}

#[test]
fn subtyping_narrower_ref() {
    // ANCHOR: subtyping_narrower_ref
    crate::assert_ok!(
        {
            class Data { }

            class Main {
                fn test(^ self, d1: ^ Data, d2: ^ Data) -> shared[d1, d2] Data {
                    d1.ref;
                }
            }
        }
    );
    // ANCHOR_END: subtyping_narrower_ref
}

#[test]
fn subtyping_different_classes_fail() {
    // ANCHOR: subtyping_different_classes_fail
    crate::assert_err!(
        {
            class Foo { }
            class Bar { }

            class Main {
                fn test(^ self) {
                    let f = new Foo();
                    let b: Bar = f^;
                    ();
                }
            }
        },
        expect_test::expect!["judgment had no applicable rules: `check_program { program: class Foo { } class Bar { } class Main { fn test (^ self) -> () { let f = new Foo () ; let b : Bar = f ^ ; () ; } } }`"]
    );
    // ANCHOR_END: subtyping_different_classes_fail
}

#[test]
fn subtyping_narrowing_ref_fails() {
    // ANCHOR: subtyping_narrowing_ref_fails
    crate::assert_err!(
        {
            class Data { }

            class Main {
                fn test(^ self, d1: ^ Data, d2: ^ Data) -> shared[d1] Data {
                    let r: shared[d1, d2] Data = d1.ref;
                    r^;
                }
            }
        },
        expect_test::expect![[r#"
            the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(place_a)`
                place_b = d1
                place_a = d2"#]]
    );
    // ANCHOR_END: subtyping_narrowing_ref_fails
}

#[test]
fn subtyping_perm_erasure_ref_int() {
    // ANCHOR: subtyping_perm_erasure_ref_int
    crate::assert_ok!(
        {
            class Main {
                fn test(^ self) -> Int {
                    let x: shared[self] Int = 0;
                    x^;
                }
            }
        }
    );
    // ANCHOR_END: subtyping_perm_erasure_ref_int
}

#[test]
fn subtyping_perm_erasure_int_to_ref() {
    // ANCHOR: subtyping_perm_erasure_int_to_ref
    crate::assert_ok!(
        {
            class Main {
                fn test(^ self) -> Int {
                    let x: Int = 0;
                    let y: shared[self] Int = x^;
                    y^;
                }
            }
        }
    );
    // ANCHOR_END: subtyping_perm_erasure_int_to_ref
}

#[test]
fn subtyping_shared_class_copy_params() {
    // ANCHOR: subtyping_shared_class_copy_params
    crate::assert_ok!(
        {
            shared class Point {
                x: Int;
                y: Int;
            }

            class Main {
                fn test(^ self) -> Point {
                    let p: shared Point = new Point(1, 2);
                    p^;
                }
            }
        }
    );
    // ANCHOR_END: subtyping_shared_class_copy_params
}

#[test]
fn subtyping_non_copy_params_block_erasure() {
    // ANCHOR: subtyping_non_copy_params_block_erasure
    crate::assert_err!(
        {
            shared class Box[ty T] {
                value: T;
            }

            class Data { }

            class Main {
                fn test(^ self, d: ^ Data) -> Box[Data] {
                    let b: shared[d] Box[Data] = new Box[Data](new Data());
                    b^;
                }
            }
        },
        expect_test::expect!["judgment had no applicable rules: `check_program { program: shared class Box [ty] { value : ^ty0_0 ; } class Data { } class Main { fn test (^ self d : ^ Data) -> Box[Data] { let b : shared [d] Box[Data] = new Box [Data] (new Data ()) ; b ^ ; } } }`"]
    );
    // ANCHOR_END: subtyping_non_copy_params_block_erasure
}

#[test]
fn subtyping_place_refinement() {
    // ANCHOR: subtyping_place_refinement
    crate::assert_ok!(
        {
            class Data {
                left: ^ Data;
                right: ^ Data;
            }

            class Main {
                fn test(^ self, d: ^ Data) -> shared[d] Data {
                    d.left.ref;
                }
            }
        }
    );
    // ANCHOR_END: subtyping_place_refinement
}

#[test]
fn subtyping_place_refinement_reverse_fails() {
    // ANCHOR: subtyping_place_refinement_reverse_fails
    crate::assert_err!(
        {
            class Data {
                left: ^ Data;
                right: ^ Data;
            }

            class Main {
                fn test(^ self, d: ^ Data) -> shared[d.left] Data {
                    d.ref;
                }
            }
        },
        expect_test::expect![[r#"
            the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(place_a)`
                place_b = d . left
                place_a = d"#]]
    );
    // ANCHOR_END: subtyping_place_refinement_reverse_fails
}

// =========================================================================
// Chapter: Subtypes and subpermissions — Copy permissions
// =========================================================================

#[test]
fn copy_perm_shared_subtype_ref() {
    // ANCHOR: copy_perm_shared_subtype_ref
    crate::assert_ok!(
        {
            class Data { }

            class Main {
                fn test(^ self, d: ^ Data) {
                    let s: shared Data = new Data().share;
                    let r: shared[d] Data = s^;
                    ();
                }
            }
        }
    );
    // ANCHOR_END: copy_perm_shared_subtype_ref
}

#[test]
fn copy_perm_ref_not_subtype_shared() {
    // ANCHOR: copy_perm_ref_not_subtype_shared
    crate::assert_err!(
        {
            class Data { }

            class Main {
                fn test(^ self, d: ^ Data) {
                    let r: shared[d] Data = d.ref;
                    let s: shared Data = r^;
                    ();
                }
            }
        },
        expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { } class Main { fn test (^ self d : ^ Data) -> () { let r : shared [d] Data = d . ref ; let s : shared Data = r ^ ; () ; } } }`"]
    );
    // ANCHOR_END: copy_perm_ref_not_subtype_shared
}

#[test]
fn copy_perm_shared_subtype_shared_mut() {
    // ANCHOR: copy_perm_shared_subtype_shared_mut
    crate::assert_ok!(
        {
            class Data { }

            class Main {
                fn test(^ self, d: ^ Data) {
                    let s: shared Data = new Data().share;
                    let r: shared ![d] Data = s^;
                    ();
                }
            }
        }
    );
    // ANCHOR_END: copy_perm_shared_subtype_shared_mut
}

#[test]
fn copy_perm_ref_subtype_shared_mut() {
    // ANCHOR: copy_perm_ref_subtype_shared_mut
    crate::assert_ok!(
        {
            class Data { }

            class Main {
                fn test(^ self, d: ^ Data) {
                    let r: shared[d] Data = d.ref;
                    let sm: shared ![d] Data = r^;
                    ();
                }
            }
        }
    );
    // ANCHOR_END: copy_perm_ref_subtype_shared_mut
}

#[test]
fn copy_perm_shared_mut_not_subtype_ref() {
    // ANCHOR: copy_perm_shared_mut_not_subtype_ref
    crate::assert_err!(
        {
            class Data { }

            class Main {
                fn test(^ self, d: ^ Data) {
                    let p: ![d] Data = d!;
                    let sm: shared ![d] Data = p.ref;
                    let r: shared[d] Data = sm^;
                    ();
                }
            }
        },
        expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { } class Main { fn test (^ self d : ^ Data) -> () { let p : ! [d] Data = d ! ; let sm : shared ! [d] Data = p . ref ; let r : shared [d] Data = sm ^ ; () ; } } }`"]
    );
    // ANCHOR_END: copy_perm_shared_mut_not_subtype_ref
}

#[test]
fn copy_perm_ref_shared_absorbs() {
    // ANCHOR: copy_perm_ref_shared_absorbs
    crate::assert_ok!(
        {
            class Data { }

            class Main {
                fn test(^ self) {
                    let d: shared Data = new Data().share;
                    let r = d.ref;
                    let s: shared Data = r^;
                    ();
                }
            }
        }
    );
    // ANCHOR_END: copy_perm_ref_shared_absorbs
}

#[test]
fn copy_perm_ref_mut_composes() {
    // ANCHOR: copy_perm_ref_mut_composes
    crate::assert_ok!(
        {
            class Data { }

            class Main {
                fn test(^ self) {
                    let d: ^ Data = new Data();
                    let p: ![d] Data = d!;
                    let q: shared[p] ![d] Data = p.ref;
                    ();
                }
            }
        }
    );
    // ANCHOR_END: copy_perm_ref_mut_composes
}

#[test]
fn copy_perm_mut_not_subtype_ref() {
    // ANCHOR: copy_perm_mut_not_subtype_ref
    crate::assert_err!(
        {
            class Data { }

            class Main {
                fn test(^ self, d: ^ Data) {
                    let p: ![d] Data = d!;
                    let q: shared[d] Data = p^;
                    ();
                }
            }
        },
        expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { } class Main { fn test (^ self d : ^ Data) -> () { let p : ! [d] Data = d ! ; let q : shared [d] Data = p ^ ; () ; } } }`"]
    );
    // ANCHOR_END: copy_perm_mut_not_subtype_ref
}

#[test]
fn copy_perm_given_not_subtype_shared() {
    // ANCHOR: copy_perm_given_not_subtype_shared
    crate::assert_err!(
        {
            class Data { }

            class Main {
                fn test(^ self, d: ^ Data) {
                    let s: shared Data = d^;
                    ();
                }
            }
        },
        expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { } class Main { fn test (^ self d : ^ Data) -> () { let s : shared Data = d ^ ; () ; } } }`"]
    );
    // ANCHOR_END: copy_perm_given_not_subtype_shared
}

// =========================================================================
// Chapter: Subtypes and subpermissions — Place ordering
// =========================================================================

#[test]
fn place_ordering_ref_subplace() {
    // ANCHOR: place_ordering_ref_subplace
    crate::assert_ok!(
        {
            class Data {
                left: ^ Data;
                right: ^ Data;
            }

            class Main {
                fn test(^ self, d: ^ Data) {
                    let r: shared[d] Data = d.left.ref;
                    ();
                }
            }
        }
    );
    // ANCHOR_END: place_ordering_ref_subplace
}

#[test]
fn place_ordering_mut_subplace() {
    // ANCHOR: place_ordering_mut_subplace
    crate::assert_ok!(
        {
            class Data {
                left: ^ Data;
                right: ^ Data;
            }

            class Main {
                fn test(^ self, d: ^ Data) {
                    let r: ![d] Data = d.left!;
                    ();
                }
            }
        }
    );
    // ANCHOR_END: place_ordering_mut_subplace
}

#[test]
fn place_ordering_reverse_fails() {
    // ANCHOR: place_ordering_reverse_fails
    crate::assert_err!(
        {
            class Data {
                left: ^ Data;
                right: ^ Data;
            }

            class Main {
                fn test(^ self, d: ^ Data) {
                    let r: shared[d.left] Data = d.ref;
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(place_a)`
                place_b = d . left
                place_a = d"#]]
    );
    // ANCHOR_END: place_ordering_reverse_fails
}

#[test]
fn place_ordering_set_subset() {
    // ANCHOR: place_ordering_set_subset
    crate::assert_ok!(
        {
            class Data { }

            class Main {
                fn test(^ self, d1: ^ Data, d2: ^ Data) {
                    let r: shared[d1, d2] Data = d1.ref;
                    ();
                }
            }
        }
    );
    // ANCHOR_END: place_ordering_set_subset
}

#[test]
fn place_ordering_dropping_source_fails() {
    // ANCHOR: place_ordering_dropping_source_fails
    crate::assert_err!(
        {
            class Data { }

            class Main {
                fn test(^ self, d1: ^ Data, d2: ^ Data) {
                    let r: shared[d1, d2] Data = d1.ref;
                    let s: shared[d1] Data = r^;
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(place_a)`
                place_b = d1
                place_a = d2"#]]
    );
    // ANCHOR_END: place_ordering_dropping_source_fails
}

#[test]
fn place_ordering_both_dimensions() {
    // ANCHOR: place_ordering_both_dimensions
    crate::assert_ok!(
        {
            class Data {
                left: ^ Data;
                right: ^ Data;
            }

            class Main {
                fn test(^ self, d: ^ Data) {
                    let r: shared[d.left, d.right] Data = d.left.ref;
                    let s: shared[d] Data = r^;
                    ();
                }
            }
        }
    );
    // ANCHOR_END: place_ordering_both_dimensions
}

#[test]
fn place_ordering_both_dimensions_mut() {
    // ANCHOR: place_ordering_both_dimensions_mut
    crate::assert_ok!(
        {
            class Data {
                left: ^ Data;
                right: ^ Data;
            }

            class Main {
                fn test(^ self, d: ^ Data) {
                    let r: ![d.left, d.right] Data = d.left!;
                    let s: ![d] Data = r^;
                    ();
                }
            }
        }
    );
    // ANCHOR_END: place_ordering_both_dimensions_mut
}

// =========================================================================
// Chapter: Subtypes and subpermissions — Liveness and cancellation
// =========================================================================

#[test]
fn liveness_dead_mut_cancels() {
    // ANCHOR: liveness_dead_mut_cancels
    crate::assert_ok!(
        {
            class Data { }

            class Main {
                fn test(^ self) {
                    let d = new Data();
                    let p: ![d] Data = d!;
                    let q: ![p] Data = p!;
                    let r: ![d] Data = q^;
                    ();
                }
            }
        }
    );
    // ANCHOR_END: liveness_dead_mut_cancels
}

#[test]
fn liveness_live_mut_no_cancel() {
    // ANCHOR: liveness_live_mut_no_cancel
    crate::assert_err!(
        {
            class Data {
                fn read[perm P](P self) { (); }
            }

            class Main {
                fn test(^ self) {
                    let d = new Data();
                    let p: ![d] Data = d!;
                    let q: ![p] Data = p!;
                    let r: ![d] Data = q^;
                    p^.read[![d]]();
                }
            }
        },
        expect_test::expect![[r#"
            the rule "(mut::P) vs (mut::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(place_a)`
                place_b = d
                place_a = p"#]]
    );
    // ANCHOR_END: liveness_live_mut_no_cancel
}

#[test]
fn liveness_dead_ref_promotes() {
    // ANCHOR: liveness_dead_ref_promotes
    crate::assert_ok!(
        {
            class Data { }

            class Main {
                fn test(^ self) {
                    let d = new Data();
                    let p: ![d] Data = d!;
                    let q: shared[p] Data = p.ref;
                    let r: shared ![d] Data = q^;
                    ();
                }
            }
        }
    );
    // ANCHOR_END: liveness_dead_ref_promotes
}

#[test]
fn liveness_live_ref_no_promote() {
    // ANCHOR: liveness_live_ref_no_promote
    crate::assert_err!(
        {
            class Data {
                fn read[perm P](P self) { (); }
            }

            class Main {
                fn test(^ self) {
                    let d = new Data();
                    let p: ![d] Data = d!;
                    let q: shared[p] Data = p.ref;
                    let r: shared ![d] Data = q^;
                    p^.read[![d]]();
                }
            }
        },
        expect_test::expect![[r#"
            the rule "(ref::P) vs (shared::mut::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(place_a)`
                place_b = d
                place_a = p"#]]
    );
    // ANCHOR_END: liveness_live_ref_no_promote
}

#[test]
fn liveness_return_cancels() {
    // ANCHOR: liveness_return_cancels
    crate::assert_ok!(
        {
            class Data { }

            class Main {
                fn reborrow(^ self, d: ![self] Data) -> ![self] Data {
                    let p: ![d] Data = d!;
                    p^;
                }
            }
        }
    );
    // ANCHOR_END: liveness_return_cancels
}

#[test]
fn liveness_ref_shared_no_cancel() {
    // ANCHOR: liveness_ref_shared_no_cancel
    crate::assert_err!(
        {
            class Data { }

            class Main {
                fn test(^ self) {
                    let d = new Data();
                    let p: ![d] Data = d!;
                    let q: shared[p] ![d] Data = p.ref;
                    let r: ![d] Data = q^;
                    ();
                }
            }
        },
        expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { } class Main { fn test (^ self) -> () { let d = new Data () ; let p : ! [d] Data = d ! ; let q : shared [p] ! [d] Data = p . ref ; let r : ! [d] Data = q ^ ; () ; } } }`"]
    );
    // ANCHOR_END: liveness_ref_shared_no_cancel
}

#[test]
fn liveness_all_places_must_be_dead() {
    // ANCHOR: liveness_all_places_must_be_dead
    crate::assert_err!(
        {
            class Data { }

            class Main {
                fn test(^ self) {
                    let d = new Data();
                    let p: shared[d] Data = d.ref;
                    let q: shared[d] Data = d.ref;
                    let r: shared[p, q] shared[d] Data = p.ref;
                    let s: shared[d] Data = r^;
                    q^;
                }
            }
        },
        expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { } class Main { fn test (^ self) -> () { let d = new Data () ; let p : shared [d] Data = d . ref ; let q : shared [d] Data = d . ref ; let r : shared [p, q] shared [d] Data = p . ref ; let s : shared [d] Data = r ^ ; q ^ ; } } }`"]
    );
    // ANCHOR_END: liveness_all_places_must_be_dead
}

#[test]
fn liveness_both_places_dead_cancels() {
    // ANCHOR: liveness_both_places_dead_cancels
    crate::assert_ok!(
        {
            class Data { }

            class Main {
                fn test(^ self) {
                    let d = new Data();
                    let p: shared[d] Data = d.ref;
                    let q: shared[d] Data = d.ref;
                    let r: shared[p, q] shared[d] Data = p.ref;
                    let s: shared[d] Data = r^;
                    ();
                }
            }
        }
    );
    // ANCHOR_END: liveness_both_places_dead_cancels
}
