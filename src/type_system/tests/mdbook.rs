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
                fn test(given self) -> Int {
                    let p = new Point(22, 44);
                    p.x.give;
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
                fn test(given self) -> Int {
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
                fn test(given self) -> Data {
                    let d = new Data();
                    d.give;
                }
            }
        }
    );
    // ANCHOR_END: giving_a_value
}

#[test]
fn giving_a_value_twice_is_error() {
    // ANCHOR: giving_a_value_twice_is_error
    crate::assert_err_str!(
        {
            class Data { }

            class Main {
                fn test(given self) -> Data {
                    let d = new Data();
                    d.give;
                    d.give;
                }
            }
        },
        r#"the rule "give" at (*) failed"#,
        "`!live_after.is_live(&place)`",
        "&place = d",
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
                fn test(given self) -> Data {
                    let p = new Pair(new Data(), new Data());
                    p.a.give;
                    p.b.give;
                }
            }
        }
    );
    // ANCHOR_END: giving_a_field
}

#[test]
fn giving_field_then_whole_is_error() {
    // ANCHOR: giving_field_then_whole_is_error
    crate::assert_err_str!(
        {
            class Data { }

            class Pair {
                a: Data;
                b: Data;
            }

            class Main {
                fn test(given self) -> Pair {
                    let p = new Pair(new Data(), new Data());
                    p.a.give;
                    p.give;
                }
            }
        },
        r#"the rule "give" at (*) failed"#,
        "`!live_after.is_live(&place)`",
        "&place = p . a",
    );
    // ANCHOR_END: giving_field_then_whole_is_error
}

#[test]
fn giving_whole_then_field_is_error() {
    // ANCHOR: giving_whole_then_field_is_error
    crate::assert_err_str!(
        {
            class Data { }

            class Pair {
                a: Data;
                b: Data;
            }

            class Main {
                fn test(given self) -> Data {
                    let p = new Pair(new Data(), new Data());
                    p.give;
                    p.a.give;
                }
            }
        },
        r#"the rule "give" at (*) failed"#,
        "`!live_after.is_live(&place)`",
        "&place = p",
    );
    // ANCHOR_END: giving_whole_then_field_is_error
}

#[test]
fn shared_classes_are_copyable() {
    // ANCHOR: shared_classes_are_copyable
    crate::assert_ok!(
        {
            class Main {
                fn test(given self) -> Int {
                    let x = 22;
                    x.give;
                    x.give;
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
                fn test(given self) -> shared Data {
                    let d = new Data();
                    let s = d.give.share;
                    s.give;
                    s.give;
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
                fn test(given self) -> Point {
                    let p = new Point(22, 44);
                    p.give;
                    p.give;
                }
            }
        }
    );
    // ANCHOR_END: shared_classes_always_shared
}

#[test]
fn given_classes_cannot_be_shared() {
    // ANCHOR: given_classes_cannot_be_shared
    crate::assert_err_str!(
        {
            given class Resource { }

            class Main {
                fn test(given self) -> shared Resource {
                    let r = new Resource();
                    r.give.share;
                }
            }
        },
        r#"the rule "share class" at (*) failed"#,
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
                fn test(given self) -> shared Data {
                    let d = new Data();
                    d.give.share.share;
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
                fn test(given self) {
                    let foo = new Foo(new Data());
                    let bar = foo.ref;
                    let i = foo.i.ref;
                    bar.give;
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
    crate::assert_err_str!(
        {
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn test(given self) {
                    let foo = new Foo(new Data());
                    let bar = foo.ref;
                    let i = foo.i.mut;
                    bar.give;
                    ();
                }
            }
        },
        r#"the rule "share-mutation" at (*) failed"#,
        "`place_disjoint_from(&accessed_place, &shared_place)`",
        "&accessed_place = foo . i",
        "&shared_place = foo",
    );
    // ANCHOR_END: mutation_through_ref_is_error
}

#[test]
fn giving_field_while_refd_is_error() {
    // ANCHOR: giving_field_while_refd_is_error
    crate::assert_err_str!(
        {
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn test(given self) {
                    let foo = new Foo(new Data());
                    let bar = foo.ref;
                    let i = foo.i.give;
                    bar.give;
                    ();
                }
            }
        },
        r#"the rule "share-give" at (*) failed"#,
        "`place_disjoint_from_or_prefix_of(&accessed_place, &shared_place)`",
        "&accessed_place = foo . i",
        "&shared_place = foo",
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
                fn test(given self) {
                    let foo = new Foo(new Data());
                    let bar = foo.mut;
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
    crate::assert_err_str!(
        {
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn test(given self) {
                    let foo = new Foo(new Data());
                    let bar = foo.mut;
                    let i = foo.i.ref;
                    bar.give;
                    ();
                }
            }
        },
        r#"the rule "lease-mutation" at (*) failed"#,
        "`place_disjoint_from(&accessed_place, &leased_place)`",
        "&accessed_place = foo . i",
        "&leased_place = foo",
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
                fn test(given self) {
                    let foo = new Data();
                    let other = new Data();
                    let bar = foo.ref;
                    other.give;
                    bar.give;
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
    crate::assert_err_str!(
        {
            class Data { }

            class Foo {
                i: Data;
            }

            class Main {
                fn test(given self) {
                    let p = new Foo(new Data());
                    let q = p.mut;
                    let r = q.ref;
                    let i = p.i.ref;
                    r.give;
                    ();
                }
            }
        },
        r#"the rule "lease-mutation" at (*) failed"#,
        "`place_disjoint_from(&accessed_place, &leased_place)`",
        "&accessed_place = p . i",
        "&leased_place = p",
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
                fn test(given self) -> Data {
                    let d: given Data = new Data();
                    d.give;
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
                fn test(given self, d: given Data) -> ref[d] Data {
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
                fn test(given self, d: given Outer) -> ref[d] Inner {
                    let r: ref[d] Outer = d.ref;
                    r.i.give;
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
                fn test(given self, w: given Wrapper) -> Point {
                    let r: ref[w] Wrapper = w.ref;
                    r.p.give;
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
                fn test(given self) {
                    let d: given Data = new Data();
                    let p: mut[d] Data = d.mut;
                    let q: ref[p] mut[d] Data = p.ref;
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
                fn test(given self) -> ref[self] Data {
                    let d: shared Data = new Data().share;
                    d.give;
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
                fn test(given self, d1: given Data, d2: given Data) -> ref[d1, d2] Data {
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
    crate::assert_err_str!(
        {
            class Foo { }
            class Bar { }

            class Main {
                fn test(given self) {
                    let f = new Foo();
                    let b: Bar = f.give;
                    ();
                }
            }
        },
        r#"no applicable rules"#,
    );
    // ANCHOR_END: subtyping_different_classes_fail
}

#[test]
fn subtyping_narrowing_ref_fails() {
    // ANCHOR: subtyping_narrowing_ref_fails
    crate::assert_err_str!(
        {
            class Data { }

            class Main {
                fn test(given self, d1: given Data, d2: given Data) -> ref[d1] Data {
                    let r: ref[d1, d2] Data = d1.ref;
                    r.give;
                }
            }
        },
        r#"is_prefix_of"#,
    );
    // ANCHOR_END: subtyping_narrowing_ref_fails
}

#[test]
fn subtyping_perm_erasure_ref_int() {
    // ANCHOR: subtyping_perm_erasure_ref_int
    crate::assert_ok!(
        {
            class Main {
                fn test(given self) -> Int {
                    let x: ref[self] Int = 0;
                    x.give;
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
                fn test(given self) -> Int {
                    let x: Int = 0;
                    let y: ref[self] Int = x.give;
                    y.give;
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
                fn test(given self) -> Point {
                    let p: shared Point = new Point(1, 2);
                    p.give;
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
                fn test(given self, d: given Data) -> Box[Data] {
                    let b: ref[d] Box[Data] = new Box[Data](new Data());
                    b.give;
                }
            }
        },
        expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]
    );
    // ANCHOR_END: subtyping_non_copy_params_block_erasure
}

#[test]
fn subtyping_place_refinement() {
    // ANCHOR: subtyping_place_refinement
    crate::assert_ok!(
        {
            class Data {
                left: given Data;
                right: given Data;
            }

            class Main {
                fn test(given self, d: given Data) -> ref[d] Data {
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
    crate::assert_err_str!(
        {
            class Data {
                left: given Data;
                right: given Data;
            }

            class Main {
                fn test(given self, d: given Data) -> ref[d.left] Data {
                    d.ref;
                }
            }
        },
        r#"is_prefix_of"#,
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
                fn test(given self, d: given Data) {
                    let s: shared Data = new Data().share;
                    let r: ref[d] Data = s.give;
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
    crate::assert_err_str!(
        {
            class Data { }

            class Main {
                fn test(given self, d: given Data) {
                    let r: ref[d] Data = d.ref;
                    let s: shared Data = r.give;
                    ();
                }
            }
        },
        r#"predicates.rs"#,
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
                fn test(given self, d: given Data) {
                    let s: shared Data = new Data().share;
                    let r: shared mut[d] Data = s.give;
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
                fn test(given self, d: given Data) {
                    let r: ref[d] Data = d.ref;
                    let sm: shared mut[d] Data = r.give;
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
    crate::assert_err_str!(
        {
            class Data { }

            class Main {
                fn test(given self, d: given Data) {
                    let p: mut[d] Data = d.mut;
                    let sm: shared mut[d] Data = p.ref;
                    let r: ref[d] Data = sm.give;
                    ();
                }
            }
        },
        r#"predicates.rs"#,
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
                fn test(given self) {
                    let d: shared Data = new Data().share;
                    let r = d.ref;
                    let s: shared Data = r.give;
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
                fn test(given self) {
                    let d: given Data = new Data();
                    let p: mut[d] Data = d.mut;
                    let q: ref[p] mut[d] Data = p.ref;
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
    crate::assert_err_str!(
        {
            class Data { }

            class Main {
                fn test(given self, d: given Data) {
                    let p: mut[d] Data = d.mut;
                    let q: ref[d] Data = p.give;
                    ();
                }
            }
        },
        r#"predicates.rs"#,
    );
    // ANCHOR_END: copy_perm_mut_not_subtype_ref
}

#[test]
fn copy_perm_given_not_subtype_shared() {
    // ANCHOR: copy_perm_given_not_subtype_shared
    crate::assert_err_str!(
        {
            class Data { }

            class Main {
                fn test(given self, d: given Data) {
                    let s: shared Data = d.give;
                    ();
                }
            }
        },
        r#"predicates.rs"#,
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
                left: given Data;
                right: given Data;
            }

            class Main {
                fn test(given self, d: given Data) {
                    let r: ref[d] Data = d.left.ref;
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
                left: given Data;
                right: given Data;
            }

            class Main {
                fn test(given self, d: given Data) {
                    let r: mut[d] Data = d.left.mut;
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
    crate::assert_err_str!(
        {
            class Data {
                left: given Data;
                right: given Data;
            }

            class Main {
                fn test(given self, d: given Data) {
                    let r: ref[d.left] Data = d.ref;
                    ();
                }
            }
        },
        r#"predicates.rs"#,
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
                fn test(given self, d1: given Data, d2: given Data) {
                    let r: ref[d1, d2] Data = d1.ref;
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
    crate::assert_err_str!(
        {
            class Data { }

            class Main {
                fn test(given self, d1: given Data, d2: given Data) {
                    let r: ref[d1, d2] Data = d1.ref;
                    let s: ref[d1] Data = r.give;
                    ();
                }
            }
        },
        r#"predicates.rs"#,
    );
    // ANCHOR_END: place_ordering_dropping_source_fails
}

#[test]
fn place_ordering_both_dimensions() {
    // ANCHOR: place_ordering_both_dimensions
    crate::assert_ok!(
        {
            class Data {
                left: given Data;
                right: given Data;
            }

            class Main {
                fn test(given self, d: given Data) {
                    let r: ref[d.left, d.right] Data = d.left.ref;
                    let s: ref[d] Data = r.give;
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
                left: given Data;
                right: given Data;
            }

            class Main {
                fn test(given self, d: given Data) {
                    let r: mut[d.left, d.right] Data = d.left.mut;
                    let s: mut[d] Data = r.give;
                    ();
                }
            }
        }
    );
    // ANCHOR_END: place_ordering_both_dimensions_mut
}
