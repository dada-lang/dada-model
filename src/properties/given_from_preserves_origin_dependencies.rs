//! ## Giving preserves the origins' borrowing dependencies
//!
//! A value with permission `given_from[p1, ..., pn]` retains borrowing
//! dependencies from every possible originating place's type. Giving that value
//! to another binding does not erase those dependencies. Duplicating it, when
//! permitted, leaves each live duplicate subject to the same restrictions.
//!
//! For example, if `d1: ref[source1.field] Data` and
//! `d2: ref[source2.field] Data`, then a live value with permission
//! `given_from[d1, d2]` protects both possible referents from mutation. Even after
//! `d1`, `d2`, the original value, and one duplicate have their last uses, a
//! surviving duplicate still protects both fields. For `mut` origins, the
//! surviving value blocks reads as well as mutations of the referents.
//!
//! The **origins** are `d1` and `d2`; their **referents** are `source1.field` and
//! `source2.field`. `given_from` inherits the origins' dependencies rather than
//! creating fresh borrows of the origin bindings. Those bindings need not stay
//! live. Origins can also be projected places such as `d1.field` storing a ref.
//!
//! Disjoint sibling fields remain accessible. Once the last dependent value has
//! its final use, the borrowing restrictions cease. If the referent itself is
//! moved to a new binding while a dependent value stays live, its restrictions
//! follow the new place, as in the separate move-dependency property.
//!
//! ### Candidate lemma and evidence
//!
//! In a well-formed environment, the liens of the permission
//! `given_from[p1, ..., pn]` are the union of the liens obtained from the types of
//! those places. No additional lien on an origin is introduced by `given_from`
//! itself. For a permitted transfer to a fresh binding, the resulting live value
//! retains those referent obligations, accounting for any place substitutions.
//! This is a candidate static preservation lemma, not a proved theorem.
//!
//! Complete Dada programs check both alternative referents separately, projected
//! origins with stored refs, disjoint siblings, and access after the surviving
//! value's final use. Initialized local examples transfer a mutable borrow
//! through `given_from` after its origin's last use; paired examples check the
//! same restriction before and after relocating the referent. The duplication
//! cases were extracted from `given_from_duplication_requires_shared_origins`.
//!
//! These examples use ordinary non-shared classes. They concern static access
//! restrictions, not runtime mutable-pointer relocation, scope-exit cleanup, or
//! every permission composition and generic type.

use formality_core::test;

#[test]
fn duplicated_ref_protects_referent_1() {
    let program = r#"
    class Data {}
    class Container { field: Data; other: Data; }
    class Main {
        fn test(given self, source1: given Container, source2: given Container,
                d1: ref[source1.field] Data, d2: ref[source2.field] Data,
                x: given_from[d1, d2] Data) {
            let first = x.give;
            let survivor = x.give;
            first.give;
            source1.field.mut;
            survivor.give;
            ();
        }
    }
    "#;
    crate::assert_err!(
        program,
        expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
            accessed_place = source1 . field
            shared_place = source1 . field"#]]
    );
}

#[test]
fn duplicated_ref_protects_referent_2() {
    let program = r#"
    class Data {}
    class Container { field: Data; other: Data; }
    class Main {
        fn test(given self, source1: given Container, source2: given Container,
                d1: ref[source1.field] Data, d2: ref[source2.field] Data,
                x: given_from[d1, d2] Data) {
            let first = x.give;
            let survivor = x.give;
            first.give;
            source2.field.mut;
            survivor.give;
            ();
        }
    }
    "#;
    crate::assert_err!(
        program,
        expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
            accessed_place = source2 . field
            shared_place = source2 . field"#]]
    );
}

#[test]
fn duplicated_ref_allows_disjoint_siblings() {
    let program = r#"
    class Data {}
    class Container { field: Data; other: Data; }
    class Main {
        fn test(given self, source1: given Container, source2: given Container,
                d1: ref[source1.field] Data, d2: ref[source2.field] Data,
                x: given_from[d1, d2] Data) {
            let first = x.give;
            let survivor = x.give;
            first.give;
            source1.other.mut;
            source2.other.mut;
            survivor.give;
            ();
        }
    }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn duplicated_ref_releases_referents_after_last_use() {
    let program = r#"
    class Data {}
    class Container { field: Data; other: Data; }
    class Main {
        fn test(given self, source1: given Container, source2: given Container,
                d1: ref[source1.field] Data, d2: ref[source2.field] Data,
                x: given_from[d1, d2] Data) {
            let first = x.give;
            let survivor = x.give;
            first.give;
            survivor.give;
            source1.field.mut;
            source2.field.mut;
            ();
        }
    }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn transferred_mut_protects_referent_1() {
    let program = r#"
    class Data {}
    class Container { field: Data; other: Data; }
    class Main {
        fn test(given self, source1: given Container, source2: given Container,
                d1: mut[source1.field] Data, d2: mut[source2.field] Data,
                x: given_from[d1, d2] Data) {
            let survivor = x.give;
            source1.field.ref;
            survivor.give;
            ();
        }
    }
    "#;
    crate::assert_err!(
        program,
        expect_test::expect![[r#"
        the rule "lease-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
            accessed_place = source1 . field
            leased_place = source1 . field"#]]
    );
}

#[test]
fn transferred_mut_protects_referent_2() {
    let program = r#"
    class Data {}
    class Container { field: Data; other: Data; }
    class Main {
        fn test(given self, source1: given Container, source2: given Container,
                d1: mut[source1.field] Data, d2: mut[source2.field] Data,
                x: given_from[d1, d2] Data) {
            let survivor = x.give;
            source2.field.ref;
            survivor.give;
            ();
        }
    }
    "#;
    crate::assert_err!(
        program,
        expect_test::expect![[r#"
        the rule "lease-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
            accessed_place = source2 . field
            leased_place = source2 . field"#]]
    );
}

#[test]
fn transferred_mut_allows_disjoint_siblings() {
    let program = r#"
    class Data {}
    class Container { field: Data; other: Data; }
    class Main {
        fn test(given self, source1: given Container, source2: given Container,
                d1: mut[source1.field] Data, d2: mut[source2.field] Data,
                x: given_from[d1, d2] Data) {
            let survivor = x.give;
            source1.other.mut;
            source2.other.mut;
            survivor.give;
            ();
        }
    }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn transferred_mut_releases_referents_after_last_use() {
    let program = r#"
    class Data {}
    class Container { field: Data; other: Data; }
    class Main {
        fn test(given self, source1: given Container, source2: given Container,
                d1: mut[source1.field] Data, d2: mut[source2.field] Data,
                x: given_from[d1, d2] Data) {
            let survivor = x.give;
            survivor.give;
            source1.field.mut;
            source2.field.mut;
            ();
        }
    }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn stored_ref_origin_protects_referent_1() {
    let program = r#"
    class Data {}
    class Container { field: Data; other: Data; }
    class Holder[perm P] { field: P Data; }
    class Main {
        fn test(given self, source1: given Container, source2: given Container,
                d1: given Holder[ref[source1.field]],
                d2: given Holder[ref[source2.field]],
                x: given_from[d1.field, d2.field] Data) {
            let survivor = x.give;
            source1.field.mut;
            survivor.give;
            ();
        }
    }
    "#;
    crate::assert_err!(
        program,
        expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
            accessed_place = source1 . field
            shared_place = source1 . field"#]]
    );
}

#[test]
fn stored_ref_origin_protects_referent_2() {
    let program = r#"
    class Data {}
    class Container { field: Data; other: Data; }
    class Holder[perm P] { field: P Data; }
    class Main {
        fn test(given self, source1: given Container, source2: given Container,
                d1: given Holder[ref[source1.field]],
                d2: given Holder[ref[source2.field]],
                x: given_from[d1.field, d2.field] Data) {
            let survivor = x.give;
            source2.field.mut;
            survivor.give;
            ();
        }
    }
    "#;
    crate::assert_err!(
        program,
        expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
            accessed_place = source2 . field
            shared_place = source2 . field"#]]
    );
}

#[test]
fn stored_ref_origins_allow_disjoint_and_later_access() {
    let program = r#"
    class Data {}
    class Container { field: Data; other: Data; }
    class Holder[perm P] { field: P Data; }
    class Main {
        fn test(given self, source1: given Container, source2: given Container,
                d1: given Holder[ref[source1.field]],
                d2: given Holder[ref[source2.field]],
                x: given_from[d1.field, d2.field] Data) {
            let survivor = x.give;
            source1.other.mut;
            source2.other.mut;
            survivor.give;
            source1.field.mut;
            source2.field.mut;
            ();
        }
    }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn initialized_mut_origin_protects_source() {
    let program = r#"
    class Data {}
    class Main {
        fn test(given self) {
            let source = new Data();
            let origin: mut[source] Data = source.mut;
            let x: given_from[origin] Data = origin.give;
            let survivor = x.give;
            source.ref;
            survivor.give;
            ();
        }
    }
    "#;
    crate::assert_err!(
        program,
        expect_test::expect![[r#"
        the rule "lease-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
            accessed_place = source
            leased_place = source"#]]
    );
}

#[test]
fn initialized_mut_origin_releases_source() {
    let program = r#"
    class Data {}
    class Main {
        fn test(given self) {
            let source = new Data();
            let origin: mut[source] Data = source.mut;
            let x: given_from[origin] Data = origin.give;
            let survivor = x.give;
            survivor.give;
            source.ref;
            ();
        }
    }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn initialized_mut_origin_protects_relocated() {
    let program = r#"
    class Data {}
    class Main {
        fn test(given self) {
            let source = new Data();
            let origin: mut[source] Data = source.mut;
            let x: given_from[origin] Data = origin.give;
            let survivor = x.give;
            let relocated = source.give;
            relocated.ref;
            survivor.give;
            ();
        }
    }
    "#;
    crate::assert_err!(
        program,
        expect_test::expect![[r#"
        the rule "lease-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
            accessed_place = relocated
            leased_place = relocated"#]]
    );
}

#[test]
fn initialized_mut_origin_releases_relocated() {
    let program = r#"
    class Data {}
    class Main {
        fn test(given self) {
            let source = new Data();
            let origin: mut[source] Data = source.mut;
            let x: given_from[origin] Data = origin.give;
            let survivor = x.give;
            let relocated = source.give;
            survivor.give;
            relocated.ref;
            ();
        }
    }
    "#;
    crate::assert_ok!(program);
}
