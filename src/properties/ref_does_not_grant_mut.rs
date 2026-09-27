//! ## A shared borrow does not grant a mutable lease
//!
//! Borrowing with `ref` produces a shared view. It does not satisfy `mut`, even
//! when the borrowed place itself holds a mutable lease. A caller cannot pass that
//! view to a method requiring `P is mut` merely because the underlying owner or
//! lease permits mutation.
//!
//! For an ordinary non-shared `Wrapper`, these examples distinguish the view
//! from the place it borrows:
//!
//! | View | Satisfies `shared`? | Satisfies `mut`? |
//! | --- | --- | --- |
//! | `ref[source]`, where `source` is uniquely owned | Yes | No |
//! | `ref[lease]`, where `lease: mut[source] Wrapper` | Yes | No |
//! | `ref[lease.field]`, through a mutable container lease | Yes | No |
//! | `shared mut[source]`, after cancelling a dead intermediate lease | Yes | No |
//!
//! The lifetime of the intermediate lease does not upgrade the view. When the
//! lease is dead, the view can be coerced to `shared mut[source]`; the shared
//! component remains. When the lease stays live, it can be passed to a method
//! requiring `mut` after the view's final use. Its predicate remains true throughout;
//! the view temporarily restricts access to it.
//!
//! ### Candidate lemma and evidence
//!
//! For concrete permissions and an ordinary non-shared class, adding a shared
//! view by `ref` does not derive the `mut` predicate from the underlying place's
//! `mut` predicate. Eliminating a dead intermediate place preserves that shared
//! component. This is a candidate lemma about static permission classification,
//! not a proved theorem about arbitrary generic assumptions or runtime aliases.
//!
//! Each example constructs its view in a complete Dada program and passes it to
//! a method requiring either `shared` (accepted) or `mut` (rejected). The cases
//! cover a unique owner, a live lease, a dead lease, explicit cancellation, and a
//! projected field. Each rejection has a control with only its `mut` requirement
//! removed. The live-lease cases also pass the original lease to a method requiring
//! `mut` after the view's last use. Referents remain live throughout the calls.

use formality_core::test;

#[test]
fn ref_of_owner_satisfies_shared() {
    let program = r#"
    class Wrapper {
        value: Int;
        fn check_lease[perm Q](Q self) where Q is mut { (); }
    }
    class Main {
        fn require_shared[perm P](given self, value: P Wrapper)
        where P is shared { (); }
        fn test(given self, source: given Wrapper) {
            let view: ref[source] Wrapper = source.ref;
            self.give.require_shared[ref[source]](view.give);
            source.ref;
            ();
        }
    }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn ref_of_owner_does_not_satisfy_mut() {
    let program = r#"
    class Wrapper {
        value: Int;
        fn check_lease[perm Q](Q self) where Q is mut { (); }
    }
    class Main {
        fn require_mut[perm P](given self, value: P Wrapper)
        where P is mut { (); }
        fn test(given self, source: given Wrapper) {
            let view: ref[source] Wrapper = source.ref;
            self.give.require_mut[ref[source]](view.give);
            source.ref;
            ();
        }
    }
    "#;
    // The view and call are valid without the capability requirement.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; fn check_lease [perm] (^perm0_0 self) -> () where ^perm0_0 is mut { () ; } } class Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (given self source : given Wrapper) -> () { let view : ref [source] Wrapper = source . ref ; self . give . require_mut [ref [source]] (view . give) ; source . ref ; () ; } } }`"]);
}

#[test]
fn ref_of_live_lease_satisfies_shared() {
    let program = r#"
    class Wrapper {
        value: Int;
        fn check_lease[perm Q](Q self) where Q is mut { (); }
    }
    class Main {
        fn require_shared[perm P](given self, value: P Wrapper)
        where P is shared { (); }
        fn test(given self, source: given Wrapper) {
            let lease: mut[source] Wrapper = source.mut;
            let view: ref[lease] Wrapper = lease.ref;
            self.give.require_shared[ref[lease]](view.give);
            lease.give.check_lease[mut[source]]();
            source.ref;
            ();
        }
    }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn ref_of_live_lease_does_not_satisfy_mut() {
    let program = r#"
    class Wrapper {
        value: Int;
        fn check_lease[perm Q](Q self) where Q is mut { (); }
    }
    class Main {
        fn require_mut[perm P](given self, value: P Wrapper)
        where P is mut { (); }
        fn test(given self, source: given Wrapper) {
            let lease: mut[source] Wrapper = source.mut;
            let view: ref[lease] Wrapper = lease.ref;
            self.give.require_mut[ref[lease]](view.give);
            lease.give.check_lease[mut[source]]();
            source.ref;
            ();
        }
    }
    "#;
    // The view and call are valid without the capability requirement.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; fn check_lease [perm] (^perm0_0 self) -> () where ^perm0_0 is mut { () ; } } class Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (given self source : given Wrapper) -> () { let lease : mut [source] Wrapper = source . mut ; let view : ref [lease] Wrapper = lease . ref ; self . give . require_mut [ref [lease]] (view . give) ; lease . give . check_lease [mut [source]] () ; source . ref ; () ; } } }`"]);
}

#[test]
fn ref_of_dead_lease_satisfies_shared() {
    let program = r#"
    class Wrapper {
        value: Int;
        fn check_lease[perm Q](Q self) where Q is mut { (); }
    }
    class Main {
        fn require_shared[perm P](given self, value: P Wrapper)
        where P is shared { (); }
        fn test(given self, source: given Wrapper) {
            let lease: mut[source] Wrapper = source.mut;
            let view: ref[lease] Wrapper = lease.ref;
            self.give.require_shared[ref[lease]](view.give);
            source.ref;
            ();
        }
    }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn ref_of_dead_lease_does_not_satisfy_mut() {
    let program = r#"
    class Wrapper {
        value: Int;
        fn check_lease[perm Q](Q self) where Q is mut { (); }
    }
    class Main {
        fn require_mut[perm P](given self, value: P Wrapper)
        where P is mut { (); }
        fn test(given self, source: given Wrapper) {
            let lease: mut[source] Wrapper = source.mut;
            let view: ref[lease] Wrapper = lease.ref;
            self.give.require_mut[ref[lease]](view.give);
            source.ref;
            ();
        }
    }
    "#;
    // The view and call are valid without the capability requirement.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; fn check_lease [perm] (^perm0_0 self) -> () where ^perm0_0 is mut { () ; } } class Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (given self source : given Wrapper) -> () { let lease : mut [source] Wrapper = source . mut ; let view : ref [lease] Wrapper = lease . ref ; self . give . require_mut [ref [lease]] (view . give) ; source . ref ; () ; } } }`"]);
}

#[test]
fn cancelled_ref_of_dead_lease_satisfies_shared() {
    let program = r#"
    class Wrapper {
        value: Int;
        fn check_lease[perm Q](Q self) where Q is mut { (); }
    }
    class Main {
        fn require_shared[perm P](given self, value: P Wrapper)
        where P is shared { (); }
        fn test(given self, source: given Wrapper) {
            let lease: mut[source] Wrapper = source.mut;
            let view: ref[lease] Wrapper = lease.ref;
            let flattened: shared mut[source] Wrapper = view.give;
            self.give.require_shared[shared mut[source]](flattened.give);
            source.ref;
            ();
        }
    }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn cancelled_ref_of_dead_lease_does_not_satisfy_mut() {
    let program = r#"
    class Wrapper {
        value: Int;
        fn check_lease[perm Q](Q self) where Q is mut { (); }
    }
    class Main {
        fn require_mut[perm P](given self, value: P Wrapper)
        where P is mut { (); }
        fn test(given self, source: given Wrapper) {
            let lease: mut[source] Wrapper = source.mut;
            let view: ref[lease] Wrapper = lease.ref;
            let flattened: shared mut[source] Wrapper = view.give;
            self.give.require_mut[shared mut[source]](flattened.give);
            source.ref;
            ();
        }
    }
    "#;
    // The view and call are valid without the capability requirement.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; fn check_lease [perm] (^perm0_0 self) -> () where ^perm0_0 is mut { () ; } } class Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (given self source : given Wrapper) -> () { let lease : mut [source] Wrapper = source . mut ; let view : ref [lease] Wrapper = lease . ref ; let flattened : shared mut [source] Wrapper = view . give ; self . give . require_mut [shared mut [source]] (flattened . give) ; source . ref ; () ; } } }`"]);
}

#[test]
fn ref_of_leased_field_satisfies_shared() {
    let program = r#"
    class Wrapper {
        value: Int;
        fn check_lease[perm Q](Q self) where Q is mut { (); }
    }
    class Container { field: Wrapper; }
    class Main {
        fn require_shared[perm P](given self, value: P Wrapper)
        where P is shared { (); }
        fn test(given self, source: given Container) {
            let lease: mut[source] Container = source.mut;
            let view: ref[lease.field] Wrapper = lease.field.ref;
            self.give.require_shared[ref[lease.field]](view.give);
            source.ref;
            ();
        }
    }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn ref_of_leased_field_does_not_satisfy_mut() {
    let program = r#"
    class Wrapper {
        value: Int;
        fn check_lease[perm Q](Q self) where Q is mut { (); }
    }
    class Container { field: Wrapper; }
    class Main {
        fn require_mut[perm P](given self, value: P Wrapper)
        where P is mut { (); }
        fn test(given self, source: given Container) {
            let lease: mut[source] Container = source.mut;
            let view: ref[lease.field] Wrapper = lease.field.ref;
            self.give.require_mut[ref[lease.field]](view.give);
            source.ref;
            ();
        }
    }
    "#;
    // The view and call are valid without the capability requirement.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; fn check_lease [perm] (^perm0_0 self) -> () where ^perm0_0 is mut { () ; } } class Container { field : Wrapper ; } class Main { fn require_mut [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (given self source : given Container) -> () { let lease : mut [source] Container = source . mut ; let view : ref [lease . field] Wrapper = lease . field . ref ; self . give . require_mut [ref [lease . field]] (view . give) ; source . ref ; () ; } } }`"]);
}
