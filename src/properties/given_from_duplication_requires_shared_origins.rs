//! ## Giving from alternative origins: duplication requires shared origins
//!
//! For an ordinary non-shared class, a value with permission
//! `given_from[p1, ..., pn]` may be duplicated only if every possible originating
//! place has a type satisfying the `shared` predicate.
//!
//! An **origin** is a place listed in `given_from`: `x: given_from[a, b] Data`
//! means that `x` could have been given from `a` or from `b`. These are alternative
//! origins of one value, not two values stored in `x`. Giving a shared value can
//! duplicate it; giving a uniquely owned value transfers ownership. Uncertainty
//! about which occurred cannot grant permission to duplicate a unique value.
//!
//! For `class Data {}`, the examples are:
//!
//! | Type of `a` | Type of `b` | Duplicate `x: given_from[a, b] Data`? |
//! | --- | --- | --- |
//! | `shared Data` | `shared Data` | Yes |
//! | `shared Data` | `given Data` | No |
//! | `given Data` | `shared Data` | No |
//! | `given Data` | `given Data` | No |
//!
//! Duplication here means using `x.give` twice. The first give must preserve `x`
//! for the second; finding just one shared alternative does not justify that.
//!
//! Origins can also be field places: `given_from[d1.field, d2.field] Data`, or
//! nested places such as `d1.inner.field`. The type of the **complete place**
//! matters. A unique container can hold a declared `shared Data` field;
//! conversely, accessing a `Data` field through a shared container is shared
//! even though its declaration does not say `shared`. The same four-way table
//! applies to those effective field types, including nested projections.
//!
//! ### Candidate lemma
//!
//! Let `C` be an ordinary non-generic class that is not itself shared. In a
//! well-formed environment, for a nonempty list of valid places `p1, ..., pn`,
//! proving `given_from[p1, ..., pn] C is shared` requires proving that the type
//! of every `pi` satisfies `shared`. In particular, one uniquely owned `C`
//! alternative prevents duplication, regardless of its position in the list.
//!
//! This is a candidate formulation, not a proved theorem. The tests exercise two
//! origins of an empty ordinary class, using concrete `given` and `shared`
//! permissions. They cover both mixed orders, both uniform cases, and initialized
//! locals as well as parameters with alternative origins. Field and nested-field
//! matrices cover declared field permissions and permissions inherited from the
//! container. Each matrix case first verifies that giving once is permitted,
//! then checks whether giving twice succeeds or fails specifically at the give.
//!
//! ### Scope
//!
//! This property concerns duplication of `given_from` values, not every predicate
//! or every permission constructor. `shared` is the predicate for duplicability;
//! it does not require full ownership. The tests here use owned shared origins.
//! Types such as `Int` are independently duplicable and are outside the class
//! assumption above. Mutation through alternative origins is a separate property.

use formality_core::test;

#[test]
fn shared_origins_allow_duplicating_initialized_value() {
    crate::assert_ok!({
        class Data {}
        class Main {
            fn test(given self, d1: shared Data, d2: shared Data) {
                let result: given_from[d1, d2] Data = d1.give;
                let a = result.give;
                let b = result.give;
                ();
            }
        }
    });
}

#[test]
fn unique_initializer_cannot_be_duplicated() {
    crate::assert_err!({
        class Data {}
        class Main {
            fn test(given self, d1: given Data, d2: shared Data) {
                let x: given_from[d1, d2] Data = d1.give;
                let a = x.give;
                let b = x.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "give" at (expressions.rs) failed because
          condition evaluted to false: `!live_after.is_live(place)`
            live_after = LivePlaces { accessed: {x}, traversed: {} }
            place = x"#]]);
}

#[test]
fn shared_then_unique_origins_reject_duplication() {
    crate::assert_err!({
        class Data {}
        class Main {
            fn test(given self, d1: shared Data, d2: given Data, x: given_from[d1, d2] Data) {
                let a = x.give;
                let b = x.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "give" at (expressions.rs) failed because
          condition evaluted to false: `!live_after.is_live(place)`
            live_after = LivePlaces { accessed: {x}, traversed: {} }
            place = x"#]]);
}

#[test]
fn unique_then_shared_origins_reject_duplication() {
    crate::assert_err!({
        class Data {}
        class Main {
            fn test(given self, d1: given Data, d2: shared Data, x: given_from[d1, d2] Data) {
                let a = x.give;
                let b = x.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "give" at (expressions.rs) failed because
          condition evaluted to false: `!live_after.is_live(place)`
            live_after = LivePlaces { accessed: {x}, traversed: {} }
            place = x"#]]);
}

#[test]
fn shared_origins_allow_duplicating_parameter() {
    crate::assert_ok!({
        class Data {}
        class Main {
            fn test(given self, d1: shared Data, d2: shared Data, x: given_from[d1, d2] Data) {
                let a = x.give;
                let b = x.give;
                ();
            }
        }
    });
}

#[test]
fn unique_origins_reject_duplication() {
    crate::assert_err!({
        class Data {}
        class Main {
            fn test(given self, d1: given Data, d2: given Data, x: given_from[d1, d2] Data) {
                let a = x.give;
                let b = x.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "give" at (expressions.rs) failed because
          condition evaluted to false: `!live_after.is_live(place)`
            live_after = LivePlaces { accessed: {x}, traversed: {} }
            place = x"#]]);
}

/// Check both the permission of the complete place and the all-origins rule.
/// Every row must permit one give, so a negative duplication case cannot pass
/// merely because its field path or dependent parameter type is ill-formed.
fn check_projected_origins(classes: &str, shared_root: &str, unique_root: &str, path: &str) {
    for (left, right, duplicable) in [
        (shared_root, shared_root, true),
        (shared_root, unique_root, false),
        (unique_root, shared_root, false),
        (unique_root, unique_root, false),
    ] {
        let program = |body: &str| {
            format!(
                "class Data {{}} {classes}
                 class Main {{
                     fn test(given self, d1: {left}, d2: {right},
                             x: given_from[d1.{path}, d2.{path}] Data) {{
                         {body}
                         ();
                     }}
                 }}"
            )
        };
        crate::assert_ok!(&program("let a = x.give;"));
        let duplicate = program("let a = x.give; let b = x.give;");
        if duplicable {
            crate::assert_ok!(&duplicate);
        } else {
            crate::assert_err!(
                &duplicate,
                expect_test::expect![[r#"
                the rule "give" at (expressions.rs) failed because
                  condition evaluted to false: `!live_after.is_live(place)`
                    live_after = LivePlaces { accessed: {x}, traversed: {} }
                    place = x"#]]
            );
        }
    }
}

#[test]
fn declared_field_permissions_control_duplication() {
    // Both containers are unique; the declared field types distinguish origins.
    check_projected_origins(
        "class SharedField { field: shared Data; }
         class UniqueField { field: given Data; }",
        "given SharedField",
        "given UniqueField",
        "field",
    );
}

#[test]
fn container_permissions_control_field_duplication() {
    // The declaration is identical; a shared container makes field access shared.
    check_projected_origins(
        "class Container { field: Data; }",
        "shared Container",
        "given Container",
        "field",
    );
}

#[test]
fn declared_nested_field_permissions_control_duplication() {
    check_projected_origins(
        "class SharedField { field: shared Data; }
         class UniqueField { field: given Data; }
         class SharedLeaf { inner: SharedField; }
         class UniqueLeaf { inner: UniqueField; }",
        "given SharedLeaf",
        "given UniqueLeaf",
        "inner.field",
    );
}

#[test]
fn container_permissions_control_nested_field_duplication() {
    check_projected_origins(
        "class Inner { field: Data; }
         class Outer { inner: Inner; }",
        "shared Outer",
        "given Outer",
        "inner.field",
    );
}
