use formality_core::test;

// Tests for predicate quantifier correctness on multi-place permissions.
//
// given_from[p1, p2] means "could have been given from either p1 or p2."
// A predicate must hold for ALL places, not just ANY, because we don't
// know which place the value actually came from.
//
// Similarly, mut[p1, p2] means "borrowed mutably from one of these places."

// --- Copy predicate on given_from ---

/// given_from[p1, p2] where BOTH places have copy types → copy.
/// Giving twice should succeed because the value is copy.
#[test]
fn given_from_copy_when_all_copy() {
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

/// given_from with a single non-copy place → not copy.
/// Giving twice should fail.
#[test]
fn given_from_not_copy_single_place() {
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
        src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: shared Data, x: given_from [d1, d2] Data}, assumptions: {}, fresh: 0 } }

        src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: shared Data, x: given_from [d1, d2] Data}, assumptions: {}, fresh: 0 } }

        src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: shared Data, x: given_from [d1, d2] Data}, assumptions: {}, fresh: 0 } }

        the rule "give" at (expressions.rs) failed because
          condition evaluated to false: `!live_after.is_live(place)`
            live_after = LivePlaces { accessed: {x}, traversed: {} }
            place = x"#]]);
}

/// given_from[d1, d2] where d1 is copy but d2 is NOT copy → NOT copy.
/// This is the key bug: with the old ANY rule, given_from[d1, d2] would be
/// considered copy because d1 is copy. But the value could have come from d2,
/// which is move-only.
///
/// We use a function parameter typed as given_from[d1, d2] Data to get
/// the multi-place permission, then try to use it twice.
#[test]
fn given_from_not_copy_when_mixed_copy_and_move() {
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
        src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Data, d2: given Data, x: given_from [d1, d2] Data}, assumptions: {}, fresh: 0 } }

        src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Data, d2: given Data, x: given_from [d1, d2] Data}, assumptions: {}, fresh: 0 } }

        src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: shared Data, d2: given Data, x: given_from [d1, d2] Data}, assumptions: {}, fresh: 0 } }

        the rule "give" at (expressions.rs) failed because
          condition evaluated to false: `!live_after.is_live(place)`
            live_after = LivePlaces { accessed: {x}, traversed: {} }
            place = x"#]]);
}

/// Symmetric: given_from[d1, d2] where d1 is NOT copy but d2 IS copy → NOT copy.
#[test]
fn given_from_not_copy_when_mixed_move_and_copy() {
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
        src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: shared Data, x: given_from [d1, d2] Data}, assumptions: {}, fresh: 0 } }

        src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: shared Data, x: given_from [d1, d2] Data}, assumptions: {}, fresh: 0 } }

        src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d1: given Data, d2: shared Data, x: given_from [d1, d2] Data}, assumptions: {}, fresh: 0 } }

        the rule "give" at (expressions.rs) failed because
          condition evaluated to false: `!live_after.is_live(place)`
            live_after = LivePlaces { accessed: {x}, traversed: {} }
            place = x"#]]);
}

/// given_from[d1, d2] where BOTH are copy → copy. Double use should succeed.
#[test]
fn given_from_copy_when_both_copy() {
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

// --- Mut predicate on given_from ---

/// given_from[d1, d2] where both places have non-copy (given) types → mut.
/// Field assignment requires mut permission on the object.
/// given is non-copy, so given_from[given_place] composes to mut.
#[test]
fn given_from_mut_when_all_noncopy() {
    crate::assert_ok!({
        class Wrapper { value: Int; }
        class Main {
            fn test(given self, d1: given Wrapper, d2: given Wrapper, x: given_from[d1, d2] Wrapper) {
                x.value = 42;
                ();
            }
        }
    });
}

/// given_from[d1, d2] where d1 is non-copy (mut) but d2 is copy (not mut) → NOT mut.
/// Field assignment should fail because given_from might have come from d2 (shared),
/// and shared permissions don't allow mutation.
#[test]
fn given_from_not_mut_when_mixed() {
    crate::assert_err!({
        class Wrapper { value: Int; }
        class Main {
            fn test(given self, d1: given Wrapper, d2: shared Wrapper, x: given_from[d1, d2] Wrapper) {
                x.value = 42;
                ();
            }
        }
    }, expect_test::expect![[r#"
        src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Int, d1: given Wrapper, d2: shared Wrapper, x: given_from [d1, d2] Wrapper}, assumptions: {}, fresh: 1 } }

        src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: Wrapper, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Int, d1: given Wrapper, d2: shared Wrapper, x: given_from [d1, d2] Wrapper}, assumptions: {}, fresh: 1 } }

        src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Int, d1: given Wrapper, d2: shared Wrapper, x: given_from [d1, d2] Wrapper}, assumptions: {}, fresh: 1 } }

        src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Int, d1: given Wrapper, d2: shared Wrapper, x: given_from [d1, d2] Wrapper}, assumptions: {}, fresh: 1 } }

        src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Int, d1: given Wrapper, d2: shared Wrapper, x: given_from [d1, d2] Wrapper}, assumptions: {}, fresh: 1 } }

        src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Int, d1: given Wrapper, d2: shared Wrapper, x: given_from [d1, d2] Wrapper}, assumptions: {}, fresh: 1 } }

        src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: Wrapper, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Int, d1: given Wrapper, d2: shared Wrapper, x: given_from [d1, d2] Wrapper}, assumptions: {}, fresh: 1 } }

        src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Int, d1: given Wrapper, d2: shared Wrapper, x: given_from [d1, d2] Wrapper}, assumptions: {}, fresh: 1 } }

        src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: Wrapper, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Int, d1: given Wrapper, d2: shared Wrapper, x: given_from [d1, d2] Wrapper}, assumptions: {}, fresh: 1 } }

        src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Int, d1: given Wrapper, d2: shared Wrapper, x: given_from [d1, d2] Wrapper}, assumptions: {}, fresh: 1 } }

        src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Int, d1: given Wrapper, d2: shared Wrapper, x: given_from [d1, d2] Wrapper}, assumptions: {}, fresh: 1 } }

        src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: shared, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Int, d1: given Wrapper, d2: shared Wrapper, x: given_from [d1, d2] Wrapper}, assumptions: {}, fresh: 1 } }"#]]);
}
