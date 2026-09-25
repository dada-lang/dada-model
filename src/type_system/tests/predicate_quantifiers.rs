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
/// Giving twice should succeed because the value is shared.
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
        the rule "give" at (expressions.rs) failed because
          condition evaluted to false: `!live_after.is_live(place)`
            live_after = LivePlaces { accessed: {x}, traversed: {} }
            place = x"#]]);
}

/// given_from[d1, d2] where d1 is shared but d2 is NOT copy → NOT copy.
/// This is the key bug: with the old ANY rule, given_from[d1, d2] would be
/// considered copy because d1 is shared. But the value could have come from d2,
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
        the rule "give" at (expressions.rs) failed because
          condition evaluted to false: `!live_after.is_live(place)`
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
        the rule "give" at (expressions.rs) failed because
          condition evaluted to false: `!live_after.is_live(place)`
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

/// given_from[d1, d2] where d1 is non-copy (mut) but d2 is shared (not mut) → NOT mut.
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
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn test (given self d1 : given Wrapper, d2 : shared Wrapper, x : given_from [d1, d2] Wrapper) -> () { x . value = 42 ; () ; } } }`"]);
}

/// Shared means duplicable, independently of whether a value is fully owned
/// or can be converted to shared form. Group the contrasting cases together.
#[test]
fn shared_owned_and_share_are_distinct() {
    use crate::grammar::{Program, Ty, Var};
    use crate::type_system::{
        env::Env,
        predicates::{prove_is_owned, prove_is_shareable, prove_is_shared, prove_is_shared_owned},
    };
    use std::sync::Arc;

    let program: Arc<Program> = crate::dada_lang::term("class Data {} given class Guard {}");
    let env = Env::new(program)
        .push_local_variable(
            crate::dada_lang::term::<Var>("x"),
            crate::dada_lang::term::<Ty>("Data"),
        )
        .unwrap()
        .push_local_variable(
            crate::dada_lang::term::<Var>("g"),
            crate::dada_lang::term::<Ty>("Guard"),
        )
        .unwrap();

    for (source, shared, owned, share) in [
        ("given Data", false, true, true),
        ("shared Data", true, true, true),
        ("ref[x] Data", true, false, true),
        ("mut[x] Data", false, false, true),
        ("given Guard", false, true, false),
        ("ref[g] Guard", true, false, true),
        ("mut[g] Guard", false, false, true),
        ("or(ref[x], shared) Data", true, false, true),
    ] {
        let ty: Ty = crate::dada_lang::term(source);
        assert_eq!(
            prove_is_shared(&env, &ty).is_proven(),
            shared,
            "{source}: shared"
        );
        assert_eq!(
            prove_is_owned(&env, &ty).is_proven(),
            owned,
            "{source}: owned"
        );
        assert_eq!(
            prove_is_shareable(&env, &ty).is_proven(),
            share,
            "{source}: share"
        );
        assert_eq!(
            prove_is_shared_owned(&env, &ty).is_proven(),
            shared && owned,
            "{source}: shared + owned"
        );
    }
}

/// Replacing the old shared predicate must preserve both its requirements on
/// shared-class fields, including when their permission is generic.
#[test]
fn shared_class_fields_still_require_owned() {
    crate::assert_ok!({
        class Data {}
        shared class Holder[perm P] where P is relative, P is shared, P is owned {
            value: shared P Data;
        }
    });
    crate::assert_err!({
        class Data {}
        shared class Holder[perm P] where P is relative, P is shared {
            value: shared P Data;
        }
    }, expect_test::expect![[r#"
        the rule "check_field" at (classes.rs) failed because
          judgment `prove_predicate { predicate: shared !perm_0 Data is owned, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: Holder[!perm_0]}, assumptions: {!perm_0 is shared, !perm_0 is relative}, fresh: 0 } }` failed at the following rule(s):
            the rule "owned" at (predicates.rs) failed because
              judgment `prove_owned_predicate { p: shared !perm_0 Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: Holder[!perm_0]}, assumptions: {!perm_0 is shared, !perm_0 is relative}, fresh: 0 } }` failed at the following rule(s):
                the rule "apply-perm" at (predicates.rs) failed because
                  judgment `prove_owned_composed_predicate { lhs: shared !perm_0, rhs: Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: Holder[!perm_0]}, assumptions: {!perm_0 is shared, !perm_0 is relative}, fresh: 0 } }` failed at the following rule(s):
                    the rule "owned-lhs-rhs" at (predicates.rs) failed because
                      judgment `prove_is_owned { a: shared !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: Holder[!perm_0]}, assumptions: {!perm_0 is shared, !perm_0 is relative}, fresh: 0 } }` failed at the following rule(s):
                        the rule "is-owned" at (predicates.rs) failed because
                          judgment `prove_predicate { predicate: shared !perm_0 is owned, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: Holder[!perm_0]}, assumptions: {!perm_0 is shared, !perm_0 is relative}, fresh: 0 } }` failed at the following rule(s):
                            the rule "owned" at (predicates.rs) failed because
                              judgment `prove_owned_predicate { p: shared !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: Holder[!perm_0]}, assumptions: {!perm_0 is shared, !perm_0 is relative}, fresh: 0 } }` failed at the following rule(s):
                                the rule "perm-apply" at (predicates.rs) failed because
                                  judgment `prove_owned_composed_predicate { lhs: shared, rhs: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: Holder[!perm_0]}, assumptions: {!perm_0 is shared, !perm_0 is relative}, fresh: 0 } }` failed at the following rule(s):
                                    the rule "owned-lhs-rhs" at (predicates.rs) failed because
                                      judgment `prove_is_owned { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: Holder[!perm_0]}, assumptions: {!perm_0 is shared, !perm_0 is relative}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "is-owned" at (predicates.rs) failed because
                                          judgment `prove_predicate { predicate: !perm_0 is owned, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: Holder[!perm_0]}, assumptions: {!perm_0 is shared, !perm_0 is relative}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "owned" at (predicates.rs) failed because
                                              judgment had no applicable rules: `prove_owned_predicate { p: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: Holder[!perm_0]}, assumptions: {!perm_0 is shared, !perm_0 is relative}, fresh: 0 } }`
                                    the rule "shared-rhs" at (predicates.rs) failed because
                                      judgment `prove_is_owned { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: Holder[!perm_0]}, assumptions: {!perm_0 is shared, !perm_0 is relative}, fresh: 0 } }` failed at the following rule(s):
                                        the rule "is-owned" at (predicates.rs) failed because
                                          judgment `prove_predicate { predicate: !perm_0 is owned, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: Holder[!perm_0]}, assumptions: {!perm_0 is shared, !perm_0 is relative}, fresh: 0 } }` failed at the following rule(s):
                                            the rule "owned" at (predicates.rs) failed because
                                              judgment had no applicable rules: `prove_owned_predicate { p: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: Holder[!perm_0]}, assumptions: {!perm_0 is shared, !perm_0 is relative}, fresh: 0 } }`
                    the rule "shared-rhs" at (predicates.rs) failed because
                      judgment `prove_is_shared { a: Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: Holder[!perm_0]}, assumptions: {!perm_0 is shared, !perm_0 is relative}, fresh: 0 } }` failed at the following rule(s):
                        the rule "is" at (predicates.rs) failed because
                          judgment `prove_predicate { predicate: Data is shared, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: Holder[!perm_0]}, assumptions: {!perm_0 is shared, !perm_0 is relative}, fresh: 0 } }` failed at the following rule(s):
                            the rule "shared" at (predicates.rs) failed because
                              judgment had no applicable rules: `prove_shared_predicate { p: Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: Holder[!perm_0]}, assumptions: {!perm_0 is shared, !perm_0 is relative}, fresh: 0 } }`"#]]);
}
