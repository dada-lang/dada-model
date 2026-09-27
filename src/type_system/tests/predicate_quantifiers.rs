use formality_core::test;

// Field assignment through multi-place permissions and predicate vocabulary tests.
// Duplication cases live in properties::given_from_duplication_requires_shared_origins.

// --- Field assignment (distinct from the mut predicate) ---

/// Unique origins permit field assignment. This checks the assignment rule's
/// move requirement, not the narrower `mut` predicate. See the property
/// `given_from_mut_requires_mut_origins` for explicit `P is mut` tests.
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

/// A shared alternative prevents field assignment: the receiver might provide
/// only shared access. This is not a direct test of the `mut` predicate.
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
