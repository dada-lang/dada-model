mod lock_given;

#[test]
#[allow(non_snake_case)]
fn regular_class_cannot_hold_guard_class() {
    crate::assert_err!({
        given class GivenClass { }

        class RegularClass
        {
            g: GivenClass;
        }
      }, expect_test::expect![[r#"
          the rule "check_field" at (classes.rs) failed because
            judgment `prove_predicate { predicate: GivenClass is share, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: RegularClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
              the rule "share" at (predicates.rs) failed because
                judgment `prove_share_predicate { p: GivenClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: RegularClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                  the rule "share class" at (predicates.rs) failed because
                    pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn given_class_can_hold_guard_class() {
    crate::assert_ok!({
        given class GivenClass { }

        given class AnotherGuardClass
        {
            g: GivenClass;
        }
      });
}

#[test]
#[allow(non_snake_case)]
fn given_class_can_hold_regular_class() {
    crate::assert_ok!({
        class RegularClass { }

        given class GivenClass
        {
            g: RegularClass;
        }
      });
}

#[test]
#[allow(non_snake_case)]
fn regular_class_cannot_hold_P_guard_class() {
    crate::assert_err!({
        class RegularClass[perm P] {
            f: P GivenClass;
        }

        given class GivenClass
        {
        }
      }, expect_test::expect![[r#"
          the rule "check_field" at (classes.rs) failed because
            judgment `prove_predicate { predicate: !perm_0 GivenClass is share, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
              the rule "share" at (predicates.rs) failed because
                judgment `prove_share_predicate { p: !perm_0 GivenClass, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                  the rule "share P T" at (predicates.rs) failed because
                    judgment `prove_predicate { predicate: GivenClass is share, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                      the rule "share" at (predicates.rs) failed because
                        judgment `prove_share_predicate { p: GivenClass, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                          the rule "share class" at (predicates.rs) failed because
                            pattern `true` did not match value `false`
                  the rule "share copy T" at (predicates.rs) failed because
                    judgment `prove_is_copy { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                      the rule "is" at (predicates.rs) failed because
                        judgment `prove_predicate { predicate: !perm_0 is copy, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                          the rule "copy" at (predicates.rs) failed because
                            src/type_system/predicates.rs:324:1: judgment had no applicable rules: `prove_copy_predicate { p: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }`
                  the rule "share mut T" at (predicates.rs) failed because
                    judgment `prove_is_mut { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                      the rule "is-mut" at (predicates.rs) failed because
                        judgment `prove_predicate { predicate: !perm_0 is mut, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                          the rule "mut" at (predicates.rs) failed because
                            src/type_system/predicates.rs:623:1: judgment had no applicable rules: `prove_mut_predicate { p: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }`"#]]);
}

// FIXME: We use `P is mut` here but would be better served with a predicate
// that covers `leased | shared | ref[]` (i.e., "not given").
#[test]
#[allow(non_snake_case)]
fn regular_class_can_hold_leased_guard_class() {
    crate::assert_ok!({
        class RegularClass[perm P]
        where
            P is mut,
        {
            f: P GivenClass;
        }

        given class GivenClass
        {
        }
      });
}

#[test]
#[allow(non_snake_case)]
fn cannot_share_guard_class() {
    crate::assert_err!({
        given class GivenClass
        {
        }

        class Main {
            fn main(given self) {
                let gc1: GivenClass = new GivenClass();
                let gc2 = gc1.give.share;
            }
        }
      }, expect_test::expect![[r#"
          the rule "share class" at (predicates.rs) failed because
            pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn cannot_share_guard_class_with_regular_generic() {
    crate::assert_err!({
        given class GivenClass[ty T]
        {
            t: T;
        }

        class RegularClass
        {
        }

        class Main {
            fn main(given self) {
                let gc1: GivenClass[RegularClass] = new GivenClass[RegularClass](new RegularClass());
                let gc2 = gc1.give.share;
            }
        }
      }, expect_test::expect![[r#"
          the rule "share class" at (predicates.rs) failed because
            pattern `true` did not match value `false`"#]]);
}
