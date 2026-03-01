mod lock_guard;

#[test]
#[allow(non_snake_case)]
fn regular_class_cannot_hold_guard_class() {
    crate::assert_err!({
        guard class GuardClass { }

        class RegularClass
        {
            g: GuardClass;
        }
      }, expect_test::expect![[r#"
          the rule "check_field" at (classes.rs) failed because
            judgment `prove_predicate { predicate: share(GuardClass), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: RegularClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
              the rule "parameter" at (predicates.rs) failed because
                pattern `true` did not match value `false`
              the rule "share class" at (predicates.rs) failed because
                pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn guard_class_can_hold_guard_class() {
    crate::assert_ok!({
        guard class GuardClass { }

        guard class AnotherGuardClass
        {
            g: GuardClass;
        }
      });
}

#[test]
#[allow(non_snake_case)]
fn guard_class_can_hold_regular_class() {
    crate::assert_ok!({
        class RegularClass { }

        guard class GuardClass
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
            f: P GuardClass;
        }

        guard class GuardClass
        {
        }
      }, expect_test::expect![[r#"
          the rule "check_field" at (classes.rs) failed because
            judgment `prove_predicate { predicate: share(!perm_0 GuardClass), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
              the rule "parameter" at (predicates.rs) failed because
                pattern `true` did not match value `false`
              the rule "share P T" at (predicates.rs) failed because
                judgment `prove_predicate { predicate: share(GuardClass), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                  the rule "parameter" at (predicates.rs) failed because
                    pattern `true` did not match value `false`
                  the rule "share class" at (predicates.rs) failed because
                    pattern `true` did not match value `false`
              the rule "share copy T" at (predicates.rs) failed because
                judgment `prove_is_copy { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                  the rule "is" at (predicates.rs) failed because
                    judgment `prove_predicate { predicate: copy(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                      the rule "parameter" at (predicates.rs) failed because
                        pattern `true` did not match value `false`
              the rule "share mut T" at (predicates.rs) failed because
                judgment `prove_is_mut { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                  the rule "is-mut" at (predicates.rs) failed because
                    judgment `prove_predicate { predicate: mut(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                      the rule "parameter" at (predicates.rs) failed because
                        pattern `true` did not match value `false`"#]]);
}

// FIXME: We use `mut(P)` here but would be better served with a predicate
// that covers `leased | shared | ref[]` (i.e., "not given").
#[test]
#[allow(non_snake_case)]
fn regular_class_can_hold_leased_guard_class() {
    crate::assert_ok!({
        class RegularClass[perm P]
        where
            mut(P),
        {
            f: P GuardClass;
        }

        guard class GuardClass
        {
        }
      });
}

#[test]
#[allow(non_snake_case)]
fn cannot_share_guard_class() {
    crate::assert_err!({
        guard class GuardClass
        {
        }

        class Main {
            fn main(given self) {
                let gc1: GuardClass = new GuardClass();
                let gc2 = gc1.give.share;
            }
        }
      }, expect_test::expect![[r#"
          the rule "parameter" at (predicates.rs) failed because
            pattern `true` did not match value `false`

          the rule "share class" at (predicates.rs) failed because
            pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn cannot_share_guard_class_with_regular_generic() {
    crate::assert_err!({
        guard class GuardClass[ty T]
        {
            t: T;
        }

        class RegularClass
        {
        }

        class Main {
            fn main(given self) {
                let gc1: GuardClass[RegularClass] = new GuardClass[RegularClass](new RegularClass());
                let gc2 = gc1.give.share;
            }
        }
      }, expect_test::expect![[r#"
          the rule "parameter" at (predicates.rs) failed because
            pattern `true` did not match value `false`

          the rule "share class" at (predicates.rs) failed because
            pattern `true` did not match value `false`"#]]);
}
