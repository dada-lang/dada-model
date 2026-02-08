mod lock_guard;

#[test]
#[allow(non_snake_case)]
fn regular_class_cannot_hold_guard_class() {
    crate::assert_err!("
        guard class GuardClass { }

        class RegularClass
        {
            g: GuardClass;
        }
      ", expect_test::expect![[r#"
          the rule "class" at (predicates.rs) failed because
            pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn guard_class_can_hold_guard_class() {
    crate::assert_ok!("
        guard class GuardClass { }

        guard class AnotherGuardClass
        {
            g: GuardClass;
        }
      ");
}

#[test]
#[allow(non_snake_case)]
fn guard_class_can_hold_regular_class() {
    crate::assert_ok!("
        class RegularClass { }

        guard class GuardClass
        {
            g: RegularClass;
        }
      ");
}

#[test]
#[allow(non_snake_case)]
fn regular_class_cannot_hold_P_guard_class() {
    crate::assert_err!("
        class RegularClass[perm P] {
            f: P GuardClass;
        }

        guard class GuardClass
        {
        }
      ", expect_test::expect![[r#"
          the rule "class" at (predicates.rs) failed because
            pattern `true` did not match value `false`

          the rule "parameter" at (predicates.rs) failed because
            pattern `true` did not match value `false`

          the rule "parameter" at (predicates.rs) failed because
            pattern `true` did not match value `false`"#]]);
}

// FIXME: We use `leased(P)` here but would be better served with a predicate
// that covers `leased | our | ref[]` (i.e., "not given").
#[test]
#[allow(non_snake_case)]
fn regular_class_can_hold_leased_guard_class() {
    crate::assert_ok!("
        class RegularClass[perm P]
        where
            leased(P),
        {
            f: P GuardClass;
        }

        guard class GuardClass
        {
        }
      ");
}

#[test]
#[allow(non_snake_case)]
fn cannot_share_guard_class() {
    crate::assert_err!("
        guard class GuardClass
        {
        }

        class Main {
            fn main(given self) {
                let gc1: GuardClass = new GuardClass();
                let gc2 = gc1.share;
            }
        }
      ", expect_test::expect![[r#"
          the rule "class" at (predicates.rs) failed because
            pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn cannot_share_guard_class_with_regular_generic() {
    crate::assert_err!("
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
                let gc2 = gc1.share;
            }
        }
      ", expect_test::expect![[r#"
          the rule "class" at (predicates.rs) failed because
            pattern `true` did not match value `false`"#]]);
}
