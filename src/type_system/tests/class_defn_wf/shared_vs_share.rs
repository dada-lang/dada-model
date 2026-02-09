#[test]
#[allow(non_snake_case)]
fn our_class_cannot_hold_a_share_class_directly() {
    crate::assert_err!("
        class RegularClass { }

        struct class OurClass
        {
            sc: RegularClass;
        }
      ", expect_test::expect![[r#"
          the rule "class" at (predicates.rs) failed because
            pattern `true` did not match value `false`

          the rule "parameter" at (predicates.rs) failed because
            pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn our_class_can_hold_a_share_class_indirectly() {
    crate::assert_ok!("
        class RegularClass { }

        struct class OurClass[ty T]
        {
            sc: T;
        }

        class Main {
            fn main(given self) {
                let rc: RegularClass = new RegularClass();
                let oc: OurClass[RegularClass] = new OurClass[RegularClass](rc.give);
            }
        }
      ");
}
