#[test]
#[allow(non_snake_case)]
fn our_class_cannot_hold_a_share_class_directly() {
    crate::assert_err!({
        class RegularClass { }

        struct class OurClass
        {
            sc: RegularClass;
        }
      }, expect_test::expect![[r#"
          the rule "check_class" at (classes.rs) failed because
            judgment `check_field { decl: sc : RegularClass ;, class_ty: OurClass, class_predicate: struct, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
              the rule "check_field" at (classes.rs) failed because
                judgment `prove_predicate { predicate: struct(RegularClass), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: OurClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                  the rule "parameter" at (predicates.rs) failed because
                    judgment `prove_class_predicate { kind: struct, parameter: RegularClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: OurClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                      the rule "class" at (predicates.rs) failed because
                        pattern `true` did not match value `false`
                      the rule "shared types" at (predicates.rs) failed because
                        judgment `prove_is_copy_owned { a: RegularClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: OurClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                          the rule "prove" at (predicates.rs) failed because
                            judgment `prove_is_copy { a: RegularClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: OurClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                              the rule "is" at (predicates.rs) failed because
                                judgment `prove_predicate { predicate: copy(RegularClass), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: OurClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                  the rule "parameter" at (predicates.rs) failed because
                                    pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn our_class_can_hold_a_share_class_indirectly() {
    crate::assert_ok!({
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
      });
}
