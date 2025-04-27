use formality_core::test_util::ResultTestExt;

use crate::{dada_lang::term, type_system::check_program};

#[test]
#[allow(non_snake_case)]
fn our_class_cannot_hold_a_share_class_directly() {
    check_program(&term(
        "
        class RegularClass { }

        our class OurClass
        {
            sc: RegularClass;
        }
      ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class RegularClass { } our class OurClass { sc : RegularClass ; }`

        Caused by:
            0: check class named `OurClass`
            1: check field named `sc`
            2: judgment `prove_predicate { predicate: our(RegularClass), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: OurClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `prove_class_predicate { kind: our, parameter: RegularClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: OurClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                     the rule "our types" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `prove_is_our { a: RegularClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: OurClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "prove" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `prove_is_shared { a: RegularClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: OurClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `prove_predicate { predicate: shared(RegularClass), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: OurClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                   pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn our_class_can_hold_a_share_class_indirectly() {
    check_program(&term(
        "
        class RegularClass { }

        our class OurClass[ty T]
        {
            sc: T;
        }

        class Main {
            fn main(my self) {
                let rc: RegularClass = new RegularClass();
                let oc: OurClass[RegularClass] = new OurClass[RegularClass](rc.move);
            }
        }
      ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}
