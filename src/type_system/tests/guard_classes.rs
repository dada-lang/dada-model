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
          the rule "check_class" at (classes.rs) failed because
            judgment `check_field { decl: g : GuardClass ;, class_ty: RegularClass, class_predicate: share, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
              the rule "check_field" at (classes.rs) failed because
                judgment `prove_predicate { predicate: share(GuardClass), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: RegularClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                  the rule "parameter" at (predicates.rs) failed because
                    judgment `prove_class_predicate { kind: share, parameter: GuardClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: RegularClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                      the rule "class" at (predicates.rs) failed because
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
          the rule "check_class" at (classes.rs) failed because
            judgment `check_field { decl: f : !perm_0 GuardClass ;, class_ty: RegularClass[!perm_0], class_predicate: share, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
              the rule "check_field" at (classes.rs) failed because
                judgment `prove_predicate { predicate: share(!perm_0 GuardClass), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                  the rule "parameter" at (predicates.rs) failed because
                    judgment `prove_class_predicate { kind: share, parameter: !perm_0 GuardClass, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                      the rule "`P T` is share if `T` is share" at (predicates.rs) failed because
                        judgment `prove_predicate { predicate: share(GuardClass), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                          the rule "parameter" at (predicates.rs) failed because
                            judgment `prove_class_predicate { kind: share, parameter: GuardClass, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                              the rule "class" at (predicates.rs) failed because
                                pattern `true` did not match value `false`
                      the rule "`mut T` is share" at (predicates.rs) failed because
                        judgment `prove_is_mut { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                          the rule "is-mut" at (predicates.rs) failed because
                            judgment `prove_predicate { predicate: mut(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                              the rule "parameter" at (predicates.rs) failed because
                                pattern `true` did not match value `false`
                      the rule "`shared T` is share" at (predicates.rs) failed because
                        judgment `prove_is_copy { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                          the rule "is" at (predicates.rs) failed because
                            judgment `prove_predicate { predicate: copy(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
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
                let gc2 = gc1.share;
            }
        }
      }, expect_test::expect![[r#"
          the rule "check_class" at (classes.rs) failed because
            judgment `check_method { decl: fn main (given self) -> () { let gc1 : GuardClass = new GuardClass () ; let gc2 = gc1 . share ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
              the rule "check_method" at (methods.rs) failed because
                judgment `check_body { body: { let gc1 : GuardClass = new GuardClass () ; let gc2 = gc1 . share ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                  the rule "block" at (methods.rs) failed because
                    judgment `can_type_expr_as { expr: { let gc1 : GuardClass = new GuardClass () ; let gc2 = gc1 . share ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                      the rule "can_type_expr_as" at (expressions.rs) failed because
                        judgment `type_expr_as { expr: { let gc1 : GuardClass = new GuardClass () ; let gc2 = gc1 . share ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                          the rule "type_expr_as" at (expressions.rs) failed because
                            judgment `type_expr { expr: { let gc1 : GuardClass = new GuardClass () ; let gc2 = gc1 . share ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                              the rule "block" at (expressions.rs) failed because
                                judgment `type_block { block: { let gc1 : GuardClass = new GuardClass () ; let gc2 = gc1 . share ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                  the rule "place" at (blocks.rs) failed because
                                    judgment `type_statements { statements: [let gc1 : GuardClass = new GuardClass () ;, let gc2 = gc1 . share ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                      the rule "type_statements" at (statements.rs) failed because
                                        judgment `type_statements_with_final_ty { statements: [let gc1 : GuardClass = new GuardClass () ;, let gc2 = gc1 . share ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                          the rule "cons" at (statements.rs) failed because
                                            judgment `type_statements_with_final_ty { statements: [let gc2 = gc1 . share ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, gc1: GuardClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                              the rule "cons" at (statements.rs) failed because
                                                judgment `type_statement { statement: let gc2 = gc1 . share ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, gc1: GuardClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                  the rule "let" at (statements.rs) failed because
                                                    judgment `type_expr { expr: gc1 . share, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, gc1: GuardClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                      the rule "share place" at (expressions.rs) failed because
                                                        judgment `prove_is_shareable { a: GuardClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, gc1: GuardClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                          the rule "is" at (predicates.rs) failed because
                                                            judgment `prove_predicate { predicate: share(GuardClass), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, gc1: GuardClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                              the rule "parameter" at (predicates.rs) failed because
                                                                judgment `prove_class_predicate { kind: share, parameter: GuardClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, gc1: GuardClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                  the rule "class" at (predicates.rs) failed because
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
                let gc2 = gc1.share;
            }
        }
      }, expect_test::expect![[r#"
          the rule "check_class" at (classes.rs) failed because
            judgment `check_method { decl: fn main (given self) -> () { let gc1 : GuardClass[RegularClass] = new GuardClass [RegularClass] (new RegularClass ()) ; let gc2 = gc1 . share ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
              the rule "check_method" at (methods.rs) failed because
                judgment `check_body { body: { let gc1 : GuardClass[RegularClass] = new GuardClass [RegularClass] (new RegularClass ()) ; let gc2 = gc1 . share ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                  the rule "block" at (methods.rs) failed because
                    judgment `can_type_expr_as { expr: { let gc1 : GuardClass[RegularClass] = new GuardClass [RegularClass] (new RegularClass ()) ; let gc2 = gc1 . share ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                      the rule "can_type_expr_as" at (expressions.rs) failed because
                        judgment `type_expr_as { expr: { let gc1 : GuardClass[RegularClass] = new GuardClass [RegularClass] (new RegularClass ()) ; let gc2 = gc1 . share ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                          the rule "type_expr_as" at (expressions.rs) failed because
                            judgment `type_expr { expr: { let gc1 : GuardClass[RegularClass] = new GuardClass [RegularClass] (new RegularClass ()) ; let gc2 = gc1 . share ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                              the rule "block" at (expressions.rs) failed because
                                judgment `type_block { block: { let gc1 : GuardClass[RegularClass] = new GuardClass [RegularClass] (new RegularClass ()) ; let gc2 = gc1 . share ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                  the rule "place" at (blocks.rs) failed because
                                    judgment `type_statements { statements: [let gc1 : GuardClass[RegularClass] = new GuardClass [RegularClass] (new RegularClass ()) ;, let gc2 = gc1 . share ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                      the rule "type_statements" at (statements.rs) failed because
                                        judgment `type_statements_with_final_ty { statements: [let gc1 : GuardClass[RegularClass] = new GuardClass [RegularClass] (new RegularClass ()) ;, let gc2 = gc1 . share ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                          the rule "cons" at (statements.rs) failed because
                                            judgment `type_statements_with_final_ty { statements: [let gc2 = gc1 . share ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, gc1: GuardClass[RegularClass]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                              the rule "cons" at (statements.rs) failed because
                                                judgment `type_statement { statement: let gc2 = gc1 . share ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, gc1: GuardClass[RegularClass]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                  the rule "let" at (statements.rs) failed because
                                                    judgment `type_expr { expr: gc1 . share, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, gc1: GuardClass[RegularClass]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                      the rule "share place" at (expressions.rs) failed because
                                                        judgment `prove_is_shareable { a: GuardClass[RegularClass], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, gc1: GuardClass[RegularClass]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                          the rule "is" at (predicates.rs) failed because
                                                            judgment `prove_predicate { predicate: share(GuardClass[RegularClass]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, gc1: GuardClass[RegularClass]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                              the rule "parameter" at (predicates.rs) failed because
                                                                judgment `prove_class_predicate { kind: share, parameter: GuardClass[RegularClass], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, gc1: GuardClass[RegularClass]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                  the rule "class" at (predicates.rs) failed because
                                                                    pattern `true` did not match value `false`"#]]);
}
