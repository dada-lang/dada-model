use formality_core::test_util::ResultTestExt;

use crate::{dada_lang::term, type_system::check_program};

mod lock_guard;

#[test]
#[allow(non_snake_case)]
fn regular_class_cannot_hold_guard_class() {
    check_program(&term(
        "
        guard class GuardClass { }

        class RegularClass
        {
            g: GuardClass;
        }
      ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `guard class GuardClass { } class RegularClass { g : GuardClass ; }`

        Caused by:
            0: check class named `RegularClass`
            1: check field named `g`
            2: judgment `prove_predicate { predicate: share(GuardClass), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: RegularClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `prove_class_predicate { kind: share, parameter: GuardClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: RegularClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                     the rule "class" failed at step #0 (src/file.rs:LL:CC) because
                       pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn guard_class_can_hold_guard_class() {
    check_program(&term(
        "
        guard class GuardClass { }

        guard class AnotherGuardClass
        {
            g: GuardClass;
        }
      ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn guard_class_can_hold_regular_class() {
    check_program(&term(
        "
        class RegularClass { }

        guard class GuardClass
        {
            g: RegularClass;
        }
      ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn regular_class_cannot_hold_P_guard_class() {
    check_program(&term(
        "
        class RegularClass[perm P] {
            f: P GuardClass;
        }

        guard class GuardClass
        {
        }
      ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class RegularClass [perm] { f : ^perm0_0 GuardClass ; } guard class GuardClass { }`

        Caused by:
            0: check class named `RegularClass`
            1: check field named `f`
            2: judgment `prove_predicate { predicate: share(!perm_0 GuardClass), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `prove_class_predicate { kind: share, parameter: !perm_0 GuardClass, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                     the rule "`P T` is share if `T` is share" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `prove_predicate { predicate: share(GuardClass), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `prove_class_predicate { kind: share, parameter: GuardClass, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "class" failed at step #0 (src/file.rs:LL:CC) because
                               pattern `true` did not match value `false`
                     the rule "`leased T` is share" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `prove_is_leased { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "is-leased" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `prove_predicate { predicate: leased(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "leased = unique + lent" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `prove_is_unique { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `prove_predicate { predicate: unique(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                       pattern `true` did not match value `false`
                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                               pattern `true` did not match value `false`
                     the rule "`shared T` is share" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `prove_is_shared { a: !perm_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `prove_predicate { predicate: shared(!perm_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: RegularClass[!perm_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                               pattern `true` did not match value `false`"#]]);
}

// FIXME: We use `leased(P)` here but would be better served with a predicate
// that covers `leased | our | ref[]` (i.e., "not my").
#[test]
#[allow(non_snake_case)]
fn regular_class_can_hold_leased_guard_class() {
    check_program(&term(
        "
        class RegularClass[perm P]
        where
            leased(P),
        {
            f: P GuardClass;
        }

        guard class GuardClass
        {
        }
      ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

#[test]
#[allow(non_snake_case)]
fn cannot_share_guard_class() {
    check_program(&term(
        "
        guard class GuardClass
        {
        }

        class Main {
            fn main(my self) {
                let gc1: GuardClass = new GuardClass();
                let gc2 = gc1.share;
            }
        }
      ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `guard class GuardClass { } class Main { fn main (my self) -> () { let gc1 : GuardClass = new GuardClass () ; let gc2 = gc1 . share ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `main`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let gc1 : GuardClass = new GuardClass () ; let gc2 = gc1 . share ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let gc1 : GuardClass = new GuardClass () ; let gc2 = gc1 . share ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let gc1 : GuardClass = new GuardClass () ; let gc2 = gc1 . share ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let gc1 : GuardClass = new GuardClass () ; let gc2 = gc1 . share ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let gc1 : GuardClass = new GuardClass () ;, let gc2 = gc1 . share ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let gc2 = gc1 . share ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, gc1: GuardClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let gc2 = gc1 . share ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, gc1: GuardClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr { expr: gc1 . share, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, gc1: GuardClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "share place" failed at step #2 (src/file.rs:LL:CC) because
                                               judgment `prove_is_shareable { a: GuardClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, gc1: GuardClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `prove_predicate { predicate: share(GuardClass), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, gc1: GuardClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `prove_class_predicate { kind: share, parameter: GuardClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, gc1: GuardClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "class" failed at step #0 (src/file.rs:LL:CC) because
                                                           pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn cannot_share_guard_class_with_regular_generic() {
    check_program(&term(
        "
        guard class GuardClass[ty T]
        {
            t: T;
        }

        class RegularClass
        {
        }

        class Main {
            fn main(my self) {
                let gc1: GuardClass[RegularClass] = new GuardClass[RegularClass](new RegularClass());
                let gc2 = gc1.share;
            }
        }
      ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `guard class GuardClass [ty] { t : ^ty0_0 ; } class RegularClass { } class Main { fn main (my self) -> () { let gc1 : GuardClass[RegularClass] = new GuardClass [RegularClass] (new RegularClass ()) ; let gc2 = gc1 . share ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `main`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let gc1 : GuardClass[RegularClass] = new GuardClass [RegularClass] (new RegularClass ()) ; let gc2 = gc1 . share ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let gc1 : GuardClass[RegularClass] = new GuardClass [RegularClass] (new RegularClass ()) ; let gc2 = gc1 . share ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let gc1 : GuardClass[RegularClass] = new GuardClass [RegularClass] (new RegularClass ()) ; let gc2 = gc1 . share ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let gc1 : GuardClass[RegularClass] = new GuardClass [RegularClass] (new RegularClass ()) ; let gc2 = gc1 . share ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let gc1 : GuardClass[RegularClass] = new GuardClass [RegularClass] (new RegularClass ()) ;, let gc2 = gc1 . share ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let gc2 = gc1 . share ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, gc1: GuardClass[RegularClass]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let gc2 = gc1 . share ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, gc1: GuardClass[RegularClass]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr { expr: gc1 . share, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, gc1: GuardClass[RegularClass]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "share place" failed at step #2 (src/file.rs:LL:CC) because
                                               judgment `prove_is_shareable { a: GuardClass[RegularClass], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, gc1: GuardClass[RegularClass]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `prove_predicate { predicate: share(GuardClass[RegularClass]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, gc1: GuardClass[RegularClass]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `prove_class_predicate { kind: share, parameter: GuardClass[RegularClass], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, gc1: GuardClass[RegularClass]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "class" failed at step #0 (src/file.rs:LL:CC) because
                                                           pattern `true` did not match value `false`"#]]);
}
