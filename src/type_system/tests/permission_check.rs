use formality_core::test;
use formality_core::test_util::ResultTestExt;

use crate::{dada_lang::term, type_system::check_program};

/// Check sharing a field from a leased value errs.
#[test]
#[allow(non_snake_case)]
fn share_field_of_leased_value() {
    check_program(
        &term(
            "
                class Foo {
                    i: Int;
                }

                class TheClass {
                    fn empty_method(my self) {
                        let foo = new Foo(22);
                        let bar = foo.lease;
                        let i = foo.i.share;
                        bar.give;
                        ();
                    }
                }
            ",
        ),
    ).assert_err(
        expect_test::expect![[r#"
            check program `class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . lease ; let i = foo . i . share ; bar . give ; () ; } }`

            Caused by:
                0: check class named `TheClass`
                1: check method named `empty_method`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (22) ; let bar = foo . lease ; let i = foo . i . share ; bar . give ; () ; }, as_ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . lease ; let i = foo . i . share ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (22) ; let bar = foo . lease ; let i = foo . i . share ; bar . give ; () ; }, as_ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . lease ; let i = foo . i . share ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (22) ; let bar = foo . lease ; let i = foo . i . share ; bar . give ; () ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . lease ; let i = foo . i . share ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (22) ; let bar = foo . lease ; let i = foo . i . share ; bar . give ; () ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . lease ; let i = foo . i . share ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let foo = new Foo (22) ;, let bar = foo . lease ;, let i = foo . i . share ;, bar . give ;, () ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . lease ; let i = foo . i . share ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let bar = foo . lease ;, let i = foo . i . share ;, bar . give ;, () ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . lease ; let i = foo . i . share ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let i = foo . i . share ;, bar . give ;, () ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . lease ; let i = foo . i . share ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : leased (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: let i = foo . i . share ;, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . lease ; let i = foo . i . share ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : leased (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {bar} } }` failed at the following rule(s):
                                                 the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: foo . i . share, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . lease ; let i = foo . i . share ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : leased (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {bar} } }` failed at the following rule(s):
                                                     the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: share, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . lease ; let i = foo . i . share ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : leased (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {bar} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `env_permits_access { access: share, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . lease ; let i = foo . i . share ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : leased (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {bar} } }` failed at the following rule(s):
                                                             the rule "env_permits_access" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `live_variables_permit_access { variables: {bar}, access: share, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . lease ; let i = foo . i . share ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : leased (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {bar} } }` failed at the following rule(s):
                                                                 the rule "cons, initialized variable" failed at step #2 (src/file.rs:LL:CC) because
                                                                   judgment `ty_permits_access { ty: leased (foo) Foo, access: share, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . lease ; let i = foo . i . share ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : leased (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                     the rule "ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `perm_permits_access { perm: leased (foo), access: share, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . lease ; let i = foo . i . share ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : leased (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                         the rule "disjoint" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `place_disjoint_from_all_of(&accessed_place, &perm_places)`
                                                                             &accessed_place = foo . i
                                                                             &perm_places = {foo}"#]],
    )
}

/// Check sharing a field from a shared value is ok.
#[test]
#[allow(non_snake_case)]
fn share_field_of_shared_value() {
    check_program(&term(
        "
            class Foo {
                i: Int;
            }

            class TheClass {
                fn empty_method(my self) {
                    let foo = new Foo(22);
                    let bar = foo.share;
                    let i = foo.i.share;
                    bar.give;
                    ();
                }
            }
        ",
    ))
    .assert_ok(expect_test::expect!["()"])
}

/// Check leasing a field from a shared value is not ok.
#[test]
#[allow(non_snake_case)]
fn lease_field_of_shared_value() {
    check_program(
        &term(
            "
            class Foo {
                i: Int;
            }

            class TheClass {
                fn empty_method(my self) {
                    let foo = new Foo(22);
                    let bar = foo.share;
                    let i = foo.i.lease;
                    bar.give;
                    ();
                }
            }
        ",
        ),
    ).assert_err(
        expect_test::expect![[r#"
            check program `class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . lease ; bar . give ; () ; } }`

            Caused by:
                0: check class named `TheClass`
                1: check method named `empty_method`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . lease ; bar . give ; () ; }, as_ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . lease ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . lease ; bar . give ; () ; }, as_ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . lease ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . lease ; bar . give ; () ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . lease ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . lease ; bar . give ; () ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . lease ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let foo = new Foo (22) ;, let bar = foo . share ;, let i = foo . i . lease ;, bar . give ;, () ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . lease ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let bar = foo . share ;, let i = foo . i . lease ;, bar . give ;, () ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . lease ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let i = foo . i . lease ;, bar . give ;, () ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . lease ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: let i = foo . i . lease ;, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . lease ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {bar} } }` failed at the following rule(s):
                                                 the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: foo . i . lease, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . lease ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {bar} } }` failed at the following rule(s):
                                                     the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: lease, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . lease ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {bar} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `env_permits_access { access: lease, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . lease ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {bar} } }` failed at the following rule(s):
                                                             the rule "env_permits_access" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `live_variables_permit_access { variables: {bar}, access: lease, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . lease ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {bar} } }` failed at the following rule(s):
                                                                 the rule "cons, initialized variable" failed at step #2 (src/file.rs:LL:CC) because
                                                                   judgment `ty_permits_access { ty: shared (foo) Foo, access: lease, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . lease ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                     the rule "ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `perm_permits_access { perm: shared (foo), access: lease, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . lease ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                         the rule "disjoint" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `place_disjoint_from_all_of(&accessed_place, &perm_places)`
                                                                             &accessed_place = foo . i
                                                                             &perm_places = {foo}"#]],
    )
}

/// Check giving a field from a shared value is not ok.
#[test]
#[allow(non_snake_case)]
fn give_field_of_shared_value() {
    check_program(
        &term(
            "
            class Foo {
                i: Int;
            }

            class TheClass {
                fn empty_method(my self) {
                    let foo = new Foo(22);
                    let bar = foo.share;
                    let i = foo.i.give;
                    bar.give;
                    ();
                }
            }
        ",
        ),
    ).assert_err(
        expect_test::expect![[r#"
            check program `class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . give ; bar . give ; () ; } }`

            Caused by:
                0: check class named `TheClass`
                1: check method named `empty_method`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . give ; bar . give ; () ; }, as_ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . give ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . give ; bar . give ; () ; }, as_ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . give ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . give ; bar . give ; () ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . give ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . give ; bar . give ; () ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . give ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let foo = new Foo (22) ;, let bar = foo . share ;, let i = foo . i . give ;, bar . give ;, () ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . give ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let bar = foo . share ;, let i = foo . i . give ;, bar . give ;, () ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . give ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let i = foo . i . give ;, bar . give ;, () ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . give ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: let i = foo . i . give ;, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . give ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {bar} } }` failed at the following rule(s):
                                                 the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: foo . i . give, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . give ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {bar} } }` failed at the following rule(s):
                                                     the rule "give place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: give, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . give ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {bar} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `env_permits_access { access: give, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . give ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {bar} } }` failed at the following rule(s):
                                                             the rule "env_permits_access" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `live_variables_permit_access { variables: {bar}, access: give, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . give ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {bar} } }` failed at the following rule(s):
                                                                 the rule "cons, initialized variable" failed at step #2 (src/file.rs:LL:CC) because
                                                                   judgment `ty_permits_access { ty: shared (foo) Foo, access: give, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . give ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                     the rule "ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `perm_permits_access { perm: shared (foo), access: give, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo . share ; let i = foo . i . give ; bar . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                         the rule "disjoint" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `place_disjoint_from_all_of(&accessed_place, &perm_places)`
                                                                             &accessed_place = foo . i
                                                                             &perm_places = {foo}
                                                                         the rule "disjoint-or-prefix" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `place_disjoint_from_or_prefix_of_all_of(&given_place, &perm_places)`
                                                                             &given_place = foo . i
                                                                             &perm_places = {foo}"#]],
    )
}

/// Check sharing a field from a leased value errs.
#[test]
#[allow(non_snake_case)]
fn share_field_of_leased_value_after_explicit_give() {
    check_program(&term(
        "
                class Foo {
                    i: Int;
                }

                class TheClass {
                    fn empty_method(my self) {
                        let foo = new Foo(22);
                        let bar = foo.lease;
                        bar.give;
                        let i = foo.i.share;
                        ();
                    }
                }
            ",
    ))
    .assert_ok(expect_test::expect!["()"])
}

/// Check that we can permit accessing `foo.i` even though
/// it was leased since `bar` is dead.
#[test]
#[allow(non_snake_case)]
fn share_field_of_leased_value_without_explicit_give() {
    check_program(&term(
        "
                class Foo {
                    i: Int;
                }

                class TheClass {
                    fn empty_method(my self) {
                        let foo = new Foo(22);
                        let bar = foo.lease;
                        let i = foo.i.share;
                        ();
                    }
                }
            ",
    ))
    .assert_ok(expect_test::expect!["()"])
}

#[test]
fn share_field_of_leased_value_but_lease_variable_is_dead() {
    // Here, the variable `q` is dead, but its restrictions must
    // still be enforced because `r` is live.
    check_program(&term(
        "
                class Foo {
                    i: Int;
                }

                class TheClass {
                    fn empty_method(my self) {
                        let p = new Foo(22);
                        let q = p.lease;
                        let r = q.share;
                        let i = p.i.share;
                        r.give;
                        ();
                    }
                }
            ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; } }`

        Caused by:
            0: check class named `TheClass`
            1: check method named `empty_method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; }, as_ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; }, as_ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let p = new Foo (22) ;, let q = p . lease ;, let r = q . share ;, let i = p . i . share ;, r . give ;, () ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let q = p . lease ;, let r = q . share ;, let i = p . i . share ;, r . give ;, () ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let r = q . share ;, let i = p . i . share ;, r . give ;, () ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : Foo, q : leased (p) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let i = p . i . share ;, r . give ;, () ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : Foo, q : leased (p) Foo, r : shared (q) leased (p) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: let i = p . i . share ;, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : Foo, q : leased (p) Foo, r : shared (q) leased (p) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {r} } }` failed at the following rule(s):
                                                 the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: p . i . share, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : Foo, q : leased (p) Foo, r : shared (q) leased (p) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {r} } }` failed at the following rule(s):
                                                     the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: share, place: p . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : Foo, q : leased (p) Foo, r : shared (q) leased (p) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {r} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `env_permits_access { access: share, place: p . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : Foo, q : leased (p) Foo, r : shared (q) leased (p) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {r} } }` failed at the following rule(s):
                                                             the rule "env_permits_access" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `live_variables_permit_access { variables: {r}, access: share, place: p . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : Foo, q : leased (p) Foo, r : shared (q) leased (p) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {r} } }` failed at the following rule(s):
                                                                 the rule "cons, initialized variable" failed at step #2 (src/file.rs:LL:CC) because
                                                                   judgment `ty_permits_access { ty: shared (q) leased (p) Foo, access: share, place: p . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : Foo, q : leased (p) Foo, r : shared (q) leased (p) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                     the rule "ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `perm_permits_access { perm: shared (q), access: share, place: p . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : Foo, q : leased (p) Foo, r : shared (q) leased (p) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                         the rule "disjoint" failed at step #1 (src/file.rs:LL:CC) because
                                                                           judgment `perm_places_permit_access { perm_places: {q}, access: share, place: p . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : Foo, q : leased (p) Foo, r : shared (q) leased (p) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                             the rule "nil" failed at step #1 (src/file.rs:LL:CC) because
                                                                               judgment `ty_permits_access { ty: leased (p) Foo, access: share, place: p . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : Foo, q : leased (p) Foo, r : shared (q) leased (p) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                                 the rule "ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `perm_permits_access { perm: leased (p), access: share, place: p . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : Foo, q : leased (p) Foo, r : shared (q) leased (p) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                                     the rule "disjoint" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       condition evaluted to false: `place_disjoint_from_all_of(&accessed_place, &perm_places)`
                                                                                         &accessed_place = p . i
                                                                                         &perm_places = {p}
                                                                         the rule "shared-shared" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `perm_places_permit_access { perm_places: {q}, access: share, place: p . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : Foo, q : leased (p) Foo, r : shared (q) leased (p) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                             the rule "nil" failed at step #1 (src/file.rs:LL:CC) because
                                                                               judgment `ty_permits_access { ty: leased (p) Foo, access: share, place: p . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : Foo, q : leased (p) Foo, r : shared (q) leased (p) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                                 the rule "ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `perm_permits_access { perm: leased (p), access: share, place: p . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p = new Foo (22) ; let q = p . lease ; let r = q . share ; let i = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : Foo, q : leased (p) Foo, r : shared (q) leased (p) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                                     the rule "disjoint" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       condition evaluted to false: `place_disjoint_from_all_of(&accessed_place, &perm_places)`
                                                                                         &accessed_place = p . i
                                                                                         &perm_places = {p}"#]])
}

#[test]
fn share_field_of_leased_value_but_lease_variable_is_dead_explicit_ty() {
    // Here, the variable `q` is dead, but its restrictions must
    // still be enforced because `r` is live.
    check_program(&term(
        "
                class Foo {
                    i: Int;
                }

                class TheClass {
                    fn empty_method(my self) {
                        let p: my Foo = new Foo(22);
                        let q: leased(p) Foo = p.lease;
                        let r: shared(q) Foo = q.share;
                        let i: shared(p.i) Int = p.i.share;
                        r.give;
                        ();
                    }
                }
            ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; } }`

        Caused by:
            0: check class named `TheClass`
            1: check method named `empty_method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; }, as_ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; }, as_ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let p : my Foo = new Foo (22) ;, let q : leased (p) Foo = p . lease ;, let r : shared (q) Foo = q . share ;, let i : shared (p . i) Int = p . i . share ;, r . give ;, () ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let q : leased (p) Foo = p . lease ;, let r : shared (q) Foo = q . share ;, let i : shared (p . i) Int = p . i . share ;, r . give ;, () ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : my Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let r : shared (q) Foo = q . share ;, let i : shared (p . i) Int = p . i . share ;, r . give ;, () ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : my Foo, q : leased (p) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [let i : shared (p . i) Int = p . i . share ;, r . give ;, () ;], ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : my Foo, q : leased (p) Foo, r : shared (q) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: let i : shared (p . i) Int = p . i . share ;, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : my Foo, q : leased (p) Foo, r : shared (q) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {r} } }` failed at the following rule(s):
                                                 the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr_as { expr: p . i . share, as_ty: shared (p . i) Int, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : my Foo, q : leased (p) Foo, r : shared (q) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {r} } }` failed at the following rule(s):
                                                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `type_expr { expr: p . i . share, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : my Foo, q : leased (p) Foo, r : shared (q) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {r} } }` failed at the following rule(s):
                                                         the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `access_permitted { access: share, place: p . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : my Foo, q : leased (p) Foo, r : shared (q) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {r} } }` failed at the following rule(s):
                                                             the rule "access_permitted" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `env_permits_access { access: share, place: p . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : my Foo, q : leased (p) Foo, r : shared (q) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {r} } }` failed at the following rule(s):
                                                                 the rule "env_permits_access" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `live_variables_permit_access { variables: {r}, access: share, place: p . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : my Foo, q : leased (p) Foo, r : shared (q) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {r} } }` failed at the following rule(s):
                                                                     the rule "cons, initialized variable" failed at step #2 (src/file.rs:LL:CC) because
                                                                       judgment `ty_permits_access { ty: shared (q) Foo, access: share, place: p . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : my Foo, q : leased (p) Foo, r : shared (q) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                         the rule "ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `perm_permits_access { perm: shared (q), access: share, place: p . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : my Foo, q : leased (p) Foo, r : shared (q) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                             the rule "disjoint" failed at step #1 (src/file.rs:LL:CC) because
                                                                               judgment `perm_places_permit_access { perm_places: {q}, access: share, place: p . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : my Foo, q : leased (p) Foo, r : shared (q) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                                 the rule "nil" failed at step #1 (src/file.rs:LL:CC) because
                                                                                   judgment `ty_permits_access { ty: leased (p) Foo, access: share, place: p . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : my Foo, q : leased (p) Foo, r : shared (q) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                                     the rule "ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       judgment `perm_permits_access { perm: leased (p), access: share, place: p . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : my Foo, q : leased (p) Foo, r : shared (q) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                                         the rule "disjoint" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           condition evaluted to false: `place_disjoint_from_all_of(&accessed_place, &perm_places)`
                                                                                             &accessed_place = p . i
                                                                                             &perm_places = {p}
                                                                             the rule "shared-shared" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `perm_places_permit_access { perm_places: {q}, access: share, place: p . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : my Foo, q : leased (p) Foo, r : shared (q) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                                 the rule "nil" failed at step #1 (src/file.rs:LL:CC) because
                                                                                   judgment `ty_permits_access { ty: leased (p) Foo, access: share, place: p . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : my Foo, q : leased (p) Foo, r : shared (q) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                                     the rule "ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                                       judgment `perm_permits_access { perm: leased (p), access: share, place: p . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let p : my Foo = new Foo (22) ; let q : leased (p) Foo = p . lease ; let r : shared (q) Foo = q . share ; let i : shared (p . i) Int = p . i . share ; r . give ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, p : my Foo, q : leased (p) Foo, r : shared (q) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                                         the rule "disjoint" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           condition evaluted to false: `place_disjoint_from_all_of(&accessed_place, &perm_places)`
                                                                                             &accessed_place = p . i
                                                                                             &perm_places = {p}"#]])
}
