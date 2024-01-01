use formality_core::Fallible;

use crate::{dada_lang::term, test::check_program_errs, type_system::check_program};

/// Check sharing a field from a leased value errs.
#[test]
#[allow(non_snake_case)]
fn share_field_of_leased_value() -> Fallible<()> {
    check_program_errs(
        &term(
            "
                class Foo {
                    i: Int;
                }

                class TheClass {
                    fn empty_method(my self) {
                        let foo = new Foo(22);
                        let bar = lease foo;
                        let i = share foo.i;
                        give bar;
                        ();
                    }
                }
            ",
        ),
        expect_test::expect![[r#"
            check program `class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; let i = foo . i ; give bar ; () ; } }`

            Caused by:
                0: check class named `TheClass`
                1: check method named `empty_method`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (22) ; let bar = lease foo ; let i = foo . i ; give bar ; () ; }, as_ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; let i = foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (22) ; let bar = lease foo ; let i = foo . i ; give bar ; () ; }, as_ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; let i = foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (22) ; let bar = lease foo ; let i = foo . i ; give bar ; () ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; let i = foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (22) ; let bar = lease foo ; let i = foo . i ; give bar ; () ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; let i = foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `"flat_map"` failed at the following rule(s):
                                     failed at (src/file.rs:LL:CC) because
                                       judgment `"flat_map"` failed at the following rule(s):
                                         failed at (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: let i = foo . i ;, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; let i = foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : leased (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                             the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; let i = foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : leased (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                 the rule "share|lease place" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `access_permitted { access: share, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; let i = foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : leased (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                     the rule "nil" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `variables_permit_access { variables: [self : my TheClass, foo : Foo, bar : leased (foo) Foo], access: share, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; let i = foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : leased (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                                           judgment `variables_permit_access { variables: [foo : Foo, bar : leased (foo) Foo], access: share, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; let i = foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : leased (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                             the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                                               judgment `variables_permit_access { variables: [bar : leased (foo) Foo], access: share, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; let i = foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : leased (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `ty_permits_access { ty: leased (foo) Foo, access: share, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; let i = foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : leased (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                     the rule "ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `perm_permits_access { perm: leased (foo), access: share, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = lease foo ; let i = foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : leased (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                         the rule "disjoint" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `place_disjoint_from_all_of(&accessed_place, &perm_places)`"#]],
    )
}

/// Check sharing a field from a shared value is ok.
#[test]
#[allow(non_snake_case)]
fn share_field_of_shared_value() -> Fallible<()> {
    check_program(&term(
        "
            class Foo {
                i: Int;
            }

            class TheClass {
                fn empty_method(my self) {
                    let foo = new Foo(22);
                    let bar = share foo;
                    let i = share foo.i;
                    give bar;
                    ();
                }
            }
        ",
    ))
}

/// Check leasing a field from a shared value is not ok.
#[test]
#[allow(non_snake_case)]
fn lease_field_of_shared_value() -> Fallible<()> {
    check_program_errs(
        &term(
            "
            class Foo {
                i: Int;
            }

            class TheClass {
                fn empty_method(my self) {
                    let foo = new Foo(22);
                    let bar = share foo;
                    let i = lease foo.i;
                    give bar;
                    ();
                }
            }
        ",
        ),
        expect_test::expect![[r#"
            check program `class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = lease foo . i ; give bar ; () ; } }`

            Caused by:
                0: check class named `TheClass`
                1: check method named `empty_method`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (22) ; let bar = foo ; let i = lease foo . i ; give bar ; () ; }, as_ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = lease foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (22) ; let bar = foo ; let i = lease foo . i ; give bar ; () ; }, as_ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = lease foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (22) ; let bar = foo ; let i = lease foo . i ; give bar ; () ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = lease foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (22) ; let bar = foo ; let i = lease foo . i ; give bar ; () ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = lease foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `"flat_map"` failed at the following rule(s):
                                     failed at (src/file.rs:LL:CC) because
                                       judgment `"flat_map"` failed at the following rule(s):
                                         failed at (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: let i = lease foo . i ;, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = lease foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                             the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: lease foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = lease foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                 the rule "share|lease place" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `access_permitted { access: lease, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = lease foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                     the rule "nil" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `variables_permit_access { variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], access: lease, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = lease foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                                           judgment `variables_permit_access { variables: [foo : Foo, bar : shared (foo) Foo], access: lease, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = lease foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                             the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                                               judgment `variables_permit_access { variables: [bar : shared (foo) Foo], access: lease, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = lease foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `ty_permits_access { ty: shared (foo) Foo, access: lease, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = lease foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                     the rule "ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `perm_permits_access { perm: shared (foo), access: lease, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = lease foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                         the rule "disjoint" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `place_disjoint_from_all_of(&accessed_place, &perm_places)`"#]],
    )
}
