use formality_core::test_util::ResultTestExt;

use crate::{dada_lang::term, type_system::check_program};

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
                    let bar = share foo;
                    let i = give foo.i;
                    give bar;
                    ();
                }
            }
        ",
    )).assert_err(
        expect_test::expect![[r#"
            check program `class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = give foo . i ; give bar ; () ; } }`

            Caused by:
                0: check class named `TheClass`
                1: check method named `empty_method`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (22) ; let bar = foo ; let i = give foo . i ; give bar ; () ; }, as_ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = give foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/type_system/type_expr.rs:26:14) because
                       judgment `type_expr_as { expr: { let foo = new Foo (22) ; let bar = foo ; let i = give foo . i ; give bar ; () ; }, as_ty: (), env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = give foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/type_system/type_expr.rs:43:14) because
                           judgment `type_expr { expr: { let foo = new Foo (22) ; let bar = foo ; let i = give foo . i ; give bar ; () ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = give foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/type_system/type_expr.rs:63:14) because
                               judgment `type_block { block: { let foo = new Foo (22) ; let bar = foo ; let i = give foo . i ; give bar ; () ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = give foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/type_system/type_expr.rs:267:14) because
                                   judgment `"flat_map"` failed at the following rule(s):
                                     failed at (src/type_system/quantifiers.rs:27:27) because
                                       judgment `"flat_map"` failed at the following rule(s):
                                         failed at (src/type_system/quantifiers.rs:27:27) because
                                           judgment `type_statement { statement: let i = give foo . i ;, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = give foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                             the rule "let" failed at step #0 (src/type_system/type_expr.rs:241:14) because
                                               judgment `type_expr { expr: give foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = give foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                 the rule "give place" failed at step #1 (src/type_system/type_expr.rs:97:14) because
                                                   judgment `access_permitted { access: give, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = give foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                     the rule "nil" failed at step #1 (src/type_system/type_accessible.rs:24:14) because
                                                       judgment `variables_permit_access { variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], access: give, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = give foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                         the rule "cons" failed at step #2 (src/type_system/type_accessible.rs:50:14) because
                                                           judgment `variables_permit_access { variables: [foo : Foo, bar : shared (foo) Foo], access: give, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = give foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                             the rule "cons" failed at step #2 (src/type_system/type_accessible.rs:50:14) because
                                                               judgment `variables_permit_access { variables: [bar : shared (foo) Foo], access: give, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = give foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                 the rule "cons" failed at step #1 (src/type_system/type_accessible.rs:49:14) because
                                                                   judgment `ty_permits_access { ty: shared (foo) Foo, access: give, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = give foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                     the rule "ty" failed at step #0 (src/type_system/type_accessible.rs:123:14) because
                                                                       judgment `perm_permits_access { perm: shared (foo), access: give, place: foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> () { let foo = new Foo (22) ; let bar = foo ; let i = give foo . i ; give bar ; () ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo, bar : shared (foo) Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                                                         the rule "disjoint" failed at step #0 (src/type_system/type_accessible.rs:155:17) because
                                                                           condition evaluted to false: `place_disjoint_from_all_of(&accessed_place, &perm_places)`
       "#]],
    )
}
