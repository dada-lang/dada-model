use crate::{dada_lang::term, test::check_program_errs, type_system::check_program};
use formality_core::{test, Fallible};

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn give_same_field_twice() -> Fallible<()> {
    check_program_errs(
        &term(
            "
        class Foo {
            i: Int;
        }

        class TheClass {
            fn empty_method(my self) -> Int {
                let foo = new Foo(22);
                give foo.i;
                give foo.i;
            }
        }
    ",
        ),
        expect_test::expect![[r#"
            check program `class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo . i ; } }`

            Caused by:
                0: check class named `TheClass`
                1: check method named `empty_method`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (22) ; give foo . i ; give foo . i ; }, as_ty: Int, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (22) ; give foo . i ; give foo . i ; }, as_ty: Int, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (22) ; give foo . i ; give foo . i ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (22) ; give foo . i ; give foo . i ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `"flat_map"` failed at the following rule(s):
                                     failed at (src/file.rs:LL:CC) because
                                       judgment `"flat_map"` failed at the following rule(s):
                                         failed at (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: give foo . i ;, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo . i} } }` failed at the following rule(s):
                                             the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: give foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo . i} } }` failed at the following rule(s):
                                                 the rule "give place" failed at step #0 (src/file.rs:LL:CC) because
                                                   condition evaluted to false: `!flow.is_moved(&place)`"#]],
    )
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn give_field_of_given_variable() -> Fallible<()> {
    check_program_errs(
        &term(
            "
        class Foo {
            i: Int;
        }

        class TheClass {
            fn empty_method(my self) -> Int {
                let foo = new Foo(22);
                give foo;
                give foo.i;
            }
        }
    ",
        ),
        expect_test::expect![[r#"
            check program `class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo ; give foo . i ; } }`

            Caused by:
                0: check class named `TheClass`
                1: check method named `empty_method`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (22) ; give foo ; give foo . i ; }, as_ty: Int, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (22) ; give foo ; give foo . i ; }, as_ty: Int, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (22) ; give foo ; give foo . i ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (22) ; give foo ; give foo . i ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `"flat_map"` failed at the following rule(s):
                                     failed at (src/file.rs:LL:CC) because
                                       judgment `"flat_map"` failed at the following rule(s):
                                         failed at (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: give foo . i ;, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo} } }` failed at the following rule(s):
                                             the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: give foo . i, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo ; give foo . i ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo} } }` failed at the following rule(s):
                                                 the rule "give place" failed at step #0 (src/file.rs:LL:CC) because
                                                   condition evaluted to false: `!flow.is_moved(&place)`"#]],
    )
}

/// Check returning a shared instance of a class when an owned instance is expected.
#[test]
#[allow(non_snake_case)]
fn give_variable_with_given_field() -> Fallible<()> {
    check_program_errs(
        &term(
            "
        class Foo {
            i: Int;
        }

        class TheClass {
            fn empty_method(my self) -> Int {
                let foo = new Foo(22);
                give foo.i;
                give foo;
            }
        }
    ",
        ),
        expect_test::expect![[r#"
            check program `class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo ; } }`

            Caused by:
                0: check class named `TheClass`
                1: check method named `empty_method`
                2: check function body
                3: judgment `can_type_expr_as { expr: { let foo = new Foo (22) ; give foo . i ; give foo ; }, as_ty: Int, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                     the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr_as { expr: { let foo = new Foo (22) ; give foo . i ; give foo ; }, as_ty: Int, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                         the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_expr { expr: { let foo = new Foo (22) ; give foo . i ; give foo ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                             the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_block { block: { let foo = new Foo (22) ; give foo . i ; give foo ; }, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass], existentials: [], assumptions: {} }, flow: Flow { moved_places: {} } }` failed at the following rule(s):
                                 the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `"flat_map"` failed at the following rule(s):
                                     failed at (src/file.rs:LL:CC) because
                                       judgment `"flat_map"` failed at the following rule(s):
                                         failed at (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: give foo ;, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo . i} } }` failed at the following rule(s):
                                             the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: give foo, env: Env { program: class Foo { i : Int ; } class TheClass { fn empty_method (Some(my self)) -> Int { let foo = new Foo (22) ; give foo . i ; give foo ; } }, universe: universe(0), in_scope_vars: [], local_variables: [self : my TheClass, foo : Foo], existentials: [], assumptions: {} }, flow: Flow { moved_places: {foo . i} } }` failed at the following rule(s):
                                                 the rule "give place" failed at step #0 (src/file.rs:LL:CC) because
                                                   condition evaluted to false: `!flow.is_moved(&place)`"#]],
    )
}
