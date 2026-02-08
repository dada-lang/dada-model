//! Tests for subpermissions.
//!
//! Perm P is a *subpermission* of perm Q when `P T` is a subtype of `Q T` for all types `T`.

use crate::{dada_lang::term, type_system::check_program};
use formality_core::{test, test_util::ResultTestExt};

#[test]
#[allow(non_snake_case)]
fn PermDataMy_is_subtype_of_PermDataMy() {
    check_program(&term(
        "
        class Data { }

        class PermData[perm P] {
            data: P Data;
        }

        class Main {
            fn test(my self, data: PermData[my]) {
                let m: PermData[my] = data.move;
            }
        }
        ",
    ))
    .assert_ok();
}

#[test]
#[allow(non_snake_case)]
fn PermDataMy_not_subtype_of_PermDataOur() {
    check_program(&term(
        "
        class Data { }

        class PermData[perm P] {
            data: P Data;
        }

        class Main {
            fn test(my self, data: PermData[my]) {
                let m: PermData[our] = data.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class PermData [perm] { data : ^perm0_0 Data ; } class Main { fn test (my self data : PermData[my]) -> () { let m : PermData[our] = data . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let m : PermData[our] = data . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" at (expressions.rs) failed because
                   judgment `type_expr_as { expr: { let m : PermData[our] = data . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" at (expressions.rs) failed because
                       judgment `type_expr { expr: { let m : PermData[our] = data . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" at (expressions.rs) failed because
                           judgment `type_block { block: { let m : PermData[our] = data . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" at (blocks.rs) failed because
                               judgment `type_statements_with_final_ty { statements: [let m : PermData[our] = data . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" at (statements.rs) failed because
                                   judgment `type_statement { statement: let m : PermData[our] = data . move ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "let" at (statements.rs) failed because
                                       judgment `type_expr_as { expr: data . move, as_ty: PermData[our], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "type_expr_as" at (expressions.rs) failed because
                                           judgment `sub { a: PermData[my], b: PermData[our], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "sub-classes" at (subtypes.rs) failed because
                                               judgment `sub_generic_parameter { perm_a: my, a: my, perm_b: my, b: our, variances: [], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "covariant-copy" at (subtypes.rs) failed because
                                                   judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "is" at (predicates.rs) failed because
                                                       judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "parameter" at (predicates.rs) failed because
                                                           pattern `true` did not match value `false`
                                                 the rule "covariant-owned" at (subtypes.rs) failed because
                                                   judgment `sub { a: my my, b: my our, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub-perms" at (subtypes.rs) failed because
                                                       judgment `sub_perms { perm_a: my my, perm_b: my our, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub_red_perms" at (redperms.rs) failed because
                                                           judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Our] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub_red_perms" at (redperms.rs) failed because
                                                               judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Our] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "(my) vs (my)" at (redperms.rs) failed because
                                                                   judgment `prove_is_my { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "prove" at (predicates.rs) failed because
                                                                       judgment `prove_is_unique { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is-moved" at (predicates.rs) failed because
                                                                           judgment `prove_predicate { predicate: unique(our), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "leased => unique" at (predicates.rs) failed because
                                                                               judgment `prove_is_leased { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "is-leased" at (predicates.rs) failed because
                                                                                   judgment `prove_predicate { predicate: leased(our), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "parameter" at (predicates.rs) failed because
                                                                                       pattern `true` did not match value `false`
                                                                             the rule "parameter" at (predicates.rs) failed because
                                                                               pattern `true` did not match value `false`
                                                 the rule "invariant" at (subtypes.rs) failed because
                                                   judgment `sub { a: my, b: our, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub-perms" at (subtypes.rs) failed because
                                                       judgment `sub_perms { perm_a: my, perm_b: our, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub_red_perms" at (redperms.rs) failed because
                                                           judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Our] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub_red_perms" at (redperms.rs) failed because
                                                               judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Our] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "(my) vs (my)" at (redperms.rs) failed because
                                                                   judgment `prove_is_my { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "prove" at (predicates.rs) failed because
                                                                       judgment `prove_is_unique { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "is-moved" at (predicates.rs) failed because
                                                                           judgment `prove_predicate { predicate: unique(our), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "leased => unique" at (predicates.rs) failed because
                                                                               judgment `prove_is_leased { a: our, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "is-leased" at (predicates.rs) failed because
                                                                                   judgment `prove_predicate { predicate: leased(our), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "parameter" at (predicates.rs) failed because
                                                                                       pattern `true` did not match value `false`
                                                                             the rule "parameter" at (predicates.rs) failed because
                                                                               pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn PermDataMy_is_not_subtype_of_PermDataLeased() {
    check_program(&term(
        "
        class Data { }

        class PermData[perm P] {
            data: P Data;
        }

        class Main {
            fn test(my self, data: PermData[my]) {
                let d = new Data();
                let m: PermData[mut[d]] = data.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class PermData [perm] { data : ^perm0_0 Data ; } class Main { fn test (my self data : PermData[my]) -> () { let d = new Data () ; let m : PermData[mut [d]] = data . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d = new Data () ; let m : PermData[mut [d]] = data . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" at (expressions.rs) failed because
                   judgment `type_expr_as { expr: { let d = new Data () ; let m : PermData[mut [d]] = data . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" at (expressions.rs) failed because
                       judgment `type_expr { expr: { let d = new Data () ; let m : PermData[mut [d]] = data . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" at (expressions.rs) failed because
                           judgment `type_block { block: { let d = new Data () ; let m : PermData[mut [d]] = data . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" at (blocks.rs) failed because
                               judgment `type_statements_with_final_ty { statements: [let d = new Data () ;, let m : PermData[mut [d]] = data . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" at (statements.rs) failed because
                                   judgment `type_statements_with_final_ty { statements: [let m : PermData[mut [d]] = data . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" at (statements.rs) failed because
                                       judgment `type_statement { statement: let m : PermData[mut [d]] = data . move ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" at (statements.rs) failed because
                                           judgment `type_expr_as { expr: data . move, as_ty: PermData[mut [d]], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "type_expr_as" at (expressions.rs) failed because
                                               judgment `sub { a: PermData[my], b: PermData[mut [d]], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub-classes" at (subtypes.rs) failed because
                                                   judgment `sub_generic_parameter { perm_a: my, a: my, perm_b: my, b: mut [d], variances: [], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "covariant-copy" at (subtypes.rs) failed because
                                                       judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "is" at (predicates.rs) failed because
                                                           judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "parameter" at (predicates.rs) failed because
                                                               pattern `true` did not match value `false`
                                                     the rule "covariant-owned" at (subtypes.rs) failed because
                                                       judgment `sub { a: my my, b: my mut [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-perms" at (subtypes.rs) failed because
                                                           judgment `sub_perms { perm_a: my my, perm_b: my mut [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub_red_perms" at (redperms.rs) failed because
                                                               judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Mtd(d)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "sub_red_perms" at (redperms.rs) failed because
                                                                   judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Mtd(d)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "(my) vs (my)" at (redperms.rs) failed because
                                                                       judgment `prove_is_my { a: mut [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "prove" at (predicates.rs) failed because
                                                                           judgment `prove_is_owned { a: mut [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "is-owned" at (predicates.rs) failed because
                                                                               judgment `prove_predicate { predicate: owned(mut [d]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "parameter" at (predicates.rs) failed because
                                                                                   pattern `true` did not match value `false`
                                                     the rule "invariant" at (subtypes.rs) failed because
                                                       judgment `sub { a: my, b: mut [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-perms" at (subtypes.rs) failed because
                                                           judgment `sub_perms { perm_a: my, perm_b: mut [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub_red_perms" at (redperms.rs) failed because
                                                               judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Mtd(d)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "sub_red_perms" at (redperms.rs) failed because
                                                                   judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Mtd(d)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "(my) vs (my)" at (redperms.rs) failed because
                                                                       judgment `prove_is_my { a: mut [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "prove" at (predicates.rs) failed because
                                                                           judgment `prove_is_owned { a: mut [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "is-owned" at (predicates.rs) failed because
                                                                               judgment `prove_predicate { predicate: owned(mut [d]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "parameter" at (predicates.rs) failed because
                                                                                   pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn PermDataMy_is_not_subtype_of_PermDataShared() {
    check_program(&term(
        "
        class Data { }

        class PermData[perm P] {
            data: P Data;
        }

        class Main {
            fn test(my self, data: PermData[my]) {
                let d = new Data();
                let m: PermData[ref[d]] = data.move;
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class PermData [perm] { data : ^perm0_0 Data ; } class Main { fn test (my self data : PermData[my]) -> () { let d = new Data () ; let m : PermData[ref [d]] = data . move ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let d = new Data () ; let m : PermData[ref [d]] = data . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" at (expressions.rs) failed because
                   judgment `type_expr_as { expr: { let d = new Data () ; let m : PermData[ref [d]] = data . move ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" at (expressions.rs) failed because
                       judgment `type_expr { expr: { let d = new Data () ; let m : PermData[ref [d]] = data . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" at (expressions.rs) failed because
                           judgment `type_block { block: { let d = new Data () ; let m : PermData[ref [d]] = data . move ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" at (blocks.rs) failed because
                               judgment `type_statements_with_final_ty { statements: [let d = new Data () ;, let m : PermData[ref [d]] = data . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" at (statements.rs) failed because
                                   judgment `type_statements_with_final_ty { statements: [let m : PermData[ref [d]] = data . move ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" at (statements.rs) failed because
                                       judgment `type_statement { statement: let m : PermData[ref [d]] = data . move ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" at (statements.rs) failed because
                                           judgment `type_expr_as { expr: data . move, as_ty: PermData[ref [d]], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "type_expr_as" at (expressions.rs) failed because
                                               judgment `sub { a: PermData[my], b: PermData[ref [d]], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub-classes" at (subtypes.rs) failed because
                                                   judgment `sub_generic_parameter { perm_a: my, a: my, perm_b: my, b: ref [d], variances: [], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "covariant-copy" at (subtypes.rs) failed because
                                                       judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "is" at (predicates.rs) failed because
                                                           judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "parameter" at (predicates.rs) failed because
                                                               pattern `true` did not match value `false`
                                                     the rule "covariant-owned" at (subtypes.rs) failed because
                                                       judgment `sub { a: my my, b: my ref [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-perms" at (subtypes.rs) failed because
                                                           judgment `sub_perms { perm_a: my my, perm_b: my ref [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub_red_perms" at (redperms.rs) failed because
                                                               judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Rfd(d)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "sub_red_perms" at (redperms.rs) failed because
                                                                   judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Rfd(d)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "(my) vs (my)" at (redperms.rs) failed because
                                                                       judgment `prove_is_my { a: ref [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "prove" at (predicates.rs) failed because
                                                                           judgment `prove_is_unique { a: ref [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "is-moved" at (predicates.rs) failed because
                                                                               judgment `prove_predicate { predicate: unique(ref [d]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "leased => unique" at (predicates.rs) failed because
                                                                                   judgment `prove_is_leased { a: ref [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "is-leased" at (predicates.rs) failed because
                                                                                       judgment `prove_predicate { predicate: leased(ref [d]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                         the rule "parameter" at (predicates.rs) failed because
                                                                                           pattern `true` did not match value `false`
                                                                                 the rule "parameter" at (predicates.rs) failed because
                                                                                   pattern `true` did not match value `false`
                                                     the rule "invariant" at (subtypes.rs) failed because
                                                       judgment `sub { a: my, b: ref [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub-perms" at (subtypes.rs) failed because
                                                           judgment `sub_perms { perm_a: my, perm_b: ref [d], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub_red_perms" at (redperms.rs) failed because
                                                               judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [] }, red_perm_b: RedPerm { chains: {RedChain { links: [Rfd(d)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "sub_red_perms" at (redperms.rs) failed because
                                                                   judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [] }, red_chain_b: RedChain { links: [Rfd(d)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "(my) vs (my)" at (redperms.rs) failed because
                                                                       judgment `prove_is_my { a: ref [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "prove" at (predicates.rs) failed because
                                                                           judgment `prove_is_unique { a: ref [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "is-moved" at (predicates.rs) failed because
                                                                               judgment `prove_predicate { predicate: unique(ref [d]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                 the rule "leased => unique" at (predicates.rs) failed because
                                                                                   judgment `prove_is_leased { a: ref [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "is-leased" at (predicates.rs) failed because
                                                                                       judgment `prove_predicate { predicate: leased(ref [d]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, d: Data, data: PermData[my]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                         the rule "parameter" at (predicates.rs) failed because
                                                                                           pattern `true` did not match value `false`
                                                                                 the rule "parameter" at (predicates.rs) failed because
                                                                                   pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn unsound_upgrade() {
    check_program(&term(
        "
        class Data {
            fn mutate[perm P](P self)
            where
                leased(P),
            { }
        }

        class Query {
            data: our Data;
        }

        class Main {
            fn test(my self, q1: Query, q2: Query) {
                let a: mut[q1.data] Data = q1.data.mut;
                let b: mut[q1] Data = a.move;
                b.mut.mutate[mut[q1]]();
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { fn mutate [perm] (^perm0_0 self) -> () where leased(^perm0_0) { } } class Query { data : our Data ; } class Main { fn test (my self q1 : Query, q2 : Query) -> () { let a : mut [q1 . data] Data = q1 . data . mut ; let b : mut [q1] Data = a . move ; b . mut . mutate [mut [q1]] () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let a : mut [q1 . data] Data = q1 . data . mut ; let b : mut [q1] Data = a . move ; b . mut . mutate [mut [q1]] () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, q1: Query, q2: Query}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" at (expressions.rs) failed because
                   judgment `type_expr_as { expr: { let a : mut [q1 . data] Data = q1 . data . mut ; let b : mut [q1] Data = a . move ; b . mut . mutate [mut [q1]] () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, q1: Query, q2: Query}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" at (expressions.rs) failed because
                       judgment `type_expr { expr: { let a : mut [q1 . data] Data = q1 . data . mut ; let b : mut [q1] Data = a . move ; b . mut . mutate [mut [q1]] () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, q1: Query, q2: Query}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" at (expressions.rs) failed because
                           judgment `type_block { block: { let a : mut [q1 . data] Data = q1 . data . mut ; let b : mut [q1] Data = a . move ; b . mut . mutate [mut [q1]] () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, q1: Query, q2: Query}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" at (blocks.rs) failed because
                               judgment `type_statements_with_final_ty { statements: [let a : mut [q1 . data] Data = q1 . data . mut ;, let b : mut [q1] Data = a . move ;, b . mut . mutate [mut [q1]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, q1: Query, q2: Query}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" at (statements.rs) failed because
                                   judgment `type_statements_with_final_ty { statements: [let b : mut [q1] Data = a . move ;, b . mut . mutate [mut [q1]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" at (statements.rs) failed because
                                       judgment `type_statement { statement: let b : mut [q1] Data = a . move ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {b}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" at (statements.rs) failed because
                                           judgment `type_expr_as { expr: a . move, as_ty: mut [q1] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "type_expr_as" at (expressions.rs) failed because
                                               judgment `sub { a: mut [q1 . data] Data, b: mut [q1] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "sub-classes" at (subtypes.rs) failed because
                                                   judgment `sub_perms { perm_a: mut [q1 . data], perm_b: mut [q1], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "sub_red_perms" at (redperms.rs) failed because
                                                       judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Our] }, red_perm_b: RedPerm { chains: {RedChain { links: [Mtd(q1)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub_red_perms" at (redperms.rs) failed because
                                                           judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Our] }, red_chain_b: RedChain { links: [Mtd(q1)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "(our) vs (shared)" at (redperms.rs) failed because
                                                               judgment `prove_is_shared { a: mut [q1], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is" at (predicates.rs) failed because
                                                                   judgment `prove_predicate { predicate: shared(mut [q1]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" at (predicates.rs) failed because
                                                                       pattern `true` did not match value `false`
                                                             the rule "(our::P) vs (shared::P)" at (redperms.rs) failed because
                                                               judgment `prove_is_shared { a: mut [q1], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "is" at (predicates.rs) failed because
                                                                   judgment `prove_predicate { predicate: shared(mut [q1]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, a: mut [q1 . data] Data, q1: Query, q2: Query}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" at (predicates.rs) failed because
                                                                       pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_exists() {
    check_program(&term(
        "
        class Query {
        }

        class Main {
            fn test(my self, q1: Query, q2: Query) {
                let a: ref[q1] Query = q1.ref;
                let b: ref[q2] Query = q2.ref;
                let c: ref[a] ref[q1] Query = a.ref;
                let d: ref[b] ref[q2] Query = b.ref;
                let x: ref[a, b] Query = c.move;
                let y: ref[a, b] Query = d.move;
            }
        }
        ",
    ))
    .assert_ok();
}
