use formality_core::test;

#[test]
fn choice_with_self_ref_a() {
    crate::assert_ok!({
        class Data {
        }

        class Pair {
            a: Data;
            b: Data;
        }

        class Choice {
            pair: Pair;
            data: ref[self.pair] Data;
        }

        class TheClass {
            fn empty_method(given self) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1.give, d2.give);
                let r = pair.a.ref;
                let choice = new Choice(pair.give, r.give);
                ();
            }
        }
    })
}

#[test]
fn choice_with_self_ref_b() {
    crate::assert_ok!({
        class Data {
        }

        class Pair {
            a: Data;
            b: Data;
        }

        class Choice {
            pair: Pair;
            data: ref[self.pair] Data;
        }

        class TheClass {
            fn empty_method(given self) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1.give, d2.give);
                let r = pair.b.ref;
                let choice = new Choice(pair.give, r.give);
                ();
            }
        }
    })
}

#[test]
fn choice_with_non_self_ref() {
    crate::assert_err!({
        class Data {
        }

        class Pair {
            a: Data;
            b: Data;
        }

        class Choice {
            pair: Pair;
            data: ref[self.pair] Data;
        }

        class TheClass {
            fn empty_method(given self) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let d3 = new Data();
                let pair = new Pair(d1.give, d2.give);
                let r = d3.ref;
                let choice = new Choice(pair.give, r.give);
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "check_class" at (classes.rs) failed because
          judgment `check_method { decl: fn empty_method (given self) -> () { let d1 = new Data () ; let d2 = new Data () ; let d3 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = d3 . ref ; let choice = new Choice (pair . give, r . give) ; () ; }, class_ty: TheClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
            the rule "check_method" at (methods.rs) failed because
              judgment `check_body { body: { let d1 = new Data () ; let d2 = new Data () ; let d3 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = d3 . ref ; let choice = new Choice (pair . give, r . give) ; () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "block" at (methods.rs) failed because
                  judgment `can_type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let d3 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = d3 . ref ; let choice = new Choice (pair . give, r . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                    the rule "can_type_expr_as" at (expressions.rs) failed because
                      judgment `type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let d3 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = d3 . ref ; let choice = new Choice (pair . give, r . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr { expr: { let d1 = new Data () ; let d2 = new Data () ; let d3 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = d3 . ref ; let choice = new Choice (pair . give, r . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "block" at (expressions.rs) failed because
                              judgment `type_block { block: { let d1 = new Data () ; let d2 = new Data () ; let d3 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = d3 . ref ; let choice = new Choice (pair . give, r . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "place" at (blocks.rs) failed because
                                  judgment `type_statements_with_final_ty { statements: [let d1 = new Data () ;, let d2 = new Data () ;, let d3 = new Data () ;, let pair = new Pair (d1 . give, d2 . give) ;, let r = d3 . ref ;, let choice = new Choice (pair . give, r . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "cons" at (statements.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let d2 = new Data () ;, let d3 = new Data () ;, let pair = new Pair (d1 . give, d2 . give) ;, let r = d3 . ref ;, let choice = new Choice (pair . give, r . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, d1: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let d3 = new Data () ;, let pair = new Pair (d1 . give, d2 . give) ;, let r = d3 . ref ;, let choice = new Choice (pair . give, r . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [let pair = new Pair (d1 . give, d2 . give) ;, let r = d3 . ref ;, let choice = new Choice (pair . give, r . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, d1: Data, d2: Data, d3: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statements_with_final_ty { statements: [let r = d3 . ref ;, let choice = new Choice (pair . give, r . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, d1: Data, d2: Data, d3: Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "cons" at (statements.rs) failed because
                                                      judgment `type_statements_with_final_ty { statements: [let choice = new Choice (pair . give, r . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "cons" at (statements.rs) failed because
                                                          judgment `type_statement { statement: let choice = new Choice (pair . give, r . give) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                            the rule "let" at (statements.rs) failed because
                                                              judgment `type_expr { expr: new Choice (pair . give, r . give), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                the rule "new" at (expressions.rs) failed because
                                                                  judgment `type_field_exprs_as { temp_var: @ fresh(0), exprs: [pair . give, r . give], fields: [pair : Pair ;, data : ref [self . pair] Data ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                    the rule "cons" at (expressions.rs) failed because
                                                                      judgment `type_field_exprs_as { temp_var: @ fresh(0), exprs: [r . give], fields: [data : ref [self . pair] Data ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                                        the rule "cons" at (expressions.rs) failed because
                                                                          judgment `sub { a: ref [d3] Data, b: ref [@ fresh(0) . pair] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                            the rule "sub-classes" at (subtypes.rs) failed because
                                                                              judgment `sub_perms { perm_a: ref [d3], perm_b: ref [@ fresh(0) . pair], live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                the rule "sub_red_perms" at (redperms.rs) failed because
                                                                                  judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Rfd(d3)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Rfd(@ fresh(0) . pair)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                                                                      judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Rfd(d3)] }, red_chain_b: RedChain { links: [Rfd(@ fresh(0) . pair)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                        the rule "(ref-dead::P) vs Q ~~> (shared::P) vs Q" at (redperms.rs) failed because
                                                                                          judgment `prove_is_mut { a: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                            the rule "is-mut" at (predicates.rs) failed because
                                                                                              judgment `prove_predicate { predicate: mut(given), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                                the rule "parameter" at (predicates.rs) failed because
                                                                                                  pattern `true` did not match value `false`
                                                                                        the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
                                                                                          condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                                                                            place_b = @ fresh(0) . pair
                                                                                            &place_a = d3
                                                                                        the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                                                                          judgment `prove_is_copy_owned { a: ref [d3], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                            the rule "prove" at (predicates.rs) failed because
                                                                                              judgment `prove_is_owned { a: ref [d3], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                                the rule "is-owned" at (predicates.rs) failed because
                                                                                                  judgment `prove_predicate { predicate: owned(ref [d3]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): Choice, d1: Data, d2: Data, d3: Data, pair: Pair, r: ref [d3] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                                                    the rule "parameter" at (predicates.rs) failed because
                                                                                                      pattern `true` did not match value `false`"#]])
}

/// Test that we can create a `Choice`,
/// pull out its individual fields (in the correct order, mind)
/// and then reconstruct it.
///
/// In other words, when we move from `choice1.data.give`
/// to `choice1_data`, we correctly track that it has type
/// `copy(choice1.pair) Data`, and then when we
/// move from `choice1.pair` to `choice1_pair`, we can adjust
/// type of `choice1_data` to be `copy(choice1_pair) Data`.
#[test]
fn unpack_and_reconstruct_correct_order() {
    crate::assert_ok!({
        class Data {
        }

        class Pair {
            a: Data;
            b: Data;
        }

        class Choice {
            pair: Pair;
            data: ref[self.pair] Data;
        }

        class TheClass {
            fn empty_method(given self) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1.give, d2.give);
                let r = pair.a.ref;
                let choice1 = new Choice(pair.give, r.give);
                let choice1_data = choice1.data.give;
                let choice1_pair = choice1.pair.give;
                let choice2 = new Choice(choice1_pair.give, choice1_data.give);
                ();
            }
        }
    })
}

/// Version of `unpack_and_reconstruct_correct_order` where we pull out the
/// fields in the other order. While in principle this should work,
/// we can't handle it in our type system and we should error. Why?
/// When we move `choice1.pair` first, the type declared for `Choice::data`
/// would have to be adjusteed to reference a local variable, and that
/// doesn't work.
///
/// FIXME: We do currently get an error, but not the one I really expect us to get.
/// I think the ideal is that moving `choice1.pair` should making all of `choice1`
/// be considered moved.
#[test]
fn unpack_and_reconstruct_wrong_order() {
    crate::assert_err!({
        class Data {
        }

        class Pair {
            a: Data;
            b: Data;
        }

        class Choice {
            pair: Pair;
            data: ref[self.pair] Data;
        }

        class TheClass {
            fn empty_method(given self) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1.give, d2.give);
                let r = pair.a.ref;
                let choice1 = new Choice(pair.give, r.give);
                let choice1_pair = choice1.pair.give; 
                let choice1_data = choice1.data.give;
                let choice2 = new Choice(choice1_pair.give, choice1_data.give);
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "check_class" at (classes.rs) failed because
          judgment `check_method { decl: fn empty_method (given self) -> () { let d1 = new Data () ; let d2 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = pair . a . ref ; let choice1 = new Choice (pair . give, r . give) ; let choice1_pair = choice1 . pair . give ; let choice1_data = choice1 . data . give ; let choice2 = new Choice (choice1_pair . give, choice1_data . give) ; () ; }, class_ty: TheClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
            the rule "check_method" at (methods.rs) failed because
              judgment `check_body { body: { let d1 = new Data () ; let d2 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = pair . a . ref ; let choice1 = new Choice (pair . give, r . give) ; let choice1_pair = choice1 . pair . give ; let choice1_data = choice1 . data . give ; let choice2 = new Choice (choice1_pair . give, choice1_data . give) ; () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "block" at (methods.rs) failed because
                  judgment `can_type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = pair . a . ref ; let choice1 = new Choice (pair . give, r . give) ; let choice1_pair = choice1 . pair . give ; let choice1_data = choice1 . data . give ; let choice2 = new Choice (choice1_pair . give, choice1_data . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                    the rule "can_type_expr_as" at (expressions.rs) failed because
                      judgment `type_expr_as { expr: { let d1 = new Data () ; let d2 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = pair . a . ref ; let choice1 = new Choice (pair . give, r . give) ; let choice1_pair = choice1 . pair . give ; let choice1_data = choice1 . data . give ; let choice2 = new Choice (choice1_pair . give, choice1_data . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr { expr: { let d1 = new Data () ; let d2 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = pair . a . ref ; let choice1 = new Choice (pair . give, r . give) ; let choice1_pair = choice1 . pair . give ; let choice1_data = choice1 . data . give ; let choice2 = new Choice (choice1_pair . give, choice1_data . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "block" at (expressions.rs) failed because
                              judgment `type_block { block: { let d1 = new Data () ; let d2 = new Data () ; let pair = new Pair (d1 . give, d2 . give) ; let r = pair . a . ref ; let choice1 = new Choice (pair . give, r . give) ; let choice1_pair = choice1 . pair . give ; let choice1_data = choice1 . data . give ; let choice2 = new Choice (choice1_pair . give, choice1_data . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "place" at (blocks.rs) failed because
                                  judgment `type_statements_with_final_ty { statements: [let d1 = new Data () ;, let d2 = new Data () ;, let pair = new Pair (d1 . give, d2 . give) ;, let r = pair . a . ref ;, let choice1 = new Choice (pair . give, r . give) ;, let choice1_pair = choice1 . pair . give ;, let choice1_data = choice1 . data . give ;, let choice2 = new Choice (choice1_pair . give, choice1_data . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "cons" at (statements.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let d2 = new Data () ;, let pair = new Pair (d1 . give, d2 . give) ;, let r = pair . a . ref ;, let choice1 = new Choice (pair . give, r . give) ;, let choice1_pair = choice1 . pair . give ;, let choice1_data = choice1 . data . give ;, let choice2 = new Choice (choice1_pair . give, choice1_data . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, d1: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let pair = new Pair (d1 . give, d2 . give) ;, let r = pair . a . ref ;, let choice1 = new Choice (pair . give, r . give) ;, let choice1_pair = choice1 . pair . give ;, let choice1_data = choice1 . data . give ;, let choice2 = new Choice (choice1_pair . give, choice1_data . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, d1: Data, d2: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [let r = pair . a . ref ;, let choice1 = new Choice (pair . give, r . give) ;, let choice1_pair = choice1 . pair . give ;, let choice1_data = choice1 . data . give ;, let choice2 = new Choice (choice1_pair . give, choice1_data . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, d1: Data, d2: Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statements_with_final_ty { statements: [let choice1 = new Choice (pair . give, r . give) ;, let choice1_pair = choice1 . pair . give ;, let choice1_data = choice1 . data . give ;, let choice2 = new Choice (choice1_pair . give, choice1_data . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, d1: Data, d2: Data, pair: Pair, r: ref [pair . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "cons" at (statements.rs) failed because
                                                      judgment `type_statements_with_final_ty { statements: [let choice1_pair = choice1 . pair . give ;, let choice1_data = choice1 . data . give ;, let choice2 = new Choice (choice1_pair . give, choice1_data . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice1: Choice, d1: Data, d2: Data, pair: Pair, r: ref [choice1 . pair . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "cons" at (statements.rs) failed because
                                                          judgment `type_statement { statement: let choice1_pair = choice1 . pair . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice1: Choice, d1: Data, d2: Data, pair: Pair, r: ref [choice1 . pair . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice1 . data, choice1_pair}, traversed: {} } }` failed at the following rule(s):
                                                            the rule "let" at (statements.rs) failed because
                                                              judgment `type_expr { expr: choice1 . pair . give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice1: Choice, d1: Data, d2: Data, pair: Pair, r: ref [choice1 . pair . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice1 . data}, traversed: {} } }` failed at the following rule(s):
                                                                the rule "give place" at (expressions.rs) failed because
                                                                  judgment `access_permitted { access: give, place: choice1 . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice1: Choice, d1: Data, d2: Data, pair: Pair, r: ref [choice1 . pair . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice1 . data}, traversed: {} } }` failed at the following rule(s):
                                                                    the rule "access_permitted" at (accesses.rs) failed because
                                                                      judgment `env_permits_access { access: give, place: choice1 . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice1: Choice, d1: Data, d2: Data, pair: Pair, r: ref [choice1 . pair . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice1 . data}, traversed: {} } }` failed at the following rule(s):
                                                                        the rule "env_permits_access" at (accesses.rs) failed because
                                                                          judgment `accessed_place_permits_access { place: choice1 . pair, access: give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice1: Choice, d1: Data, d2: Data, pair: Pair, r: ref [choice1 . pair . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice1 . data}, traversed: {} } }` failed at the following rule(s):
                                                                            the rule "live" at (accesses.rs) failed because
                                                                              judgment `accessed_place_prefix_permits_access { place_prefix: choice1, place: choice1 . pair, access: give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice1: Choice, d1: Data, d2: Data, pair: Pair, r: ref [choice1 . pair . a] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "live" at (accesses.rs) failed because
                                                                                  judgment `"flat_map"` failed at the following rule(s):
                                                                                    failed at (quantifiers.rs) because
                                                                                      judgment `field_of_accessed_place_prefix_permits_access { place_prefix: choice1, field: data : ref [self . pair] Data ;, place: choice1 . pair, access: give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice1: Choice, d1: Data, d2: Data, pair: Pair, r: ref [choice1 . pair . a] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "not accessed place" at (accesses.rs) failed because
                                                                                          judgment `parameter_permits_access { parameter: ref [choice1 . pair] Data, access: drop, place: choice1 . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice1: Choice, d1: Data, d2: Data, pair: Pair, r: ref [choice1 . pair . a] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "parameter" at (accesses.rs) failed because
                                                                                              judgment `lien_permit_access { lien: rf(choice1 . pair), access: drop, accessed_place: choice1 . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice1: Choice, d1: Data, d2: Data, pair: Pair, r: ref [choice1 . pair . a] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                                the rule "ref'd" at (accesses.rs) failed because
                                                                                                  judgment `ref_place_permits_access { shared_place: choice1 . pair, access: drop, accessed_place: choice1 . pair }` failed at the following rule(s):
                                                                                                    the rule "share-mutation" at (accesses.rs) failed because
                                                                                                      condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
                                                                                                        &accessed_place = choice1 . pair
                                                                                                        &shared_place = choice1 . pair"#]])
}

/// Access to the field `choice.pair` but the other field
/// `choice.data` has a lease on `choice.pair`.
#[test]
fn lease_when_internally_leased() {
    crate::assert_err!({
        class Data {
        }

        class Pair {
            a: Data;
            b: Data;
        }

        class Choice {
            pair: Pair;
            data: mut[self.pair] Data;
        }

        class TheClass {
            fn empty_method(given self, choice: Choice) -> () {
                let pair = choice.pair.mut;
                let data = choice.data.mut;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "check_class" at (classes.rs) failed because
          judgment `check_method { decl: fn empty_method (given self choice : Choice) -> () { let pair = choice . pair . mut ; let data = choice . data . mut ; () ; }, class_ty: TheClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
            the rule "check_method" at (methods.rs) failed because
              judgment `check_body { body: { let pair = choice . pair . mut ; let data = choice . data . mut ; () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "block" at (methods.rs) failed because
                  judgment `can_type_expr_as { expr: { let pair = choice . pair . mut ; let data = choice . data . mut ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                    the rule "can_type_expr_as" at (expressions.rs) failed because
                      judgment `type_expr_as { expr: { let pair = choice . pair . mut ; let data = choice . data . mut ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr { expr: { let pair = choice . pair . mut ; let data = choice . data . mut ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "block" at (expressions.rs) failed because
                              judgment `type_block { block: { let pair = choice . pair . mut ; let data = choice . data . mut ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "place" at (blocks.rs) failed because
                                  judgment `type_statements_with_final_ty { statements: [let pair = choice . pair . mut ;, let data = choice . data . mut ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "cons" at (statements.rs) failed because
                                      judgment `type_statement { statement: let pair = choice . pair . mut ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                        the rule "let" at (statements.rs) failed because
                                          judgment `type_expr { expr: choice . pair . mut, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                            the rule "ref|mut place" at (expressions.rs) failed because
                                              judgment `access_permitted { access: mut, place: choice . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                                the rule "access_permitted" at (accesses.rs) failed because
                                                  judgment `env_permits_access { access: mut, place: choice . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "env_permits_access" at (accesses.rs) failed because
                                                      judgment `accessed_place_permits_access { place: choice . pair, access: mut, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "live" at (accesses.rs) failed because
                                                          judgment `accessed_place_prefix_permits_access { place_prefix: choice, place: choice . pair, access: mut, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "live" at (accesses.rs) failed because
                                                              judgment `"flat_map"` failed at the following rule(s):
                                                                failed at (quantifiers.rs) because
                                                                  judgment `field_of_accessed_place_prefix_permits_access { place_prefix: choice, field: data : mut [self . pair] Data ;, place: choice . pair, access: mut, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "not accessed place" at (accesses.rs) failed because
                                                                      judgment `parameter_permits_access { parameter: mut [choice . pair] Data, access: mut, place: choice . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "parameter" at (accesses.rs) failed because
                                                                          judgment `lien_permit_access { lien: mt(choice . pair), access: mut, accessed_place: choice . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "mut'd" at (accesses.rs) failed because
                                                                              judgment `mut_place_permits_access { leased_place: choice . pair, access: mut, accessed_place: choice . pair }` failed at the following rule(s):
                                                                                the rule "lease-mutation" at (accesses.rs) failed because
                                                                                  condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
                                                                                    &accessed_place = choice . pair
                                                                                    &leased_place = choice . pair"#]])
}

/// Extract the `pair` from choice and then drop it.
/// Then access data supposedly leased from that pair.
/// This should fail.
#[test]
fn unpack_and_reconstruct_drop_then_access() {
    crate::assert_err!({
        class Data {
        }

        class Pair {
            a: Data;
            b: Data;
        }

        class Choice {
            pair: Pair;
            data: ref[self.pair] Data;
        }

        class TheClass {
            fn empty_method(given self, choice: Choice) -> () {
                let choice_pair = choice.pair.give; 
                choice_pair.give;
                let choice_data = choice.data.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "check_class" at (classes.rs) failed because
          judgment `check_method { decl: fn empty_method (given self choice : Choice) -> () { let choice_pair = choice . pair . give ; choice_pair . give ; let choice_data = choice . data . give ; () ; }, class_ty: TheClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
            the rule "check_method" at (methods.rs) failed because
              judgment `check_body { body: { let choice_pair = choice . pair . give ; choice_pair . give ; let choice_data = choice . data . give ; () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "block" at (methods.rs) failed because
                  judgment `can_type_expr_as { expr: { let choice_pair = choice . pair . give ; choice_pair . give ; let choice_data = choice . data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                    the rule "can_type_expr_as" at (expressions.rs) failed because
                      judgment `type_expr_as { expr: { let choice_pair = choice . pair . give ; choice_pair . give ; let choice_data = choice . data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr { expr: { let choice_pair = choice . pair . give ; choice_pair . give ; let choice_data = choice . data . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "block" at (expressions.rs) failed because
                              judgment `type_block { block: { let choice_pair = choice . pair . give ; choice_pair . give ; let choice_data = choice . data . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "place" at (blocks.rs) failed because
                                  judgment `type_statements_with_final_ty { statements: [let choice_pair = choice . pair . give ;, choice_pair . give ;, let choice_data = choice . data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "cons" at (statements.rs) failed because
                                      judgment `type_statement { statement: let choice_pair = choice . pair . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data, choice_pair}, traversed: {} } }` failed at the following rule(s):
                                        the rule "let" at (statements.rs) failed because
                                          judgment `type_expr { expr: choice . pair . give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                            the rule "give place" at (expressions.rs) failed because
                                              judgment `access_permitted { access: give, place: choice . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                                the rule "access_permitted" at (accesses.rs) failed because
                                                  judgment `env_permits_access { access: give, place: choice . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "env_permits_access" at (accesses.rs) failed because
                                                      judgment `accessed_place_permits_access { place: choice . pair, access: give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {choice . data}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "live" at (accesses.rs) failed because
                                                          judgment `accessed_place_prefix_permits_access { place_prefix: choice, place: choice . pair, access: give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "live" at (accesses.rs) failed because
                                                              judgment `"flat_map"` failed at the following rule(s):
                                                                failed at (quantifiers.rs) because
                                                                  judgment `field_of_accessed_place_prefix_permits_access { place_prefix: choice, field: data : ref [self . pair] Data ;, place: choice . pair, access: give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "not accessed place" at (accesses.rs) failed because
                                                                      judgment `parameter_permits_access { parameter: ref [choice . pair] Data, access: drop, place: choice . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "parameter" at (accesses.rs) failed because
                                                                          judgment `lien_permit_access { lien: rf(choice . pair), access: drop, accessed_place: choice . pair, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, choice: Choice}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "ref'd" at (accesses.rs) failed because
                                                                              judgment `ref_place_permits_access { shared_place: choice . pair, access: drop, accessed_place: choice . pair }` failed at the following rule(s):
                                                                                the rule "share-mutation" at (accesses.rs) failed because
                                                                                  condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
                                                                                    &accessed_place = choice . pair
                                                                                    &shared_place = choice . pair"#]])
}

/// This should fail because `r` is actually a pointer to `pair`
/// so when `pair` is moved it should be invalidated. Currently it passes (FIXME#12).
#[test]
fn choice_with_leased_self_ref_a() {
    crate::assert_ok!({
        class Data {
        }

        class Pair {
            a: Data;
            b: Data;
        }

        class Choice {
            pair: Pair;
            data: mut[self.pair] Data;
        }

        class TheClass {
            fn empty_method(given self) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1.give, d2.give);
                let r = pair.a.mut;
                let choice = new Choice(pair.give, r.give);
                ();
            }
        }
    })
}
