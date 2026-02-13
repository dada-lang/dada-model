use formality_core::test;

#[test]
#[allow(non_snake_case)]
fn shared_dead_leased_to_our_leased() {
    crate::assert_ok!({
        class Data {
            fn read[perm P](P self) where copy(P) {
                ();
            }
        }
        class Main {
            fn test(given self) {
                let d = new Data();
                let p: mut[d] Data = d.mut;
                let q: ref[p] Data = p.ref;
                let r: shared mut[d] Data = q.give;
                r.give.read[shared mut[d]]();
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn shared_live_leased_to_our_leased() {
    // Cannot coerce from `ref[p] mut[d]` to `shared mut[d]`
    // because `p` is not dead.
    crate::assert_err!({
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test(given self) {
                let d = new Data();
                let p: mut[d] Data = d.mut;
                let q: ref[p] Data = p.ref;
                let r: shared mut[d] Data = q.give;
                p.give.read[mut[d]]();
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self) -> () { let d = new Data () ; let p : mut [d] Data = d . mut ; let q : ref [p] Data = p . ref ; let r : shared mut [d] Data = q . give ; p . give . read [mut [d]] () ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let d = new Data () ; let p : mut [d] Data = d . mut ; let q : ref [p] Data = p . ref ; let r : shared mut [d] Data = q . give ; p . give . read [mut [d]] () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let d = new Data () ; let p : mut [d] Data = d . mut ; let q : ref [p] Data = p . ref ; let r : shared mut [d] Data = q . give ; p . give . read [mut [d]] () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let d = new Data () ; let p : mut [d] Data = d . mut ; let q : ref [p] Data = p . ref ; let r : shared mut [d] Data = q . give ; p . give . read [mut [d]] () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let d = new Data () ; let p : mut [d] Data = d . mut ; let q : ref [p] Data = p . ref ; let r : shared mut [d] Data = q . give ; p . give . read [mut [d]] () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let d = new Data () ; let p : mut [d] Data = d . mut ; let q : ref [p] Data = p . ref ; let r : shared mut [d] Data = q . give ; p . give . read [mut [d]] () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements { statements: [let d = new Data () ;, let p : mut [d] Data = d . mut ;, let q : ref [p] Data = p . ref ;, let r : shared mut [d] Data = q . give ;, p . give . read [mut [d]] () ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "type_statements" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let d = new Data () ;, let p : mut [d] Data = d . mut ;, let q : ref [p] Data = p . ref ;, let r : shared mut [d] Data = q . give ;, p . give . read [mut [d]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [let p : mut [d] Data = d . mut ;, let q : ref [p] Data = p . ref ;, let r : shared mut [d] Data = q . give ;, p . give . read [mut [d]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statements_with_final_ty { statements: [let q : ref [p] Data = p . ref ;, let r : shared mut [d] Data = q . give ;, p . give . read [mut [d]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "cons" at (statements.rs) failed because
                                                      judgment `type_statements_with_final_ty { statements: [let r : shared mut [d] Data = q . give ;, p . give . read [mut [d]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "cons" at (statements.rs) failed because
                                                          judgment `type_statement { statement: let r : shared mut [d] Data = q . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                            the rule "let" at (statements.rs) failed because
                                                              judgment `type_expr_as { expr: q . give, as_ty: shared mut [d] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                                the rule "type_expr_as" at (expressions.rs) failed because
                                                                  judgment `sub { a: ref [p] Data, b: shared mut [d] Data, live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "sub-classes" at (subtypes.rs) failed because
                                                                      judgment `sub_perms { perm_a: ref [p], perm_b: shared mut [d], live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                                                          judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Rfl(p), Mtd(d)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Shared, Mtd(d)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                                                              judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Rfl(p), Mtd(d)] }, red_chain_b: RedChain { links: [Shared, Mtd(d)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "(ref::P) vs (shared::mut::P)" at (redperms.rs) failed because
                                                                                  condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                                                                    place_b = d
                                                                                    &place_a = p
                                                                                the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                                                                  judgment `prove_is_copy_owned { a: ref [p], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "prove" at (predicates.rs) failed because
                                                                                      judgment `prove_is_owned { a: ref [p], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "is-owned" at (predicates.rs) failed because
                                                                                          judgment `prove_predicate { predicate: owned(ref [p]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                                              pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn leased_dead_leased_to_leased() {
    // Can coerce from `mut[p] mut[d]` to `mut[d]`
    // because `p` is dead.
    crate::assert_ok!({
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test(given self) {
                let d = new Data();
                let p: mut[d] Data = d.mut;
                let q: mut[p] Data = p.mut;
                let r: mut[d] Data = q.give;
                r.give.read[mut[d]]();
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn leased_live_leased_to_leased() {
    // Cannot coerce from `mut[p] mut[d]` to `mut[d]`
    // because `p` is not dead.
    crate::assert_err!({
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test(given self) {
                let d = new Data();
                let p: mut[d] Data = d.mut;
                let q: mut[p] Data = p.mut;
                let r: mut[d] Data = q.give;
                p.give.read[mut[d]]();
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self) -> () { let d = new Data () ; let p : mut [d] Data = d . mut ; let q : mut [p] Data = p . mut ; let r : mut [d] Data = q . give ; p . give . read [mut [d]] () ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let d = new Data () ; let p : mut [d] Data = d . mut ; let q : mut [p] Data = p . mut ; let r : mut [d] Data = q . give ; p . give . read [mut [d]] () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let d = new Data () ; let p : mut [d] Data = d . mut ; let q : mut [p] Data = p . mut ; let r : mut [d] Data = q . give ; p . give . read [mut [d]] () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let d = new Data () ; let p : mut [d] Data = d . mut ; let q : mut [p] Data = p . mut ; let r : mut [d] Data = q . give ; p . give . read [mut [d]] () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let d = new Data () ; let p : mut [d] Data = d . mut ; let q : mut [p] Data = p . mut ; let r : mut [d] Data = q . give ; p . give . read [mut [d]] () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let d = new Data () ; let p : mut [d] Data = d . mut ; let q : mut [p] Data = p . mut ; let r : mut [d] Data = q . give ; p . give . read [mut [d]] () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements { statements: [let d = new Data () ;, let p : mut [d] Data = d . mut ;, let q : mut [p] Data = p . mut ;, let r : mut [d] Data = q . give ;, p . give . read [mut [d]] () ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "type_statements" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let d = new Data () ;, let p : mut [d] Data = d . mut ;, let q : mut [p] Data = p . mut ;, let r : mut [d] Data = q . give ;, p . give . read [mut [d]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [let p : mut [d] Data = d . mut ;, let q : mut [p] Data = p . mut ;, let r : mut [d] Data = q . give ;, p . give . read [mut [d]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statements_with_final_ty { statements: [let q : mut [p] Data = p . mut ;, let r : mut [d] Data = q . give ;, p . give . read [mut [d]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "cons" at (statements.rs) failed because
                                                      judgment `type_statements_with_final_ty { statements: [let r : mut [d] Data = q . give ;, p . give . read [mut [d]] () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "cons" at (statements.rs) failed because
                                                          judgment `type_statement { statement: let r : mut [d] Data = q . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                            the rule "let" at (statements.rs) failed because
                                                              judgment `type_expr_as { expr: q . give, as_ty: mut [d] Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {p}, traversed: {} } }` failed at the following rule(s):
                                                                the rule "type_expr_as" at (expressions.rs) failed because
                                                                  judgment `sub { a: mut [p] Data, b: mut [d] Data, live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                    the rule "sub-classes" at (subtypes.rs) failed because
                                                                      judgment `sub_perms { perm_a: mut [p], perm_b: mut [d], live_after: LivePlaces { accessed: {p}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                                                          judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Mtl(p), Mtd(d)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Mtd(d)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "sub_red_perms" at (redperms.rs) failed because
                                                                              judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Mtl(p), Mtd(d)] }, red_chain_b: RedChain { links: [Mtd(d)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "(mut::P) vs (mut::P)" at (redperms.rs) failed because
                                                                                  condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                                                                    place_b = d
                                                                                    &place_a = p
                                                                                the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                                                                  judgment `prove_is_copy_owned { a: mut [p], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                    the rule "prove" at (predicates.rs) failed because
                                                                                      judgment `prove_is_copy { a: mut [p], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "is" at (predicates.rs) failed because
                                                                                          judgment `prove_predicate { predicate: copy(mut [p]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                                              pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn return_leased_dead_leased_to_leased() {
    // Equivalent of `fn test(given self, d: leased Data) -> mut[d] Data
    crate::assert_ok!({
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test[perm P](given self, d: P Data) -> mut[d] Data
            where
                mut(P),
            {
                let p: mut[d] Data = d.mut;
                let q: mut[p] Data = p.mut;
                q.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn return_leased_dead_leased_to_leased_and_use_while_leased() {
    // Equivalent of `fn test(given self, d: leased Data) -> mut[d] Data
    crate::assert_err!({
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test[perm P](given self, d: P Data) -> mut[d] Data
            where
                mut(P),
            {
                let p: mut[d] Data = d.mut;
                let q: mut[p] Data = p.mut;
                p.ref.read[ref[p] Data]();
                q.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test [perm] (given self d : ^perm0_0 Data) -> mut [d] Data where mut(^perm0_0) { let p : mut [d] Data = d . mut ; let q : mut [p] Data = p . mut ; p . ref . read [ref [p] Data] () ; q . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let p : mut [d] Data = d . mut ; let q : mut [p] Data = p . mut ; p . ref . read [ref [p] Data] () ; q . give ; }, output: mut [d] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d: !perm_0 Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let p : mut [d] Data = d . mut ; let q : mut [p] Data = p . mut ; p . ref . read [ref [p] Data] () ; q . give ; }, as_ty: mut [d] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d: !perm_0 Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let p : mut [d] Data = d . mut ; let q : mut [p] Data = p . mut ; p . ref . read [ref [p] Data] () ; q . give ; }, as_ty: mut [d] Data, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d: !perm_0 Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let p : mut [d] Data = d . mut ; let q : mut [p] Data = p . mut ; p . ref . read [ref [p] Data] () ; q . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d: !perm_0 Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let p : mut [d] Data = d . mut ; let q : mut [p] Data = p . mut ; p . ref . read [ref [p] Data] () ; q . give ; }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d: !perm_0 Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements { statements: [let p : mut [d] Data = d . mut ;, let q : mut [p] Data = p . mut ;, p . ref . read [ref [p] Data] () ;, q . give ;], env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d: !perm_0 Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "type_statements" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let p : mut [d] Data = d . mut ;, let q : mut [p] Data = p . mut ;, p . ref . read [ref [p] Data] () ;, q . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d: !perm_0 Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [let q : mut [p] Data = p . mut ;, p . ref . read [ref [p] Data] () ;, q . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d: !perm_0 Data, p: mut [d] Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statements_with_final_ty { statements: [p . ref . read [ref [p] Data] () ;, q . give ;], ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d: !perm_0 Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "cons" at (statements.rs) failed because
                                                      judgment `type_statement { statement: p . ref . read [ref [p] Data] () ;, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d: !perm_0 Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {q}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "expr" at (statements.rs) failed because
                                                          judgment `type_expr { expr: p . ref . read [ref [p] Data] (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d: !perm_0 Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {q}, traversed: {} } }` failed at the following rule(s):
                                                            the rule "call" at (expressions.rs) failed because
                                                              judgment `type_expr { expr: p . ref, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d: !perm_0 Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {q}, traversed: {} } }` failed at the following rule(s):
                                                                the rule "ref|mut place" at (expressions.rs) failed because
                                                                  judgment `access_permitted { access: ref, place: p, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d: !perm_0 Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {q}, traversed: {} } }` failed at the following rule(s):
                                                                    the rule "access_permitted" at (accesses.rs) failed because
                                                                      judgment `env_permits_access { access: ref, place: p, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d: !perm_0 Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {q}, traversed: {} } }` failed at the following rule(s):
                                                                        the rule "env_permits_access" at (accesses.rs) failed because
                                                                          judgment `parameters_permit_access { parameters: [mut [p] Data], access: ref, place: p, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d: !perm_0 Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                            the rule "cons" at (accesses.rs) failed because
                                                                              judgment `parameter_permits_access { parameter: mut [p] Data, access: ref, place: p, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d: !perm_0 Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                the rule "parameter" at (accesses.rs) failed because
                                                                                  judgment `"flat_map"` failed at the following rule(s):
                                                                                    failed at (quantifiers.rs) because
                                                                                      judgment `lien_permit_access { lien: mt(p), access: ref, accessed_place: p, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: given Main, d: !perm_0 Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {mut(!perm_0), relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                                                                        the rule "mut'd" at (accesses.rs) failed because
                                                                                          judgment `mut_place_permits_access { leased_place: p, access: ref, accessed_place: p }` failed at the following rule(s):
                                                                                            the rule "lease-mutation" at (accesses.rs) failed because
                                                                                              condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
                                                                                                &accessed_place = p
                                                                                                &leased_place = p"#]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_leased_P_leased_P_data_to_P_data() {
    crate::assert_ok!({
        class Data {
        }
        class Main {
            fn test[perm P](given self, data: P Data) -> P Data
            where
                mut(P),
            {
                let p: mut[data] Data = data.mut;
                p.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn forall_leased_P_shared_P_data_to_our_P_data() {
    crate::assert_ok!({
        class Data {
        }
        class Main {
            fn test[perm P](given self, data: P Data) -> shared P Data
            where
                mut(P),
            {
                let p: ref[data] Data = data.ref;
                p.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn forall_shared_P_ref_P_data_to_our_P_data() {
    crate::assert_ok!({
        class Data {
        }
        class Main {
            fn test[perm P](given self, data: P Data) -> shared P Data
            where
                copy(P),
            {
                let p: ref[data] Data = data.ref;
                p.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn foo_bar_baz() {
    // Can coerce from `mut[p] mut[d]` to `mut[d]`
    // because `p` is dead.
    crate::assert_ok!({
        class Pair[ty A, ty B] {
            a: A;
            b: B;
        }
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test[perm Q, perm R](
              given self, 
              pair: Pair[Q Data, R Data],
              data: mut[pair] Q Data,
            )
            where
                mut(Q),
                mut(R),
            {
                let data2: Q Data = data.give;
            }
        }
        });
}
