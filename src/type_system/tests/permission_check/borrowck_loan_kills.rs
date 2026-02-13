//! Scenarios that Rust's borrowck handles through "kills" of a loan.

use formality_core::test;

// Demonstrates how 'live after' combined with loan cancellation
// avoids loan kills while having a similar effect -- here,
// `p = q.give` is allowed because `p` is dead and so the type
// of `q` can be upcast from `mut[p.next]` to `mut[list]`.
#[test]
fn walk_linked_list_1step_explicit_types() {
    crate::assert_ok!({
          class Data {}

          class List {
            value: Data;
            next: List;
          }

          class Main {
            fn main(given self, list: given List) {
              let p: mut[list] List = list.mut;
              let q: mut[p.next] List = p.next.mut;
              p = q.give;
              p.value = new Data();
              ();
            }
          }
    });
}

// As above but demonstrating that no upcasting is needed.
#[test]
fn walk_linked_list_1step_no_types() {
    crate::assert_ok!({
          class Data {}

          class List {
            value: Data;
            next: List;
          }

          class Main {
            fn main(given self, list: given List) {
              let p = list.mut;
              let q = p.next.mut;
              p = q.give;
              p.value = new Data();
              ();
            }
          }
    });
}

// As above but where `p` is still live when `p = q.give` is executed.
#[test]
fn walk_linked_list_1step_p_live() {
    crate::assert_err!({
          class Data {}

          class List {
            value: Data;
            next: List;
          }

          class Main {
            fn main(given self, list: given List) {
              let p = list.mut;
              let q = p.next.mut;
              let v = p.value.ref;
              p = q.give;
              v.give;
              p.value = new Data();
              ();
            }
          }
    }, expect_test::expect![[r#"
        the rule "check_class" at (classes.rs) failed because
          judgment `check_method { decl: fn main (given self list : given List) -> () { let p = list . mut ; let q = p . next . mut ; let v = p . value . ref ; p = q . give ; v . give ; p . value = new Data () ; () ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
            the rule "check_method" at (methods.rs) failed because
              judgment `check_body { body: { let p = list . mut ; let q = p . next . mut ; let v = p . value . ref ; p = q . give ; v . give ; p . value = new Data () ; () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, list: given List}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "block" at (methods.rs) failed because
                  judgment `can_type_expr_as { expr: { let p = list . mut ; let q = p . next . mut ; let v = p . value . ref ; p = q . give ; v . give ; p . value = new Data () ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, list: given List}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                    the rule "can_type_expr_as" at (expressions.rs) failed because
                      judgment `type_expr_as { expr: { let p = list . mut ; let q = p . next . mut ; let v = p . value . ref ; p = q . give ; v . give ; p . value = new Data () ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, list: given List}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr { expr: { let p = list . mut ; let q = p . next . mut ; let v = p . value . ref ; p = q . give ; v . give ; p . value = new Data () ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, list: given List}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "block" at (expressions.rs) failed because
                              judgment `type_block { block: { let p = list . mut ; let q = p . next . mut ; let v = p . value . ref ; p = q . give ; v . give ; p . value = new Data () ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, list: given List}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "place" at (blocks.rs) failed because
                                  judgment `type_statements_with_final_ty { statements: [let p = list . mut ;, let q = p . next . mut ;, let v = p . value . ref ;, p = q . give ;, v . give ;, p . value = new Data () ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, list: given List}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "cons" at (statements.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let q = p . next . mut ;, let v = p . value . ref ;, p = q . give ;, v . give ;, p . value = new Data () ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, list: given List, p: mut [list] List}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let v = p . value . ref ;, p = q . give ;, v . give ;, p . value = new Data () ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, list: given List, p: mut [list] List, q: mut [p . next] List}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [p = q . give ;, v . give ;, p . value = new Data () ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, list: given List, p: mut [list] List, q: mut [p . next] List, v: ref [p . value] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statement { statement: p = q . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, list: given List, p: mut [list] List, q: mut [p . next] List, v: ref [p . value] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {v}, traversed: {p} } }` failed at the following rule(s):
                                                    the rule "reassign" at (statements.rs) failed because
                                                      judgment `env_permits_access { access: mut, place: p, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): mut [list] List, list: given List, p: mut [list] List, q: mut [p . next] List, v: ref [p . value] Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {v}, traversed: {p} } }` failed at the following rule(s):
                                                        the rule "env_permits_access" at (accesses.rs) failed because
                                                          judgment `parameters_permit_access { parameters: [mut [list] List, ref [p . value] Data], access: mut, place: p, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): mut [list] List, list: given List, p: mut [list] List, q: mut [p . next] List, v: ref [p . value] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                            the rule "cons" at (accesses.rs) failed because
                                                              judgment `parameters_permit_access { parameters: [ref [p . value] Data], access: mut, place: p, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): mut [list] List, list: given List, p: mut [list] List, q: mut [p . next] List, v: ref [p . value] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                the rule "cons" at (accesses.rs) failed because
                                                                  judgment `parameter_permits_access { parameter: ref [p . value] Data, access: mut, place: p, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): mut [list] List, list: given List, p: mut [list] List, q: mut [p . next] List, v: ref [p . value] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                    the rule "parameter" at (accesses.rs) failed because
                                                                      judgment `lien_permit_access { lien: rf(p . value), access: mut, accessed_place: p, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): mut [list] List, list: given List, p: mut [list] List, q: mut [p . next] List, v: ref [p . value] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                        the rule "ref'd" at (accesses.rs) failed because
                                                                          judgment `ref_place_permits_access { shared_place: p . value, access: mut, accessed_place: p }` failed at the following rule(s):
                                                                            the rule "share-mutation" at (accesses.rs) failed because
                                                                              condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
                                                                                &accessed_place = p
                                                                                &shared_place = p . value"#]]);
}

// FIXME: panics because of a bug in the formality parser code.
#[test]
#[should_panic]
fn walk_linked_list_n_steps() {
    crate::assert_ok!({
          class Data {}

          class List {
            value: Data;
            next: List;
          }

          class Main {
            fn main(given self, list: given List) {
              let p = list.mut;
              loop {
                p.value = new Data();
                let q = p.next.mut;
                p = q.give;
              };
              ();
            }
          }
    });
}
