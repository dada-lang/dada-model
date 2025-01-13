//! Scenarios that Rust's borrowck handles through "kills" of a loan.

use formality_core::test;
use formality_core::test_util::ResultTestExt;

use crate::{dada_lang::term, type_system::check_program};

// Demonstrates how 'live after' combined with loan cancellation
// avoids loan kills while having a similar effect -- here,
// `p = q.give` is allowed because `p` is dead and so the type
// of `q` can be upcast from `leased{p.next}` to `leased{list}`.
#[test]
fn walk_linked_list_1step_explicit_types() {
    check_program(&term(
        "
          class Data {}

          class List {
            value: Data;
            next: List;
          }

          class Main {
            fn main(my self, list: my List) {
              let p: leased{list} List = list.lease;
              let q: leased{p.next} leased{list} List = p.next.lease;
              p = q.give;
              p.value = new Data();
              ();
            }
          }
    ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

// As above but demonstrating that no upcasting is needed.
#[test]
fn walk_linked_list_1step_no_types() {
    check_program(&term(
        "
          class Data {}

          class List {
            value: Data;
            next: List;
          }

          class Main {
            fn main(my self, list: my List) {
              let p = list.lease;
              let q = p.next.lease;
              p = q.give;
              p.value = new Data();
              ();
            }
          }
    ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}

// As above but where `p` is still live when `p = q.give` is executed.
#[test]
fn walk_linked_list_1step_p_live() {
    check_program(&term(
        "
          class Data {}

          class List {
            value: Data;
            next: List;
          }

          class Main {
            fn main(my self, list: my List) {
              let p = list.lease;
              let q = p.next.lease;
              let v = p.value.share;
              p = q.give;
              v.give;
              p.value = new Data();
              ();
            }
          }
    ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class List { value : Data ; next : List ; } class Main { fn main (my self list : my List) -> () { let p = list . lease ; let q = p . next . lease ; let v = p . value . share ; p = q . give ; v . give ; p . value = new Data () ; () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `main`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let p = list . lease ; let q = p . next . lease ; let v = p . value . share ; p = q . give ; v . give ; p . value = new Data () ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, list: my List}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let p = list . lease ; let q = p . next . lease ; let v = p . value . share ; p = q . give ; v . give ; p . value = new Data () ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, list: my List}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let p = list . lease ; let q = p . next . lease ; let v = p . value . share ; p = q . give ; v . give ; p . value = new Data () ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, list: my List}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let p = list . lease ; let q = p . next . lease ; let v = p . value . share ; p = q . give ; v . give ; p . value = new Data () ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, list: my List}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let p = list . lease ;, let q = p . next . lease ;, let v = p . value . share ;, p = q . give ;, v . give ;, p . value = new Data () ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, list: my List}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let q = p . next . lease ;, let v = p . value . share ;, p = q . give ;, v . give ;, p . value = new Data () ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, list: my List, p: leased {list} my List}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let v = p . value . share ;, p = q . give ;, v . give ;, p . value = new Data () ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, list: my List, p: leased {list} my List, q: leased {p . next} leased {list} my List}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [p = q . give ;, v . give ;, p . value = new Data () ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, list: my List, p: leased {list} my List, q: leased {p . next} leased {list} my List, v: shared {p . value} leased {list} my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: p = q . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, list: my List, p: leased {list} my List, q: leased {p . next} leased {list} my List, v: shared {p . value} leased {list} my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {v}, traversed: {p} } }` failed at the following rule(s):
                                                 the rule "reassign" failed at step #4 (src/file.rs:LL:CC) because
                                                   judgment `env_permits_access { access: lease, place: p, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): leased {list} my List, list: my List, p: leased {list} my List, q: leased {p . next} leased {list} my List, v: shared {p . value} leased {list} my Data}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {v}, traversed: {p} } }` failed at the following rule(s):
                                                     the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `parameters_permit_access { parameters: [leased {list} my List, shared {p . value} leased {list} my Data], access: lease, place: p, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): leased {list} my List, list: my List, p: leased {list} my List, q: leased {p . next} leased {list} my List, v: shared {p . value} leased {list} my Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                                           judgment `parameters_permit_access { parameters: [shared {p . value} leased {list} my Data], access: lease, place: p, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): leased {list} my List, list: my List, p: leased {list} my List, q: leased {p . next} leased {list} my List, v: shared {p . value} leased {list} my Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                             the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `parameter_permits_access { parameter: shared {p . value} leased {list} my Data, access: lease, place: p, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): leased {list} my List, list: my List, p: leased {list} my List, q: leased {p . next} leased {list} my List, v: shared {p . value} leased {list} my Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `lien_permit_access { lien: shared{p . value}, access: lease, accessed_place: p, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): leased {list} my List, list: my List, p: leased {list} my List, q: leased {p . next} leased {list} my List, v: shared {p . value} leased {list} my Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                     the rule "shared" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `shared_place_permits_access { shared_place: p . value, access: lease, accessed_place: p }` failed at the following rule(s):
                                                                         the rule "share-mutation" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
                                                                             &accessed_place = p
                                                                             &shared_place = p . value"#]]);
}

// FIXME: panics because of a bug in the formality parser code.
#[test(should_panic)]
fn walk_linked_list_n_steps() {
    check_program(&term(
        "
          class Data {}

          class List {
            value: Data;
            next: List;
          }

          class Main {
            fn main(my self, list: my List) {
              let p = list.lease;
              loop {
                p.value = new Data();
                let q = p.next.lease;
                p = q.give;
              };
              ();
            }
          }
    ",
    ))
    .assert_ok(expect_test::expect!["()"]);
}
