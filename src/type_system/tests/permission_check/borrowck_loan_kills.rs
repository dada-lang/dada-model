//! Scenarios that Rust's borrowck handles through "kills" of a loan.

use formality_core::test;
use formality_core::test_util::ResultTestExt;

use crate::{dada_lang::term, type_system::check_program};

// Demonstrates how 'live after' combined with loan cancellation
// avoids loan kills while having a similar effect -- here,
// `p = q.give` is allowed because `p` is dead and so the type
// of `q` can be upcast from `leased[p.next]` to `leased[list]`.
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
              let p: leased[list] List = list.lease;
              let q: leased[p.next] leased[list] List = p.next.lease;
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
                                   judgment `type_statements_with_final_ty { statements: [let q = p . next . lease ;, let v = p . value . share ;, p = q . give ;, v . give ;, p . value = new Data () ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, list: my List, p: leased [list] my List}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [let v = p . value . share ;, p = q . give ;, v . give ;, p . value = new Data () ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, list: my List, p: leased [list] my List, q: leased [p . next] leased [list] my List}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [p = q . give ;, v . give ;, p . value = new Data () ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, list: my List, p: leased [list] my List, q: leased [p . next] leased [list] my List, v: shared [p . value] leased [list] my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: p = q . give ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, list: my List, p: leased [list] my List, q: leased [p . next] leased [list] my List, v: shared [p . value] leased [list] my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {v}, traversed: {p} } }` failed at the following rule(s):
                                                 the rule "reassign" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `type_expr_as { expr: q . give, as_ty: leased [list] my List, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, list: my List, p: leased [list] my List, q: leased [p . next] leased [list] my List, v: shared [p . value] leased [list] my Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {v}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `sub { a: leased [p . next] leased [list] my List, b: leased [list] my List, live_after: LivePlaces { accessed: {v}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, list: my List, p: leased [list] my List, q: leased [p . next] leased [list] my List, v: shared [p . value] leased [list] my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `sub_under { cx_a: {}, a: leased [p . next] leased [list] my List, cx_b: {}, b: leased [list] my List, live_after: LivePlaces { accessed: {v}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, list: my List, p: leased [list] my List, q: leased [p . next] leased [list] my List, v: shared [p . value] leased [list] my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                               judgment `sub_some { lien_data_a: LienData { liens: {Lent, Leased(list), Leased(p . next)}, data: NamedTy(List) }, lien_datas_b: {LienData { liens: {Lent, Leased(list)}, data: NamedTy(List) }}, live_after: LivePlaces { accessed: {v}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, list: my List, p: leased [list] my List, q: leased [p . next] leased [list] my List, v: shared [p . value] leased [list] my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `sub_lien_data { lien_data_a: LienData { liens: {Lent, Leased(list), Leased(p . next)}, data: NamedTy(List) }, lien_data_b: LienData { liens: {Lent, Leased(list)}, data: NamedTy(List) }, live_after: LivePlaces { accessed: {v}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, list: my List, p: leased [list] my List, q: leased [p . next] leased [list] my List, v: shared [p . value] leased [list] my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                                                       judgment `sub_lien_sets { liens_a: {Lent, Leased(list), Leased(p . next)}, liens_b: {Lent, Leased(list)}, live_after: LivePlaces { accessed: {v}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, list: my List, p: leased [list] my List, q: leased [p . next] leased [list] my List, v: shared [p . value] leased [list] my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "sub-some" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `"flat_map"` failed at the following rule(s):
                                                                             failed at (src/file.rs:LL:CC) because
                                                                               judgment `"flat_map"` failed at the following rule(s):
                                                                                 failed at (src/file.rs:LL:CC) because
                                                                                   judgment `sub_some_lien { lien_a: Leased(p . next), liens_b: {Lent, Leased(list)}, live_after: LivePlaces { accessed: {v}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, list: my List, p: leased [list] my List, q: leased [p . next] leased [list] my List, v: shared [p . value] leased [list] my Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                                     the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                                                       judgment had no applicable rules: `sub_lien { lien_a: Leased(p . next), lien_b: Leased(list), live_after: LivePlaces { accessed: {v}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, list: my List, p: leased [list] my List, q: leased [p . next] leased [list] my List, v: shared [p . value] leased [list] my Data}, assumptions: {}, fresh: 0 } }`
                                                                                     the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                                                       judgment had no applicable rules: `sub_lien { lien_a: Leased(p . next), lien_b: Lent, live_after: LivePlaces { accessed: {v}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, list: my List, p: leased [list] my List, q: leased [p . next] leased [list] my List, v: shared [p . value] leased [list] my Data}, assumptions: {}, fresh: 0 } }`"#]]);
}

// FIXME: panics because of a bug in the formality parser code.
#[test]
#[should_panic]
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
