//! Scenarios that Rust's borrowck handles through "kills" of a loan.

use formality_core::test;

// Demonstrates how 'live after' combined with loan cancellation
// avoids loan kills while having a similar effect -- here,
// `p = q.give` is allowed because `p` is dead and so the type
// of `q` can be upcast from `mut[p.next]` to `mut[list]`.
#[test]
fn walk_linked_list_1step_explicit_types() {
    crate::assert_ok!("
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
    ");
}

// As above but demonstrating that no upcasting is needed.
#[test]
fn walk_linked_list_1step_no_types() {
    crate::assert_ok!("
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
    ");
}

// As above but where `p` is still live when `p = q.give` is executed.
#[test]
fn walk_linked_list_1step_p_live() {
    crate::assert_err!("
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
    ", expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
            &accessed_place = p
            &shared_place = p . value"#]]);
}

// FIXME: panics because of a bug in the formality parser code.
#[test]
#[should_panic]
fn walk_linked_list_n_steps() {
    crate::assert_ok!("
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
    ");
}
