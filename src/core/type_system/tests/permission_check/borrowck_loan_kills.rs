//! Scenarios that Rust's borrowck handles through "kills" of a loan.

use formality_core::test;

// Demonstrates how 'live after' combined with loan cancellation
// avoids loan kills while having a similar effect -- here,
// `p = q^` is allowed because `p` is dead and so the type
// of `q` can be upcast from `![p.next]` to `![list]`.
#[test]
fn walk_linked_list_1step_explicit_types() {
    crate::assert_ok!({
          class Data {}

          class List {
            value: Data;
            next: List;
          }

          class Main {
            fn main(^ self, list: ^ List) {
              let p: ![list] List = list!;
              let q: ![p.next] List = p.next!;
              p = q^;
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
            fn main(^ self, list: ^ List) {
              let p = list!;
              let q = p.next!;
              p = q^;
              p.value = new Data();
              ();
            }
          }
    });
}

// As above but where `p` is still live when `p = q^` is executed.
#[test]
fn walk_linked_list_1step_p_live() {
    crate::assert_err!({
          class Data {}

          class List {
            value: Data;
            next: List;
          }

          class Main {
            fn main(^ self, list: ^ List) {
              let p = list!;
              let q = p.next!;
              let v = p.value.share;
              p = q^;
              v^;
              p.value = new Data();
              ();
            }
          }
    }, expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
            accessed_place = p
            shared_place = p . value"#]]);
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
            fn main(^ self, list: ^ List) {
              let p = list!;
              loop {
                p.value = new Data();
                let q = p.next!;
                p = q^;
              };
              ();
            }
          }
    });
}
