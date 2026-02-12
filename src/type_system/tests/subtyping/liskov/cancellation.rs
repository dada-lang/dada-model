//! # Liveness and cancellation
//!
//! When variables are dead, subtyping allows for *cancellation*, so e.g. if `d1` is dead,
//! then `ref[d1] mut[d2] Foo` is a subtype of `mut[d2] Foo`. Cancellation only
//! applies when we have a shared/leased permission applies to a leased permission.
//!
//! Consideration to test:
//!
//! * C1. Cancellation can remove "relative" permissions like `shared` and `leased`, but not owned permissions
//!   like `given` or `shared` nor generic permissions (since in that case we do not know which variables they
//!   may refer to)
//! * C2. Cancellation can only occur if all variables in the permission are dead: so `ref[d1, d2]` can only
//!   be canceled if `d1` and `d2` are both dead.
//! * C3. Cancellation cannot convert a shared permission into a leased permission.
//! * C4. Subtyping must account for future cancellation. So e.g., `mut[d1, d2] Foo` cannot be a subtype of
//!   `mut[d1] mut[d2] Foo` since, if `d1` later goes dead, the supertype could be upcast
//!   to `mut[d2] Foo` but the subtype could not. That would be unsound.

use formality_core::test;

// C1. Cancellation can remove "relative" permissions like `shared` and `leased`.

#[test]
fn c1_remove_relative_shared() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: ref[m] Data = m.ref;
                let q: ref[p] ref[m] Data = p.ref;
                let r: ref[m] Data = q.give;
            }
        }
        });
}

#[test]
fn c1_remove_relative_leased() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: mut[m] Data = m.mut;
                let q: mut[p] Data = p.mut;
                let r: mut[m] Data = q.give;
            }
        }
        });
}

// C1. Cancellation and `given` permission are not very relevant.
//
// The `given given` type here is equivalent to `given` so this just becomes
// ownership transfer.

#[test]
fn c1_remove_given() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: given given Data = m.give;
                let q: given Data = p.give;
            }
        }
        });
}

// C1. Cancellation cannot remove owned permissions `shared`.

#[test]
fn c1_remove_our() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: shared given Data = m.give;
                let q: given Data = p.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

// C1. Cancellation cannot remove generic permissions `shared`.

#[test]
fn c1_remove_generic_permissions() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self, p: P given Data) {
                let q: given Data = p.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

// C2. Cancellation can only occur if all variables in the permission are dead.

#[test]
fn c2_shared_shared_one_of_one_variables_dead() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: ref[m] Data = m.ref;
                let q: ref[p] ref[m] Data = p.ref;
                let r: ref[m] Data = q.give;
            }
        }
        });
}

#[test]
fn c2_shared_shared_two_of_two_variables_dead() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: ref[m] Data = m.ref;
                let q: ref[m] Data = m.ref;
                let r: ref[p, q] ref[m] Data = p.ref;
                let s: ref[m] Data = r.give;
            }
        }
        });
}

#[test]
fn c2_shared_shared_one_of_two_variables_dead() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: ref[m] Data = m.ref;
                let q: ref[m] Data = m.ref;
                let r: ref[p, q] ref[m] Data = p.ref;
                let s: ref[m] Data = r.give;
                q.give;
            }
        }
        }, expect_test::expect![[r#"judgment had no applicable rules: `check_method { decl: fn test [perm] (given self) -> () { let m : given Data = new Data () ; let p : ref [m] Data = m . ref ; let q : ref [m] Data = m . ref ; let r : ref [p, q] ref [m] Data = p . ref ; let s : ref [m] Data = r . give ; q . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }`"#]]);
}

#[test]
fn c2_leased_leased_one_of_one_variables_dead() {
    crate::assert_ok!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: mut[m] Data = m.mut;
                let q: mut[p] Data = p.mut;
                let r: mut[m] Data = q.give;
            }
        }
        });
}

#[test]
fn c2_leased_leased_two_of_two_variables_dead() {
    crate::assert_ok!({
        class Data {}
        class Pair {
            a: given Data;
            b: given Data;
        }
        class Main {
            fn test[perm P](given self) {
                let m: given Pair = new Pair(new Data(), new Data());
                let p: mut[m.a] Data = m.a.mut;
                let q: mut[m.b] Data = m.b.mut;
                let r: mut[p, q] Data = p.mut;
                let s: mut[m] Data = r.give;
            }
        }
        });
}

#[test]
fn c2_leased_leased_one_of_two_variables_dead() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: mut[m] Data = m.mut;
                let q: mut[m] Data = m.mut;
                let r: mut[p, q] mut[m] Data = p.mut;
                let s: mut[m] Data = r.give;
                q.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "lease-mutation" at (accesses.rs) failed because
              condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
                &accessed_place = m
                &leased_place = m"#]]);
}

// C3. Cancellation cannot convert a shared permission into a leased permission.

#[test]
fn c3_shared_leased_one_of_one_variables_dead() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: mut[m] Data = m.mut;
                let q: ref[p] mut[m] Data = p.ref;
                let r: mut[m] Data = q.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

#[test]
fn c3_shared_leased_two_of_two_variables_dead() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: mut[m] Data = m.ref;
                let q: mut[m] Data = m.ref;
                let r: ref[p, q] mut[m] Data = p.ref;
                let s: ref[m] Data = r.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

#[test]
fn c3_shared_leased_one_of_two_variables_dead() {
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let m: given Data = new Data();
                let p: ref[m] Data = m.ref;
                let q: ref[m] Data = m.ref;
                let r: ref[p, q] ref[m] Data = p.ref;
                let s: ref[m] Data = r.give;
                q.give;
            }
        }
        }, expect_test::expect![[r#"judgment had no applicable rules: `check_method { decl: fn test [perm] (given self) -> () { let m : given Data = new Data () ; let p : ref [m] Data = m . ref ; let q : ref [m] Data = m . ref ; let r : ref [p, q] ref [m] Data = p . ref ; let s : ref [m] Data = r . give ; q . give ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }`"#]]);
}

// C4. Subtyping must account for future cancellation.

#[test]
fn c4_shared_d1d2d3_not_subtype_of_shared_d1_shared_d2d3() {
    // This is interesting. It fails because `ref[d1] ref[d2, d3]`
    // is equivalent to `ref[d2, d3]` and there is clearly no subtyping relation.
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let d1: given Data = new Data();
                let d2: given Data = new Data();
                let d3: given Data = new Data();
                let s1: ref[d1, d2, d3] Data = d1.ref;
                let s2: ref[d1] ref[d2, d3] Data = s1.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                place_b = d2
                &place_a = d1

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                place_b = d3
                &place_a = d1

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

#[test]
fn c4_leased_d1d2d3_subtype_of_leased_d1_leased_d2d3() {
    // This one fails because `mut[d1, d2, d3]` and `mut[d1] mut[d2, d3]` are
    // different; the latter would require that `d1` contained data leased from `d2` or `d3`.
    crate::assert_err!({
        class Data { }
        class Main {
            fn test[perm P](given self) {
                let d1: given Data = new Data();
                let d2: given Data = new Data();
                let d3: given Data = new Data();
                let s1: mut[d1, d2, d3] Data = d1.mut;
                let s2: mut[d1] mut[d2, d3] Data = s1.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

#[test]
fn c4_leased_d1d2_leased_pair_not_subtype_of_leased_d2() {
    // This one fails because you after cancelling `d1` you don't get `d2`.
    crate::assert_err!({
        class Pair {
            a: given Data;
            b: given Data;
        }
        class Data { }
        class Main {
            fn test[perm P](given self, pair: P Pair) where mut(P) {
                let d1: mut[pair.a] Data = pair.a.mut;
                let d2: mut[pair.b] Data = pair.b.mut;
                let s1: mut[d1, d2] Data = d1.mut;
                let s2: mut[d2] Data = s1.give;
                let _x = self.give.consume(pair.give, s2.give);
            }

            fn consume[perm P](given self, pair: P Pair, from_b: mut[pair.b] Data) where mut(P) { (); }
        }
        }, expect_test::expect![[r#"
            the rule "(mut::P) vs (mut::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                place_b = d2
                &place_a = pair . a

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "(mut::P) vs (mut::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                place_b = d2
                &place_a = d1

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}
