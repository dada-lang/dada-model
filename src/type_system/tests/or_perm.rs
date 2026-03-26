use formality_core::test;

// =============================================================================
// Phase 1a: Tests for Perm::Or
//
// These tests cover:
// - Well-formedness (check_perm): same-category branches pass, mixed fail
// - Predicates: for-all semantics on Or branches
// - Subtyping: Or vs multi-place equivalence
// - Nested Or rejection
// - Ascription::Ty bug fix (check_type on let-binding type annotations)
// =============================================================================

// ---------------------------------------------------------------------------
// Well-formedness: same category → ok
// ---------------------------------------------------------------------------

/// or(ref[x], ref[y]) — both copy ✅
#[test]
fn wf_or_both_ref() {
    crate::assert_ok!({
        class Data {}
        class Main {
            fn test(given self, x: given Data, y: given Data, d: or(ref[x], ref[y]) Data) {
                ();
            }
        }
    });
}

/// or(ref[x], shared) — both copy ✅
#[test]
fn wf_or_ref_and_shared() {
    crate::assert_ok!({
        class Data {}
        class Main {
            fn test(given self, x: given Data, d: or(ref[x], shared) Data) {
                ();
            }
        }
    });
}

/// or(mut[x], mut[y]) — both mut ✅
#[test]
fn wf_or_both_mut() {
    crate::assert_ok!({
        class Data {}
        class Main {
            fn test(given self, x: given Data, y: given Data, d: or(mut[x], mut[y]) Data) {
                ();
            }
        }
    });
}

/// or(given, given) — both given ✅
#[test]
fn wf_or_both_given() {
    crate::assert_ok!({
        class Data {}
        class Main {
            fn test(given self, d: or(given, given) Data) {
                ();
            }
        }
    });
}

// ---------------------------------------------------------------------------
// Well-formedness: mixed category → error
// ---------------------------------------------------------------------------

/// or(given, ref[x]) — mixed given/copy ❌
#[test]
fn wf_or_given_and_ref() {
    crate::assert_err!({
        class Data {}
        class Main {
            fn test(given self, x: given Data, d: or(given, ref[x]) Data) {
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "or" at (types.rs) failed because
          ill-formed `or(...)`: branches have mixed permission categories (must all be given, all mut, or all copy)"#]]);
}

/// or(given, mut[x]) — mixed given/mut ❌
#[test]
fn wf_or_given_and_mut() {
    crate::assert_err!({
        class Data {}
        class Main {
            fn test(given self, x: given Data, d: or(given, mut[x]) Data) {
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "or" at (types.rs) failed because
          ill-formed `or(...)`: branches have mixed permission categories (must all be given, all mut, or all copy)"#]]);
}

/// or(shared, mut[x]) — mixed copy/mut ❌
#[test]
fn wf_or_shared_and_mut() {
    crate::assert_err!({
        class Data {}
        class Main {
            fn test(given self, x: given Data, d: or(shared, mut[x]) Data) {
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "or" at (types.rs) failed because
          ill-formed `or(...)`: branches have mixed permission categories (must all be given, all mut, or all copy)"#]]);
}

// ---------------------------------------------------------------------------
// Nested Or rejection (defense-in-depth)
// ---------------------------------------------------------------------------

/// or(or(ref[x], ref[y]), ref[z]) — nested Or should be rejected by check_perm ❌
#[test]
fn wf_or_nested_rejected() {
    crate::assert_err!({
        class Data {}
        class Main {
            fn test(given self, x: given Data, y: given Data, z: given Data,
                    d: or(or(ref[x], ref[y]), ref[z]) Data) {
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "or" at (types.rs) failed because
          condition evaluted to false: `perms.iter().all(|p| !matches!(p, Perm::Or(_)))`"#]]);
}

// ---------------------------------------------------------------------------
// Predicates: for-all semantics
//
// Tests explicitly pass or(...) as a perm parameter to a function with
// a where-clause constraint, since the model doesn't support inference.
// ---------------------------------------------------------------------------

/// or(ref[x], shared) is copy ✅ — both branches are copy
#[test]
fn predicate_or_copy_both_copy() {
    crate::assert_ok!({
        class Data {}
        class Main {
            fn check[perm P](given self) where P is copy { (); }
            fn test(given self, x: given Data) {
                self.give.check[or(ref[x], shared)]();
                ();
            }
        }
    });
}

/// or(mut[x], mut[y]) is move ✅ — both branches are move
#[test]
fn predicate_or_move_both_mut() {
    crate::assert_ok!({
        class Data {}
        class Main {
            fn check[perm P](given self) where P is move { (); }
            fn test(given self, x: given Data, y: given Data) {
                self.give.check[or(mut[x], mut[y])]();
                ();
            }
        }
    });
}

/// or(mut[x], mut[y]) is mut ✅ — both branches are mut
#[test]
fn predicate_or_mut_both_mut() {
    crate::assert_ok!({
        class Data {}
        class Main {
            fn check[perm P](given self) where P is mut { (); }
            fn test(given self, x: given Data, y: given Data) {
                self.give.check[or(mut[x], mut[y])]();
                ();
            }
        }
    });
}

/// or(mut[x], mut[y]) is copy ❌ — mut is not copy
#[test]
fn predicate_or_not_copy_when_mut() {
    crate::assert_err!({
        class Data {}
        class Main {
            fn check[perm P](given self) where P is copy { (); }
            fn test(given self, x: given Data, y: given Data) {
                self.give.check[or(mut[x], mut[y])]();
                ();
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { } class Main { fn check [perm] (given self) -> () where ^perm0_0 is copy { () ; } fn test (given self x : given Data, y : given Data) -> () { self . give . check [or(mut [x], mut [y])] () ; () ; } } }`"]);
}

/// or(given, given) is given ✅
#[test]
fn predicate_or_given_both_given() {
    crate::assert_ok!({
        class Data {}
        class Main {
            fn check[perm P](given self) where P is given { (); }
            fn test(given self) {
                self.give.check[or(given, given)]();
                ();
            }
        }
    });
}

/// or(given, given) is owned ✅ — given implies owned
#[test]
fn predicate_or_owned_both_given() {
    crate::assert_ok!({
        class Data {}
        class Main {
            fn check[perm P](given self) where P is owned { (); }
            fn test(given self) {
                self.give.check[or(given, given)]();
                ();
            }
        }
    });
}

/// or(given, given) is copy ❌ — given is not copy
#[test]
fn predicate_or_not_copy_when_given() {
    crate::assert_err!({
        class Data {}
        class Main {
            fn check[perm P](given self) where P is copy { (); }
            fn test(given self) {
                self.give.check[or(given, given)]();
                ();
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { } class Main { fn check [perm] (given self) -> () where ^perm0_0 is copy { () ; } fn test (given self) -> () { self . give . check [or(given)] () ; () ; } } }`"]);
}

/// or(given, given) is move ✅ — given implies move
#[test]
fn predicate_or_move_when_given() {
    crate::assert_ok!({
        class Data {}
        class Main {
            fn check[perm P](given self) where P is move { (); }
            fn test(given self) {
                self.give.check[or(given, given)]();
                ();
            }
        }
    });
}

/// or(ref[x], mut[y]) is copy ❌ — mut branch is not copy (even if ref branch is)
#[test]
fn predicate_or_not_copy_mixed_ref_mut() {
    crate::assert_err!({
        class Data {}
        class Main {
            fn check[perm P](given self) where P is copy { (); }
            fn test(given self, x: given Data, y: given Data) {
                self.give.check[or(ref[x], mut[y])]();
                ();
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Data { } class Main { fn check [perm] (given self) -> () where ^perm0_0 is copy { () ; } fn test (given self x : given Data, y : given Data) -> () { self . give . check [or(ref [x], mut [y])] () ; () ; } } }`"]);
}

// ---------------------------------------------------------------------------
// Subtyping: Or vs multi-place permissions
// ---------------------------------------------------------------------------

/// or(ref[x], ref[y]) T <: ref[x, y] T ✅
/// Each Or branch is one of the existential branches of ref[x, y].
#[test]
fn subtype_or_ref_to_multi_ref() {
    crate::assert_ok!({
        class Data {}
        class Main {
            fn test(given self, x: given Data, y: given Data, d: or(ref[x], ref[y]) Data) {
                let r: ref[x, y] Data = d.give;
                ();
            }
        }
    });
}

/// ref[x, y] T <: or(ref[x], ref[y]) T ✅
/// Each existential branch of ref[x, y] matches an Or branch.
#[test]
fn subtype_multi_ref_to_or_ref() {
    crate::assert_ok!({
        class Data {}
        class Main {
            fn test(given self, x: given Data, y: given Data, d: ref[x, y] Data) {
                let r: or(ref[x], ref[y]) Data = d.give;
                ();
            }
        }
    });
}

/// or(ref[x], ref[y]) T <: ref[x] T ❌
/// ref[y] is not a subtype of ref[x] in general.
#[test]
fn subtype_or_ref_not_subtype_single_ref() {
    crate::assert_err!({
        class Data {}
        class Main {
            fn test(given self, x: given Data, y: given Data, d: or(ref[x], ref[y]) Data) {
                let r: ref[x] Data = d.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
          condition evaluted to false: `place_b.is_prefix_of(place_a)`
            place_b = x
            place_a = y"#]]);
}

/// or(ref[x], ref[y]) <: or(ref[x], ref[y], ref[z]) ✅
/// Subset: every branch on the left (x, y) has a match on the right (x, y, z).
#[test]
fn subtype_or_subset() {
    crate::assert_ok!({
        class Data {}
        class Main {
            fn test(given self, x: given Data, y: given Data, z: given Data,
                    d: or(ref[x], ref[y]) Data) {
                let r: or(ref[x], ref[y], ref[z]) Data = d.give;
                ();
            }
        }
    });
}

/// or(ref[x], ref[y], ref[z]) <: or(ref[x], ref[y]) ❌
/// Superset: z's chain has no match on the right.
#[test]
fn subtype_or_superset_fails() {
    crate::assert_err!({
        class Data {}
        class Main {
            fn test(given self, x: given Data, y: given Data, z: given Data,
                    d: or(ref[x], ref[y], ref[z]) Data) {
                let r: or(ref[x], ref[y]) Data = d.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
          condition evaluted to false: `place_b.is_prefix_of(place_a)`
            place_b = x
            place_a = z

        the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
          condition evaluted to false: `place_b.is_prefix_of(place_a)`
            place_b = y
            place_a = z"#]]);
}

/// ref[x] <: or(ref[x], ref[y]) ✅
/// A single perm is a subtype of an Or that includes it.
#[test]
fn subtype_single_perm_to_or_containing_it() {
    crate::assert_ok!({
        class Data {}
        class Main {
            fn test(given self, x: given Data, y: given Data, d: ref[x] Data) {
                let r: or(ref[x], ref[y]) Data = d.give;
                ();
            }
        }
    });
}

/// or(ref[x], ref[y]) <: or(ref[y], ref[z]) ❌
/// Partial overlap: ref[x] has no match in {ref[y], ref[z]}.
#[test]
fn subtype_or_partial_overlap_fails() {
    crate::assert_err!({
        class Data {}
        class Main {
            fn test(given self, x: given Data, y: given Data, z: given Data,
                    d: or(ref[x], ref[y]) Data) {
                let r: or(ref[y], ref[z]) Data = d.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
          condition evaluted to false: `place_b.is_prefix_of(place_a)`
            place_b = y
            place_a = x

        the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
          condition evaluted to false: `place_b.is_prefix_of(place_a)`
            place_b = z
            place_a = x"#]]);
}

/// or(ref[x], ref[y]) <: or(ref[x], ref[y]) ✅
/// Reflexivity: an Or is a subtype of itself.
#[test]
fn subtype_or_reflexive() {
    crate::assert_ok!({
        class Data {}
        class Main {
            fn test(given self, x: given Data, y: given Data, d: or(ref[x], ref[y]) Data) {
                let r: or(ref[x], ref[y]) Data = d.give;
                ();
            }
        }
    });
}

/// or(mut[x], mut[y]) <: or(mut[x], mut[y], mut[z]) ✅
/// Same subset logic works for mut-category Or.
#[test]
fn subtype_or_mut_subset() {
    crate::assert_ok!({
        class Data {}
        class Main {
            fn test(given self, x: given Data, y: given Data, z: given Data,
                    d: or(mut[x], mut[y]) Data) {
                let r: or(mut[x], mut[y], mut[z]) Data = d.give;
                ();
            }
        }
    });
}

/// or(ref[x], ref[y]) <: ref[x, y, z] ✅
/// Or branches are a subset of the multi-place existential branches.
#[test]
fn subtype_or_to_wider_multi_ref() {
    crate::assert_ok!({
        class Data {}
        class Main {
            fn test(given self, x: given Data, y: given Data, z: given Data,
                    d: or(ref[x], ref[y]) Data) {
                let r: ref[x, y, z] Data = d.give;
                ();
            }
        }
    });
}

/// ref[x, y, z] <: or(ref[x], ref[y]) ❌
/// Multi-place has a branch for z that doesn't match any Or branch.
#[test]
fn subtype_wider_multi_ref_to_or_fails() {
    crate::assert_err!({
        class Data {}
        class Main {
            fn test(given self, x: given Data, y: given Data, z: given Data,
                    d: ref[x, y, z] Data) {
                let r: or(ref[x], ref[y]) Data = d.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
          condition evaluted to false: `place_b.is_prefix_of(place_a)`
            place_b = x
            place_a = z

        the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
          condition evaluted to false: `place_b.is_prefix_of(place_a)`
            place_b = y
            place_a = z"#]]);
}

// ---------------------------------------------------------------------------
// Ascription::Ty bug fix: check_type on let-binding type annotations
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Borrow-checker interaction: Or permissions must restrict source places
//
// These use explicit or(...) type annotations to test the borrow checker
// directly, independent of call-site normalization.
// ---------------------------------------------------------------------------

/// or(ref[d1], ref[d2]) should block giving d1 while result is live.
/// The result borrows from d1 (in one branch), so d1 can't be moved.
#[test]
fn or_ref_blocks_give_d1() {
    crate::assert_err!({
        class Data {}
        class Main {
            fn go(given self) {
                let d1 = new Data();
                let d2 = new Data();
                let result: or(ref[d1], ref[d2]) Data = d1.ref;
                d1.give;
                result.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
            accessed_place = @ fresh(0)
            shared_place = @ fresh(0)"#]]);
}

/// or(ref[d1], ref[d2]) should block giving d2 while result is live.
#[test]
fn or_ref_blocks_give_d2() {
    crate::assert_err!({
        class Data {}
        class Main {
            fn go(given self) {
                let d1 = new Data();
                let d2 = new Data();
                let result: or(ref[d1], ref[d2]) Data = d2.ref;
                d2.give;
                result.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
            accessed_place = @ fresh(0)
            shared_place = @ fresh(0)"#]]);
}

/// or(mut[d1], mut[d2]) should block mutating d1 while result is live.
#[test]
fn or_mut_blocks_mut_d1() {
    crate::assert_err!({
        class Data {
            fn write(mut[self] self) { (); }
        }
        class Main {
            fn go(given self) {
                let d1 = new Data();
                let d2 = new Data();
                let result: or(mut[d1], mut[d2]) Data = d1.mut;
                d1.mut.write();
                result.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "lease-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
            accessed_place = d1
            leased_place = d1"#]]);
}

/// or(shared mut[d1], shared mut[d2]) from ref-through-mut should block
/// mutating d1 while result is live.
#[test]
fn or_shared_mut_blocks_mut_d1() {
    crate::assert_err!({
        class Data {
            fn write(mut[self] self) { (); }
        }
        class Main {
            fn go(given self) {
                let d1 = new Data();
                let d2 = new Data();
                let q: mut[d1] Data = d1.mut;
                let result: or(shared mut[d1], shared mut[d2]) Data = q.ref;
                d1.mut.write();
                result.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "lease-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
            accessed_place = d1
            leased_place = d1"#]]);
}

/// After the or-borrowed result is dead, d1 and d2 should be accessible again.
#[test]
fn or_ref_allows_give_after_result_dead() {
    crate::assert_ok!({
        class Data {}
        class Sink {
            fn consume(given self, d: given Data) { (); }
        }
        class Main {
            fn go(given self) {
                let d1 = new Data();
                let d2 = new Data();
                let result: or(ref[d1], ref[d2]) Data = d1.ref;
                result.give;
                let sink1 = new Sink();
                sink1.give.consume(d1.give);
                let sink2 = new Sink();
                sink2.give.consume(d2.give);
                ();
            }
        }
    });
}

// ---------------------------------------------------------------------------
// Ascription::Ty bug fix
// ---------------------------------------------------------------------------

/// let x: or(given, ref[y]) T = ... — mixed categories in type annotation.
/// Should be rejected by check_type. Currently bypasses check_type (bug).
#[test]
fn ascription_ty_rejects_ill_formed_or() {
    crate::assert_err!({
        class Data {}
        class Main {
            fn test(given self, y: given Data) {
                let x: or(given, ref[y]) Data = y.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "or" at (types.rs) failed because
          ill-formed `or(...)`: branches have mixed permission categories (must all be given, all mut, or all copy)"#]]);
}
