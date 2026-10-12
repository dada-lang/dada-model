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

/// or(shared[x], shared[y]) — both copy ✅
#[test]
fn wf_or_both_ref() {
    crate::assert_ok!({
        struct Data {}
        struct Main {
            fn test(given self, x: given Data, y: given Data, d: or(shared[x], shared[y]) Data) {
                ();
            }
        }
    });
}

/// or(shared[x], shared) — both copy ✅
#[test]
fn wf_or_ref_and_shared() {
    crate::assert_ok!({
        struct Data {}
        struct Main {
            fn test(given self, x: given Data, d: or(shared[x], shared) Data) {
                ();
            }
        }
    });
}

/// or(![x], ![y]) — both mut ✅
#[test]
fn wf_or_both_mut() {
    crate::assert_ok!({
        struct Data {}
        struct Main {
            fn test(given self, x: given Data, y: given Data, d: or(![x], ![y]) Data) {
                ();
            }
        }
    });
}

/// or(given, given) — both ^ ✅
#[test]
fn wf_or_both_given() {
    crate::assert_ok!({
        struct Data {}
        struct Main {
            fn test(given self, d: or(given, given) Data) {
                ();
            }
        }
    });
}

// ---------------------------------------------------------------------------
// Well-formedness: mixed category → error
// ---------------------------------------------------------------------------

/// or(given, shared[x]) — mixed ^/copy ❌
#[test]
fn wf_or_given_and_ref() {
    crate::assert_err!({
        struct Data {}
        struct Main {
            fn test(given self, x: given Data, d: or(given, shared[x]) Data) {
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "or" at (types.rs) failed because
          ill-formed `or(...)`: branches have mixed permission categories (must all be ^, all mut, or all shared)"#]]);
}

/// or(given, ![x]) — mixed ^/mut ❌
#[test]
fn wf_or_given_and_mut() {
    crate::assert_err!({
        struct Data {}
        struct Main {
            fn test(given self, x: given Data, d: or(given, ![x]) Data) {
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "or" at (types.rs) failed because
          ill-formed `or(...)`: branches have mixed permission categories (must all be ^, all mut, or all shared)"#]]);
}

/// or(shared, ![x]) — mixed copy/mut ❌
#[test]
fn wf_or_shared_and_mut() {
    crate::assert_err!({
        struct Data {}
        struct Main {
            fn test(given self, x: given Data, d: or(shared, ![x]) Data) {
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "or" at (types.rs) failed because
          ill-formed `or(...)`: branches have mixed permission categories (must all be ^, all mut, or all shared)"#]]);
}

// ---------------------------------------------------------------------------
// Nested Or rejection (defense-in-depth)
// ---------------------------------------------------------------------------

/// or(or(shared[x], shared[y]), shared[z]) — nested Or should be rejected by check_perm ❌
#[test]
fn wf_or_nested_rejected() {
    crate::assert_err!({
        struct Data {}
        struct Main {
            fn test(given self, x: given Data, y: given Data, z: given Data,
                    d: or(or(shared[x], shared[y]), shared[z]) Data) {
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

/// or(shared[x], shared) is shared ✅ — both branches are copy
#[test]
fn predicate_or_copy_both_copy() {
    crate::assert_ok!({
        struct Data {}
        struct Main {
            fn check[perm P](given self) where P is shared { (); }
            fn test(given self, x: given Data) {
                self^.check[or(shared[x], shared)]();
                ();
            }
        }
    });
}

/// or(![x], ![y]) is unique ✅ — both branches are move
#[test]
fn predicate_or_move_both_mut() {
    crate::assert_ok!({
        struct Data {}
        struct Main {
            fn check[perm P](given self) where P is unique { (); }
            fn test(given self, x: given Data, y: given Data) {
                self^.check[or(![x], ![y])]();
                ();
            }
        }
    });
}

/// or(![x], ![y]) is mut ✅ — both branches are mut
#[test]
fn predicate_or_mut_both_mut() {
    crate::assert_ok!({
        struct Data {}
        struct Main {
            fn check[perm P](given self) where P is mut { (); }
            fn test(given self, x: given Data, y: given Data) {
                self^.check[or(![x], ![y])]();
                ();
            }
        }
    });
}

/// or(![x], ![y]) is shared ❌ — mut is not copy
#[test]
fn predicate_or_not_copy_when_mut() {
    crate::assert_err!({
        struct Data {}
        struct Main {
            fn check[perm P](given self) where P is shared { (); }
            fn test(given self, x: given Data, y: given Data) {
                self^.check[or(![x], ![y])]();
                ();
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn check [perm] (given self) -> () where ^perm0_0 is shared { () ; } fn test (given self x : given Data, y : given Data) -> () { self ^ . check [or(! [x], ! [y])] () ; () ; } } }`"]);
}

/// or(given, given) is unique and owned ✅
#[test]
fn predicate_or_given_both_given() {
    crate::assert_ok!({
        struct Data {}
        struct Main {
            fn check[perm P](given self) where P is unique, P is owned { (); }
            fn test(given self) {
                self^.check[or(given, given)]();
                ();
            }
        }
    });
}

/// or(given, given) is owned ✅ — given implies owned
#[test]
fn predicate_or_owned_both_given() {
    crate::assert_ok!({
        struct Data {}
        struct Main {
            fn check[perm P](given self) where P is owned { (); }
            fn test(given self) {
                self^.check[or(given, given)]();
                ();
            }
        }
    });
}

/// or(given, given) is shared ❌ — given is not copy
#[test]
fn predicate_or_not_copy_when_given() {
    crate::assert_err!({
        struct Data {}
        struct Main {
            fn check[perm P](given self) where P is shared { (); }
            fn test(given self) {
                self^.check[or(given, given)]();
                ();
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn check [perm] (given self) -> () where ^perm0_0 is shared { () ; } fn test (given self) -> () { self ^ . check [or(given)] () ; () ; } } }`"]);
}

/// or(given, given) is unique ✅ — given implies move
#[test]
fn predicate_or_move_when_given() {
    crate::assert_ok!({
        struct Data {}
        struct Main {
            fn check[perm P](given self) where P is unique { (); }
            fn test(given self) {
                self^.check[or(given, given)]();
                ();
            }
        }
    });
}

/// or(shared[x], ![y]) is shared ❌ — mut branch is not copy (even if place sharing branch is)
#[test]
fn predicate_or_not_copy_mixed_ref_mut() {
    crate::assert_err!({
        struct Data {}
        struct Main {
            fn check[perm P](given self) where P is shared { (); }
            fn test(given self, x: given Data, y: given Data) {
                self^.check[or(shared[x], ![y])]();
                ();
            }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn check [perm] (given self) -> () where ^perm0_0 is shared { () ; } fn test (given self x : given Data, y : given Data) -> () { self ^ . check [or(shared [x], ! [y])] () ; () ; } } }`"]);
}

// ---------------------------------------------------------------------------
// Subtyping: Or vs multi-place permissions
// ---------------------------------------------------------------------------

/// or(shared[x], shared[y]) T <: shared[x, y] T ✅
/// Each Or branch is one of the existential branches of shared[x, y].
#[test]
fn subtype_or_ref_to_multi_ref() {
    crate::assert_ok!({
        struct Data {}
        struct Main {
            fn test(given self, x: given Data, y: given Data, d: or(shared[x], shared[y]) Data) {
                let r: shared[x, y] Data = d^;
                ();
            }
        }
    });
}

/// shared[x, y] T <: or(shared[x], shared[y]) T ✅
/// Each existential branch of shared[x, y] matches an Or branch.
#[test]
fn subtype_multi_ref_to_or_ref() {
    crate::assert_ok!({
        struct Data {}
        struct Main {
            fn test(given self, x: given Data, y: given Data, d: shared[x, y] Data) {
                let r: or(shared[x], shared[y]) Data = d^;
                ();
            }
        }
    });
}

/// or(shared[x], shared[y]) T <: shared[x] T ❌
/// shared[y] is not a subtype of shared[x] in general.
#[test]
fn subtype_or_ref_not_subtype_single_ref() {
    crate::assert_err!({
        struct Data {}
        struct Main {
            fn test(given self, x: given Data, y: given Data, d: or(shared[x], shared[y]) Data) {
                let r: shared[x] Data = d^;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "(shared[place]::P) vs (shared[place]::P)" at (redperms.rs) failed because
          condition evaluted to false: `place_b.is_prefix_of(place_a)`
            place_b = x
            place_a = y"#]]);
}

/// or(shared[x], shared[y]) <: or(shared[x], shared[y], shared[z]) ✅
/// Subset: every branch on the left (x, y) has a match on the right (x, y, z).
#[test]
fn subtype_or_subset() {
    crate::assert_ok!({
        struct Data {}
        struct Main {
            fn test(given self, x: given Data, y: given Data, z: given Data,
                    d: or(shared[x], shared[y]) Data) {
                let r: or(shared[x], shared[y], shared[z]) Data = d^;
                ();
            }
        }
    });
}

/// or(shared[x], shared[y], shared[z]) <: or(shared[x], shared[y]) ❌
/// Superset: z's chain has no match on the right.
#[test]
fn subtype_or_superset_fails() {
    crate::assert_err!({
        struct Data {}
        struct Main {
            fn test(given self, x: given Data, y: given Data, z: given Data,
                    d: or(shared[x], shared[y], shared[z]) Data) {
                let r: or(shared[x], shared[y]) Data = d^;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "(shared[place]::P) vs (shared[place]::P)" at (redperms.rs) failed because
          condition evaluted to false: `place_b.is_prefix_of(place_a)`
            place_b = x
            place_a = z

        the rule "(shared[place]::P) vs (shared[place]::P)" at (redperms.rs) failed because
          condition evaluted to false: `place_b.is_prefix_of(place_a)`
            place_b = y
            place_a = z"#]]);
}

/// shared[x] <: or(shared[x], shared[y]) ✅
/// A single perm is a subtype of an Or that includes it.
#[test]
fn subtype_single_perm_to_or_containing_it() {
    crate::assert_ok!({
        struct Data {}
        struct Main {
            fn test(given self, x: given Data, y: given Data, d: shared[x] Data) {
                let r: or(shared[x], shared[y]) Data = d^;
                ();
            }
        }
    });
}

/// or(shared[x], shared[y]) <: or(shared[y], shared[z]) ❌
/// Partial overlap: shared[x] has no match in {shared[y], shared[z]}.
#[test]
fn subtype_or_partial_overlap_fails() {
    crate::assert_err!({
        struct Data {}
        struct Main {
            fn test(given self, x: given Data, y: given Data, z: given Data,
                    d: or(shared[x], shared[y]) Data) {
                let r: or(shared[y], shared[z]) Data = d^;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "(shared[place]::P) vs (shared[place]::P)" at (redperms.rs) failed because
          condition evaluted to false: `place_b.is_prefix_of(place_a)`
            place_b = y
            place_a = x

        the rule "(shared[place]::P) vs (shared[place]::P)" at (redperms.rs) failed because
          condition evaluted to false: `place_b.is_prefix_of(place_a)`
            place_b = z
            place_a = x"#]]);
}

/// or(shared[x], shared[y]) <: or(shared[x], shared[y]) ✅
/// Reflexivity: an Or is a subtype of itself.
#[test]
fn subtype_or_reflexive() {
    crate::assert_ok!({
        struct Data {}
        struct Main {
            fn test(given self, x: given Data, y: given Data, d: or(shared[x], shared[y]) Data) {
                let r: or(shared[x], shared[y]) Data = d^;
                ();
            }
        }
    });
}

/// or(![x], ![y]) <: or(![x], ![y], ![z]) ✅
/// Same subset logic works for mut-category Or.
#[test]
fn subtype_or_mut_subset() {
    crate::assert_ok!({
        struct Data {}
        struct Main {
            fn test(given self, x: given Data, y: given Data, z: given Data,
                    d: or(![x], ![y]) Data) {
                let r: or(![x], ![y], ![z]) Data = d^;
                ();
            }
        }
    });
}

/// or(shared[x], shared[y]) <: shared[x, y, z] ✅
/// Or branches are a subset of the multi-place existential branches.
#[test]
fn subtype_or_to_wider_multi_ref() {
    crate::assert_ok!({
        struct Data {}
        struct Main {
            fn test(given self, x: given Data, y: given Data, z: given Data,
                    d: or(shared[x], shared[y]) Data) {
                let r: shared[x, y, z] Data = d^;
                ();
            }
        }
    });
}

/// shared[x, y, z] <: or(shared[x], shared[y]) ❌
/// Multi-place has a branch for z that doesn't match any Or branch.
#[test]
fn subtype_wider_multi_ref_to_or_fails() {
    crate::assert_err!({
        struct Data {}
        struct Main {
            fn test(given self, x: given Data, y: given Data, z: given Data,
                    d: shared[x, y, z] Data) {
                let r: or(shared[x], shared[y]) Data = d^;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "(shared[place]::P) vs (shared[place]::P)" at (redperms.rs) failed because
          condition evaluted to false: `place_b.is_prefix_of(place_a)`
            place_b = x
            place_a = z

        the rule "(shared[place]::P) vs (shared[place]::P)" at (redperms.rs) failed because
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

/// or(shared[d1], shared[d2]) should block giving d1 while result is live.
/// The result borrows from d1 (in one branch), so d1 can't be moved.
#[test]
fn or_ref_blocks_give_d1() {
    crate::assert_err!({
        struct Data {}
        struct Main {
            fn go(given self) {
                let d1 = new Data();
                let d2 = new Data();
                let result: or(shared[d1], shared[d2]) Data = d1.share;
                d1^;
                result^;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
            accessed_place = @ fresh(0)
            shared_place = @ fresh(0)"#]]);
}

/// or(shared[d1], shared[d2]) should block giving d2 while result is live.
#[test]
fn or_ref_blocks_give_d2() {
    crate::assert_err!({
        struct Data {}
        struct Main {
            fn go(given self) {
                let d1 = new Data();
                let d2 = new Data();
                let result: or(shared[d1], shared[d2]) Data = d2.share;
                d2^;
                result^;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
            accessed_place = @ fresh(0)
            shared_place = @ fresh(0)"#]]);
}

/// or(![d1], ![d2]) should block mutating d1 while result is live.
#[test]
fn or_mut_blocks_mut_d1() {
    crate::assert_err!({
        struct Data {
            fn write(![self] self) { (); }
        }
        struct Main {
            fn go(given self) {
                let d1 = new Data();
                let d2 = new Data();
                let result: or(![d1], ![d2]) Data = d1!;
                d1!.write();
                result^;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "lease-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
            accessed_place = d1
            leased_place = d1"#]]);
}

/// or(shared ![d1], shared ![d2]) from sharing through a lease should block
/// mutating d1 while result is live.
#[test]
fn or_shared_mut_blocks_mut_d1() {
    crate::assert_err!({
        struct Data {
            fn write(![self] self) { (); }
        }
        struct Main {
            fn go(given self) {
                let d1 = new Data();
                let d2 = new Data();
                let q: ![d1] Data = d1!;
                let result: or(shared ![d1], shared ![d2]) Data = q.share;
                d1!.write();
                result^;
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
        struct Data {}
        struct Sink {
            fn consume(given self, d: given Data) { (); }
        }
        struct Main {
            fn go(given self) {
                let d1 = new Data();
                let d2 = new Data();
                let result: or(shared[d1], shared[d2]) Data = d1.share;
                result^;
                let sink1 = new Sink();
                sink1^.consume(d1^);
                let sink2 = new Sink();
                sink2^.consume(d2^);
                ();
            }
        }
    });
}

// ---------------------------------------------------------------------------
// Ascription::Ty bug fix
// ---------------------------------------------------------------------------

/// let x: or(given, shared[y]) T = ... — mixed categories in type annotation.
/// Should be rejected by check_type. Currently bypasses check_type (bug).
#[test]
fn ascription_ty_rejects_ill_formed_or() {
    crate::assert_err!({
        struct Data {}
        struct Main {
            fn test(given self, y: given Data) {
                let x: or(given, shared[y]) Data = y^;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "or" at (types.rs) failed because
          ill-formed `or(...)`: branches have mixed permission categories (must all be ^, all mut, or all shared)"#]]);
}
