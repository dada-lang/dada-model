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
    }, expect_test::expect![[r#"placeholder"#]]);
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
    }, expect_test::expect![[r#"placeholder"#]]);
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
    }, expect_test::expect![[r#"placeholder"#]]);
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
    }, expect_test::expect![[r#"placeholder"#]]);
}

// ---------------------------------------------------------------------------
// Predicates: for-all semantics
// ---------------------------------------------------------------------------

/// or(ref[x], shared) is copy ✅ — both branches are copy
#[test]
fn predicate_or_copy_both_copy() {
    crate::assert_ok!({
        class Data {}
        class Main {
            fn test(given self, x: given Data, d: or(ref[x], shared) Data) {
                let a = d.give;
                let b = d.give;
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
            fn test(given self, x: given Data, y: given Data, d: or(mut[x], mut[y]) Data) {
                let a = d.give;
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
            fn test(given self, x: given Data, y: given Data, d: or(mut[x], mut[y]) Data) {
                let a = d.give;
                let b = d.give;
                ();
            }
        }
    }, expect_test::expect![[r#"placeholder"#]]);
}

/// or(given, given) is given ✅ — both branches are given
/// Test by passing to a function that requires `is given`.
#[test]
fn predicate_or_given_both_given() {
    crate::assert_ok!({
        class Data {}
        class Main {
            fn needs_given[perm P](given self, d: P Data) -> P Data
                where P is given,
            {
                d.give;
            }
            fn test(given self, d: or(given, given) Data) {
                let r = self.ref.needs_given(d.give);
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
            fn needs_owned[perm P](given self, d: P Data) -> P Data
                where P is owned,
            {
                d.give;
            }
            fn test(given self, d: or(given, given) Data) {
                let r = self.ref.needs_owned(d.give);
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
            fn test(given self, d: or(given, given) Data) {
                let a = d.give;
                let b = d.give;
                ();
            }
        }
    }, expect_test::expect![[r#"placeholder"#]]);
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
    }, expect_test::expect![[r#"placeholder"#]]);
}

// ---------------------------------------------------------------------------
// Ascription::Ty bug fix: check_type on let-binding type annotations
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
    }, expect_test::expect![[r#"placeholder"#]]);
}
