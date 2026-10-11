//! ## Giving from alternative origins: every origin must satisfy `move`
//!
//! `^[p1, ..., pn]` satisfies `move` only when every possible originating
//! place has a type satisfying `move`. One move-only alternative cannot establish
//! the predicate for a value whose actual origin could instead be shared.
//!
//! For an ordinary non-shared `Wrapper`, with reference origins borrowing from
//! uniquely owned `source1` and `source2`:
//!
//! | Origin types | `^[d1, d2] is move`? |
//! | --- | --- |
//! | Any pair of `^ Wrapper` and `![source] Wrapper` | Yes |
//! | Any pair containing `shared Wrapper` or `shared[source] Wrapper` | No |
//!
//! Here `move` is the predicate, not the ability to write `.give`: shared values
//! also support `.give`, which can duplicate them. A `^`/`mut` pair satisfies
//! `move` without satisfying either `owned` or `mut` uniformly. Failure to prove
//! `shared` alone does not prove `move` for alternative origins.
//!
//! ### Projected origins
//!
//! The same requirement applies to full place types such as `d1.field` and
//! `d1.inner.field`, including permissions inherited from their containers and
//! permissions stored on fields. A unique container can still contain a shared
//! field, which prevents an all-move classification when it is an origin.
//!
//! ### Candidate lemma and evidence
//!
//! For a well-formed environment and nonempty list of valid places, the `mv move`
//! rule proves `^[p1, ..., pn] is move` from the move predicate on every
//! place's type. The `mut => move` implication is compatible with this obligation:
//! establishing a mutable lease still requires the relevant origins to qualify.
//! This candidate statement has not been proved as a theorem.
//!
//! Tests call a method requiring `P is move` in complete Dada programs. All direct
//! pairs of ^/mut/shared/ref origins are covered, with selected contrasting
//! pairs in both orders for fields, nested fields, and stored-field permissions.
//! Every negative program first compiles with only that requirement removed.
//! These tests establish examples of static classification, not a universal
//! complement relation between `move` and `shared`, or runtime move correctness.

mod direct;
mod fields;
mod nested_fields;
mod stored_fields;
