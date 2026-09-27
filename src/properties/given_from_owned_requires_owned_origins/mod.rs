//! ## Giving from alternative origins: ownership requires owned origins
//!
//! `given_from[p1, ..., pn]` satisfies `owned` when every possible originating
//! place has an owned type. An owned shared value qualifies just as a unique owner
//! does; a borrowed alternative cannot be ignored merely because another origin
//! is owned.
//!
//! For an ordinary non-shared `Wrapper`, with borrowed origins referring to
//! uniquely owned `source1` and `source2`:
//!
//! | Origin types | `given_from[d1, d2] is owned`? |
//! | --- | --- |
//! | Any pair of `given Wrapper` and `shared Wrapper` | Yes |
//! | Any pair containing `ref[source] Wrapper` or `mut[source] Wrapper` | No |
//!
//! Consequently, `given`/`shared` alternatives can be owned even though they are
//! neither uniformly shared nor uniformly move-only. Ownership, duplication, and
//! the `mut` predicate describe different capabilities.
//!
//! ### The complete place type matters
//!
//! Origins may be fields, nested fields, or fields storing references inside
//! unique containers. The ownership of the container alone does not prove that
//! its stored reference is owned. The table assumes genuinely borrowed references:
//! the model can treat a reference to an owned shared value as owned, because
//! that shared ownership is retained. Reference syntax alone does not decide this
//! predicate.
//!
//! ### Candidate lemma and evidence
//!
//! For a well-formed environment and nonempty list of valid places, the `mv owned`
//! rule proves `given_from[p1, ..., pn] is owned` from ownership of each place's
//! type. Conversely, such a derivation through that rule requires every premise.
//! This is a candidate lemma, not a proof of preservation during execution.
//!
//! Tests use complete Dada programs calling a method requiring `P is owned`.
//! All concrete given/shared/ref/mut pairs are checked for direct origins; selected
//! contrasting pairs in both orders cover fields, nested fields, and stored-field
//! permissions. Every negative program compiles when only its owned requirement
//! is removed. The class is ordinary and non-generic, avoiding independently shared
//! value types such as `Int` as the result. Generic assumptions and runtime cleanup
//! are outside this evidence.

mod direct;
mod fields;
mod nested_fields;
mod stored_fields;
