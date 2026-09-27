//! ## Giving from alternative origins: every origin must satisfy `mut`
//!
//! The permission `given_from[p1, ..., pn]` satisfies the `mut` predicate only
//! when every possible originating place has a type satisfying `mut`. For the
//! ordinary class used here, this means that every alternative supplies a mutable
//! borrow (a lease), rather than merely permitting some form of mutation.
//!
//! ### A lease is different from a unique owner
//!
//! The current `mut` predicate distinguishes mutable borrowing from unique
//! ownership. A `given Wrapper` permits field assignment but does **not** satisfy
//! `mut`. Therefore, testing `x.value = 42` alone would not establish this property.
//! The tests instead pass `x` to a method requiring `P is mut`, with
//! `P = given_from[d1, d2]`.
//!
//! For `class Wrapper { value: Int; }`:
//!
//! | Origin types | `given_from[d1, d2] is mut`? |
//! | --- | --- |
//! | `mut[source1] Wrapper`, `mut[source2] Wrapper` | Yes |
//! | `mut[source1] Wrapper`, `given Wrapper` (either order) | No |
//! | `mut[source1] Wrapper`, `ref[source2] Wrapper` (either order) | No |
//! | `mut[source1] Wrapper`, `shared Wrapper` (either order) | No |
//! | Any pair with neither origin satisfying `mut` | No |
//!
//! Here `d1` and `d2` are the possible originating places; `source1` and `source2`
//! are independent referents. Giving from an owner does not by itself turn the
//! result into a lease. Likewise, failure to prove `shared` does not prove `mut`.
//!
//! ### Projected origins
//!
//! The obligation concerns the full type of each originating place, including
//! `d1.field` and `d1.inner.field`. A field accessed through a mutable borrow
//! can satisfy `mut`. A unique container may also store a mutable reference in
//! a field; in that case the field's type, not the container's ownership, matters.
//! A projected origin containing a shared reference cannot supply a mutable lease.
//!
//! ### Candidate lemma and evidence
//!
//! For a well-formed environment and a nonempty list of valid places, a derivation
//! of `given_from[p1, ..., pn] is mut` entails a derivation that the type of each
//! `pi` satisfies `mut`. Conversely, those premises suffice through the model's
//! `mv mut` rule. This is a candidate lemma, not a theorem proved by these tests.
//!
//! Four groups cover all pairs of `given`, `mut`, `shared`, and `ref` origins:
//! direct places, fields, nested fields, and permission-parameterized fields stored
//! in unique containers. Every test contains a complete Dada program calling a
//! method with an explicit `P is mut` requirement. Only the `mut`/`mut` pair
//! should compile with that requirement.
//!
//! Each rejecting test first checks that the same program compiles with just
//! `where P is mut` removed. This isolates the requirement from the validity of
//! the signature, projected places, and argument passing. The error snapshot then
//! records the rejection with the requirement present. Referents remain live
//! through the call. These are end-to-end type-checking tests, with no direct
//! calls to predicate-proving functions.
//!
//! This property concerns static predicate classification, not general assignment
//! permission, runtime alias safety, or arbitrary generic predicate assumptions.

mod direct;
mod fields;
mod nested_fields;
mod stored_fields;
