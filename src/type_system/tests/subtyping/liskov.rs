//! ## Liskov Substitution Principle (LSP)
//!
//! The "Liskov Substitution Principle" is that if T1 <: T2, then a value of type T1 can be
//! substituted for a value of type T2 and nothing can go wrong. This module aims to systematically
//! explore the various substitution considerations relevant to Dada:
//!
//! * [Compatible layout](`compatible_layout`): the most basic is that the layout of the data structure in memory must be compatible.
//!   This is affected by the permisssion since `leased` structures are represented by pointers but everything
//!   else is by-value.
//! * [Permission](`subpermission`): All operations permitted by supertype must be permitted by the subtype (relevant when a value with
//!   this type is live)
//!   * This begins with edits on the data structure itself, so `our Foo` cannot be a subtype of `my Foo`
//!     since the latter permits field mutation.
//!   * This also includes restrictions on what can be done in the environment. So `shared{d1} Foo` cannot
//!     be a subtype of `shared{d2} Foo` since the latter permits `d1` to be modified but the subtype does not.
//!     (The latter also restricts edits to `d2`, but that's ok in the supertype, it can be more restrictive.)
//! * [Liveness and cancellation](`cancellation`)
//!   * When variables are dead, subtyping allows for *cancellation*, so e.g. if `d1` is dead,
//!     then `shared{d1} leased{d2} Foo` is a subtype of `leased{d2} Foo`.

mod cancellation;
mod compatible_layout;
mod subpermission;
