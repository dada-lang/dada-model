//! Related properties of values returned by calls.
//!
//! Each child module states its own property and evidence. This module groups
//! those claims rather than asserting one general call-soundness property.
//! The end-to-end checker tests originated in `type_system::tests::normalization`.
//! Accepted programs also execute with output, result, and heap snapshots;
//! rejecting programs retain checker-error snapshots.
//!
//! The interpreter's `tests::normalization` module remains separate: its direct
//! frame tests inspect runtime result types and caller bindings, but do not
//! type-check the individual call expressions. That runtime module also has two
//! end-to-end examples that type-check and execute their programs. The local tests in
//! `type_system::pop_normalize` exercise normalization internals and guard links.

mod all_possible_return_referents_remain_borrowed;
mod borrows_of_consumed_arguments_cannot_escape;
mod forwarded_borrows_keep_referents_borrowed;
mod ownership_can_escape;
