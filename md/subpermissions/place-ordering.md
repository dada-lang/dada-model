# Place ordering

Permissions in Dada carry **places** --
they record *where* a borrow or lease comes from.
These places create a natural ordering on permissions:
more specific places are subtypes of less specific ones.

There are two dimensions to this ordering:
**sub-places** (field projections) and **place sets** (multiple sources).

## Sub-place ordering

A borrow from a field is more specific
than a borrow from the whole object.
If you borrow `d.left`,
that's a tighter restriction than borrowing all of `d`:

{anchor}`place_ordering_ref_subplace`

The expression `d.left.ref` has type `ref[d.left] Data`,
but the annotation on `r` expects `ref[d] Data`.
This works because `d` is a **prefix** of `d.left` --
a reference that borrows from `d.left`
certainly borrows from somewhere within `d`.

The same principle applies to mutable leases:

{anchor}`place_ordering_mut_subplace`

`mut[d.left] <: mut[d]` --
a lease of a field is a subtype of a lease of the parent.

### The reverse fails

Going the other direction doesn't work.
A borrow from all of `d` can't promise
it only borrows from `d.left`:

{anchor}`place_ordering_reverse_fails`

`ref[d] </: ref[d.left]` --
`d.left` is not a prefix of `d`,
so the prefix check fails.

### The rule

The chain comparison rule that handles sub-places is:

{judgment-rule}`red_chain_sub_chain, (ref::P) vs (ref::P)`

It requires `place_b.is_prefix_of(&place_a)` --
the supertype's place must be a prefix of (or equal to)
the subtype's place.
There's an analogous rule for `mut`:

{judgment-rule}`red_chain_sub_chain, (mut::P) vs (mut::P)`

## Place sets

Permissions can mention multiple places.
`ref[d1, d2]` means "a reference that may borrow from `d1` or `d2`" --
which means both `d1` and `d2` must be kept unmodified.

A permission that restricts fewer places
is a subtype of one that restricts more:

{anchor}`place_ordering_set_subset`

`ref[d1] <: ref[d1, d2]` --
the subtype restricts `d1`;
the supertype restricts both `d1` and `d2`.
The supertype is *more* restrictive,
so it's safe to use the subtype in its place.

This might feel backwards at first,
but think about it from the caller's perspective:
if you hold a `ref[d1, d2] Data`,
you know not to modify `d1` *or* `d2`.
If the actual value only borrows from `d1`,
that's fine -- you're being *extra* careful
by also avoiding modifications to `d2`.

### Dropping a source fails

The reverse doesn't work --
you can't narrow a multi-source reference
to a single source:

{anchor}`place_ordering_dropping_source_fails`

`ref[d1, d2] </: ref[d1]` --
the value might borrow from `d2`,
and the target type doesn't protect `d2` from modification.

### How place sets work in the rules

Internally, a permission like `ref[d1, d2]`
is represented as a `RedPerm` with multiple chains --
one chain `Rfl(d1)` and another chain `Rfl(d2)`.
For the subtype to hold,
*every* chain in the subtype
must match *some* chain in the supertype.

When checking `ref[d1] <: ref[d1, d2]`:
the subtype has one chain `Rfl(d1)`.
The supertype has two chains: `Rfl(d1)` and `Rfl(d2)`.
The single chain matches `Rfl(d1)` in the supertype. Done.

When checking `ref[d1, d2] <: ref[d1]`:
the subtype has two chains: `Rfl(d1)` and `Rfl(d2)`.
`Rfl(d1)` matches, but `Rfl(d2)` has no match in the supertype.
The check fails.

## Combining both dimensions

Sub-places and place sets compose naturally.
Here's a case that uses both:

{anchor}`place_ordering_both_dimensions`

`ref[d.left, d.right] <: ref[d]` --
both `d.left` and `d.right` are sub-places of `d`,
so both chains satisfy the prefix check.

The same holds for leases:

{anchor}`place_ordering_both_dimensions_mut`

`mut[d.left, d.right] <: mut[d]` works by the same logic.
