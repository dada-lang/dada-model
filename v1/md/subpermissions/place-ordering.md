# Place ordering

Permissions in Dada carry **places** --
they record *where* sharing or a mutable lease originates.
These places create a natural ordering on permissions:
more specific places are subtypes of less specific ones.

There are two dimensions to this ordering:
**sub-places** (field projections) and **place sets** (multiple sources).

## Sub-place ordering

Sharing a field restricts a smaller place than sharing the whole object.
Sharing `d.left` leaves more of `d` available for other accesses:

{anchor}`place_ordering_ref_subplace`

The expression `d.left.share` has type `shared[d.left] Data`,
but the annotation on `r` expects `shared[d] Data`.
This works because `d` is a **prefix** of `d.left` --
a value shared from `d.left` depends on a place within `d`.

The same principle applies to mutable leases:

{anchor}`place_ordering_mut_subplace`

`![d.left] <: ![d]` --
a lease of a field is a subtype of a lease of the parent.

### The reverse fails

Going the other direction doesn't work.
Sharing all of `d` cannot promise a dependency only on `d.left`:

{anchor}`place_ordering_reverse_fails`

`shared[d] </: shared[d.left]` --
`d.left` is not a prefix of `d`,
so the prefix check fails.

### The rule

The chain comparison rule that handles sub-places is:

{judgment-rule}`red_chain_sub_chain, (shared[place]::P) vs (shared[place]::P)`

It requires `place_b.is_prefix_of(&place_a)` --
the supertype's place must be a prefix of (or equal to)
the subtype's place.
There's an analogous rule for `mut`:

{judgment-rule}`red_chain_sub_chain, (mut::P) vs (mut::P)`

## Place sets

Permissions can mention multiple places.
`shared[d1, d2]` means "a value shared from `d1` or `d2`" --
which means both `d1` and `d2` must be kept unmodified.

A permission that restricts fewer places
is a subtype of one that restricts more:

{anchor}`place_ordering_set_subset`

`shared[d1] <: shared[d1, d2]` --
the subtype restricts `d1`;
the supertype restricts both `d1` and `d2`.
The supertype is *more* restrictive,
so it's safe to use the subtype in its place.

This might feel backwards at first,
but think about it from the caller's perspective:
if you hold a `shared[d1, d2] Data`,
you know not to modify `d1` *or* `d2`.
If the actual value only depends on `d1`,
that's fine -- you're being *extra* careful
by also avoiding modifications to `d2`.

### Dropping a source fails

The reverse doesn't work --
you cannot discard a possible sharing origin:

{anchor}`place_ordering_dropping_source_fails`

`shared[d1, d2] </: shared[d1]` --
the value might depend on `d2`,
and the target type doesn't protect `d2` from modification.

### How place sets work in the rules

Internally, a permission like `shared[d1, d2]`
is represented as a `RedPerm` with multiple chains --
one chain `ShareLive(d1)` and another chain `ShareLive(d2)`.
For the subtype to hold,
*every* chain in the subtype
must match *some* chain in the supertype.

When checking `shared[d1] <: shared[d1, d2]`:
the subtype has one chain `ShareLive(d1)`.
The supertype has two chains: `ShareLive(d1)` and `ShareLive(d2)`.
The single chain matches `ShareLive(d1)` in the supertype. Done.

When checking `shared[d1, d2] <: shared[d1]`:
the subtype has two chains: `ShareLive(d1)` and `ShareLive(d2)`.
`ShareLive(d1)` matches, but `ShareLive(d2)` has no match in the supertype.
The check fails.

## Combining both dimensions

Sub-places and place sets compose naturally.
Here's a case that uses both:

{anchor}`place_ordering_both_dimensions`

`shared[d.left, d.right] <: shared[d]` --
both `d.left` and `d.right` are sub-places of `d`,
so both chains satisfy the prefix check.

The same holds for leases:

{anchor}`place_ordering_both_dimensions_mut`

`![d.left, d.right] <: ![d]` works by the same logic.
