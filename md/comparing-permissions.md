# Comparing Permissions

In the [previous chapter](./subtyping.md),
we saw that subtyping in Dada is fundamentally about permissions.
Two types are related only when they name the same class --
the interesting question is whether one permission
can stand in for another.

We covered the basics:
`shared <: ref[d]` because owning a shared copy
is at least as good as borrowing,
and `ref[d1] <: ref[d1, d2]` because borrowing from fewer places
is more specific.
But we left the full picture of permission comparison
as a black box.

This chapter opens that box.
We'll work through the structural rules
that govern how permissions relate to each other --
the rules that don't require knowing
whether a variable is still alive or dead.
(Liveness enters the picture in a later chapter.)

The topics:

- [**Place ordering**](./comparing-permissions/place-ordering.md) --
  how sub-places and place sets create a partial order on permissions.
- [**Copy permissions**](./comparing-permissions/copy-permissions.md) --
  the three copy permissions (`shared`, `ref[d]`, `shared mut[d]`),
  how they relate, and how they compose.
