# Subtypes and subpermissions

In the [previous chapter](./subtyping.md),
we saw how subtyping works:
the type checker reduces permissions to `RedPerm`s
(sets of `RedChain`s)
and then compares them chain by chain.

This chapter dives into the `red_chain_sub_chain` judgment --
the rules that determine whether one chain
can stand in for another.

The topics:

- [**Place ordering**](./subpermissions/place-ordering.md) --
  how sub-places and place sets create a partial order on permissions.
- [**Copy permissions**](./subpermissions/copy-permissions.md) --
  the three copy permissions (`shared`, `ref[d]`, `shared mut[d]`),
  how they relate, and how they compose.
- [**Liveness and cancellation**](./subpermissions/liveness.md) --
  how dead links are resolved during comparison.
