# Shared copies and reference modes

This repair adopts final-slot promotion as the design of the current Shared
fragment. It resolves the provisional choice recorded in the earlier
[design context](../adversarial-2026-10-24/design-context.md); that historical
input and its inconclusive review remain unchanged.

The user confirmed the local update explicitly during this repair:

> Yes—promote that field when copied

They then clarified the meaning of the representation:

> References to objects do carry whether they are a shared reference or not;
> the object itself doesn't carry that information. If you reach the object
> through a path of references that are entirely unique, then you know you have
> unique ownership; else, you know it is shared. The system maintains an
> invariant that you never have an object that is reachable through both a
> "shared" path and a unique path.

These are the user's replies in the current chat. The word "promotion" below
means changing a stored reference's mode, never an object-wide ownership flag.
The chapter uses the explicit reference wording to avoid that ambiguity.

The rule is:

- Giving along a wholly unique route moves the final reference and empties its slot.
- Giving along a shared route copies an already-shared final reference.
- If the shared route ends at a unique reference, first promote that stored
  reference to shared, then return a shared copy to the same object.

The fragment's stored-occurrence invariant requires a unique reference to be
the sole incoming owning occurrence of its target. Keeping the final occurrence
unique while adding a shared copy would violate that local condition. Changing
that occurrence's mode makes the new pair compatible without changing any other
reference or object identity. Sharing a container therefore
need not traverse or rewrite its fields: paths through it already have shared
access regardless of the modes stored in those fields.

The path-level requirement is distinct from the local stored-occurrence
condition. `Shared/Liveness:WellFormed.path_mode_exclusive` establishes that
well-formed states cannot resolve an entirely unique path and a shared path to
the same object.
The local condition is a sufficient representation invariant; this record does
not claim it is equivalent to the path-level requirement alone. Nor does it
claim that alternative representations are observationally equivalent or that
the current fragment settles future mutation and borrowing layers.

The published rule, its direct and nested examples, and the preservation theorem
are the evidence to review against this decision. The Given-to-Shared embedding
checks the unchanged unique fragment; it cannot justify the new sharing rule by
itself. A future change to the decision must update the rule and its review inputs.
