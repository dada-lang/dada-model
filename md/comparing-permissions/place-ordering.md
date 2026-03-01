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

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Data {
            left: given Data;
            right: given Data;
        }

        class Main {
            fn test(given self, d: given Data) {
                let r: ref[d] Data = d.left.ref;
                ();
            }
        }
    }
);
```

The expression `d.left.ref` has type `ref[d.left] Data`,
but the annotation on `r` expects `ref[d] Data`.
This works because `d` is a **prefix** of `d.left` --
a reference that borrows from `d.left`
certainly borrows from somewhere within `d`.

The same principle applies to mutable leases:

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Data {
            left: given Data;
            right: given Data;
        }

        class Main {
            fn test(given self, d: given Data) {
                let r: mut[d] Data = d.left.mut;
                ();
            }
        }
    }
);
```

`mut[d.left] <: mut[d]` --
a lease of a field is a subtype of a lease of the parent.

### The reverse fails

Going the other direction doesn't work.
A borrow from all of `d` can't promise
it only borrows from `d.left`:

```rust
# extern crate dada_model;
dada_model::assert_err_str!(
    {
        class Data {
            left: given Data;
            right: given Data;
        }

        class Main {
            fn test(given self, d: given Data) {
                let r: ref[d.left] Data = d.ref;
                ();
            }
        }
    },
    r#"predicates.rs"#,
);
```

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

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Data { }

        class Main {
            fn test(given self, d1: given Data, d2: given Data) {
                let r: ref[d1, d2] Data = d1.ref;
                ();
            }
        }
    }
);
```

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

```rust
# extern crate dada_model;
dada_model::assert_err_str!(
    {
        class Data { }

        class Main {
            fn test(given self, d1: given Data, d2: given Data) {
                let r: ref[d1, d2] Data = d1.ref;
                let s: ref[d1] Data = r.give;
                ();
            }
        }
    },
    r#"predicates.rs"#,
);
```

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

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Data {
            left: given Data;
            right: given Data;
        }

        class Main {
            fn test(given self, d: given Data) {
                let r: ref[d.left, d.right] Data = d.left.ref;
                let s: ref[d] Data = r.give;
                ();
            }
        }
    }
);
```

`ref[d.left, d.right] <: ref[d]` --
both `d.left` and `d.right` are sub-places of `d`,
so both chains satisfy the prefix check.

The same holds for leases:

```rust
# extern crate dada_model;
dada_model::assert_ok!(
    {
        class Data {
            left: given Data;
            right: given Data;
        }

        class Main {
            fn test(given self, d: given Data) {
                let r: mut[d.left, d.right] Data = d.left.mut;
                let s: mut[d] Data = r.give;
                ();
            }
        }
    }
);
```

`mut[d.left, d.right] <: mut[d]` works by the same logic.
