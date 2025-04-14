# Notes

Misc notes and observations we have to place somewhere better eventually.

## Objects versus values, pondering on identity

I have been debating for some time whether to divide _classes_ from _value types_.
I've come to the conclusion that we should.

When to use which one:

- Classes are for values that have _individual identity_:
  - In some cases, like `Vec`, this identity arises from _tracking resources_ (memory) that must be disposed of.
  - But it can also arise from domain reasons -- e.g., you might have a `class Shape` representing shapes in a drawing that were created by the user and which are hence distinct objects to them.

Classes...

- Have permissions
- Support mutation of individual fields
- Permit atomic fields (if boxed)

Values...

- Are always created atomically
- Do not have their own permissions
- Do not support mutation of individual fields or atomic fields

## Boxing

Classes and values are typically represented "inline". This implies that...

- They cannot be cyclic
- They cannot have atomic fields
- Data shared/leased from their fields is invalidated when they are moved

...but they can also be declared as _boxed_. If so, they are represented by a pointer, and we allocate them on the heap. In that case...

- They can be cyclic
- They can have atomic fields
- Data shared/leased from their fields is preserved when they are moved

...definitely tempting to say "classes are always boxed, values are only boxed if they participate in a cycle" or something like that.

## Memory layout

Both classes and boxes can be declared as _boxed_. A boxed value is represented by a pointer. Otherwise,

- Owned: always a copy of the struct or (if boxed) pointer
- Rf: as owned
- Mt: always a pointer to some other location

One trick is the subtyping below. We do need to track whether this is a my/our value or a shared copy whose ref count is maintained elsewhere.

To track that:

- For boxed values: set the
- For inline values: overwrite the ref count field with

## Owned as a subtype of shared, the need to drop shared

I am pondering the `given() <: shared(_)` relation. It's very powerful.
It does imply that dropping (and copying!) a shared thing is never free,
you have to at least check for the need to bump a reference count.

We want to allow `shared() <: shared(a)` too, so that implies that `shared(a)`
has to check for reference count drops anyway.
