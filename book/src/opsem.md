# Operational semantics

For now, just some notes on how we expect Dada to be implemented.

- Dada objects may be heap or stack allocated
  - Eventually we will require `box class` to force a layer of indirection.
- All Dada objects will have a header with a reference count. Typically 1.
- Leased values are a pointer.
- Shared values are a copy of the object.
