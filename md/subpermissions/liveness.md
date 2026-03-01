# Liveness and cancellation

*This chapter is a work in progress.*

In the previous sub-chapters,
we saw how permissions are compared structurally --
place ordering and the copy permission hierarchy.
But those rules assume all borrowed places are still alive.

What happens when a borrowed place is **dead** --
no longer used by later code?

Dead links in a `RedChain` can be **cancelled** or **promoted**,
which enables subtyping relationships
that wouldn't hold for live links.
This is Dada's equivalent of Rust's non-lexical lifetimes (NLL) --
borrows end when the reference is last used,
not when it goes out of scope.
