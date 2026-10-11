# Returning values from calls

A method can return ownership directly with `-> ^ Data`, including by giving
one of its ^ parameters. Its return permission can also name its receiver
or parameters. For example, `^[x]` describes a value ^ from parameter
`x`, while `shared[x]` describes a shared borrow of it. At a call site, the checker
resolves these permissions before removing the temporary bindings used for the
arguments.

The following properties describe separate cases of that process. Each property
has its own test module; `call_returns` groups them without asserting a broader
soundness theorem. Here, "remains borrowed" means that a live returned value
continues to restrict conflicting accesses to its referents in the caller.

{{property call_returns::ownership_can_escape}}

{{property call_returns::borrows_of_consumed_arguments_cannot_escape}}

{{property call_returns::forwarded_borrows_keep_referents_borrowed}}

{{property call_returns::all_possible_return_referents_remain_borrowed}}

## Static and runtime evidence

These properties use complete programs to check acceptance and rejection.
Accepted programs also run through the interpreter with output, result, and heap
snapshots. Rejected programs use checker-error snapshots; they are not executed.
The separate [runtime normalization module](https://github.com/dada-lang/dada-model/blob/main/src/core/interpreter/tests/normalization.rs)
contains direct frame tests that inspect the returned value's type and verify
that method bindings do not leak into the caller. Those tests check their class
declarations but evaluate the individual calls directly, without type-checking
them. The same module also has two end-to-end examples that type-check and run
complete programs, covering an owned field returned to a borrowed caller and
nested calls forwarding a borrow. The direct frame assertions and the end-to-end
examples provide different kinds of evidence.

The static result accounts for all possibilities in a return signature. The
interpreter's result type describes the value actually returned. Keeping these
observations separate helps distinguish conservative borrowing restrictions
from the runtime choice of referent.
