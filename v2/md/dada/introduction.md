# About Dada

Dada explores a permission-based approach to ownership. Programs can give values,
share access, and create leases. These operations describe relationships among
objects and references, including who keeps an object alive and which accesses
can disrupt other references.

A central goal is to support a **Java-like mental model with a Rust-like execution
model**. A programmer can think about objects and their relationships while an
implementation uses ownership, inline storage, and explicit lifetime management.
The object picture should not require every object to occupy its own allocation.

This book is developing a semantic account of that design. It starts with an
abstract machine rather than a full language tutorial. The machine's four
reference kinds are explanatory vocabulary; they are not all intended to appear
as first-class concepts in Dada source syntax. In particular, `shlease` names a shared lease and `showned` names shared ownership in the operational model.

The [design goals](tenets.md) explain the language goals motivating the model.
The [heap chapters](../heap.md) explore how to make those goals precise.
