# Dada types and permissions

A Dada type has the following grammar

```rust
// Types:
{{#include ../../src/grammar.rs:Ty}}

// Permissions:
{{#include ../../src/grammar.rs:Perm}}
```

Notes:

```
Ty = Struct
   | Class
   | Var
   | Perm Ty

Perm =
```

canonical form

```
TyC = Perm (Struct | Class | Var)

PermC = shared(places)? leased(places)* (my | Var)
```
