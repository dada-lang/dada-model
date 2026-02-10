# Dada Formal Model

This book documents the formal model for the [Dada](https://dada-lang.org/) programming language. The model is implemented using [formality-core](https://rust-lang.github.io/a-mir-formality/formality_core.html) and defines Dada's type system, including its permission-based ownership model.

The code examples in this book are executable tests -- they are compiled and checked as part of the build. For example, here is a simple Dada program that type-checks successfully:

```rust
# extern crate dada_model;
# dada_model::assert_ok!("
class Foo {
    i: Int;
}

class Main {
    fn test(given self) -> Int {
        let foo = new Foo(22);
        foo.i.give;
    }
}
# ");
```
