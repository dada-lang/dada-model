formality_core friction

* [x] had to add anyhow, tracing as public dependencies
* [x] defining a custom fold for `Ty` is annoying, it'd be nice if I could do `#[term(no_fold)]` or something like that
    * also it'd be nice if there were a shorthand -- e.g., maybe just add a `#[substitute]` attribute or something
* [x] Variable should implement `parse`, no reason not to