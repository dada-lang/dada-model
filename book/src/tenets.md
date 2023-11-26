# Dada's design tenets

These are a living set of design tenets, extended as we resolve tradeoffs.

We believe that...

- **Dada's users will write high-scale, efficient programs**, thus we ensure that Dada is **expressive and performant**. Dada is not for small scripts where performance doesn't matter. It's meant for efficient, real-world programs.
- **Dada's users care most about their domain and less about machine details**, and thus we ensure Dada is **high-level**. It should feel as much as possible like Java, JavaScript, Kotlin, or other high-level languages that largely hide machine details from their users. We assume a minal
- **Dada's users want to interoperate with other languages**, and thus we ensure Dada has **minimal runtime requirements**. We are willing to require libc and a memory allocator, but we cannot assume that Dada owns the entire stack top-to-bottom. Dada must use a standard stack frame format and there may be frames on the stack from other languages that our runtime does not control.

## Why this ordering / examples of tension?

- _Expressive and performant_ over _high-level_ -- we distinguish _boxed_ values from regular values, which is a case of showing machine details that we'd rather not show. But it's important because avoiding the need to allocate on every value is critical for performanmce. Also
