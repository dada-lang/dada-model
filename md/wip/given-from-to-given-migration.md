# Goal

Track the migration from `given_from[places] T` to `given[places] T`.

This is a separate concern from the broader surface-syntax elaboration work. The `surface-syntax.md` document describes the target surface-language design; this document covers only the spelling change for place-based `given`.

# Design

The intended end state is to remove the `given_from` spelling entirely and use `given` for both forms throughout the language:

- `given T` — the concrete owned-unique permission
- `given[places] T` — a symbolic permission representing ownership transferred out of those specific places

The parser disambiguates by looking ahead for `[`.

This is not just a surface sugar. The old `given_from[...]` spelling should be removed from the language rather than retained as a legacy alias.

# Rollout plan

## Commit 1: parser spike

- [x] Proved out that the parser can distinguish `given` from `given[places]` in a minimal test case.
- Added focused parse coverage for the new `given[places]` spelling, and targeted parser tests passed with both `given` and `given[...]` forms present in `Perm`.

## Commit 2: grammar rename

- [x] Updated the grammar so the language spells the place-based form as `given[places]`.
- [x] Removed `given_from` from `KEYWORDS`; the old spelling is no longer reserved or accepted.
- [x] Updated parser-facing rule names, comments, and diagnostics references in the Rust sources.

## Commit 3: corpus migration

- [x] Rewrote `given_from` occurrences under `src/**/tests/`, `book/`, and docs to `given`.
- [ ] Verify the full test suite is green.

# Open questions

- Resolved: the cleanest parser encoding is to keep both `Perm` variants under the `given` keyword and rely on lookahead for `[` to distinguish `given` from `given[...]`.
- Resolved: this landed as a clean break. There is no temporary compatibility alias for `given_from[...]`.
