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

Prove out that the parser can distinguish `given` from `given[places]` in a minimal test case.

## Commit 2: grammar rename

- Update the grammar so the language spells the place-based form as `given[places]`.
- Rename the corresponding core syntax to match.
- Update any error messages mentioning the old keyword.

## Commit 3: corpus migration

- Rewrite `given_from` occurrences under `src/**/tests/`, `book/`, and docs to `given`.
- Verify the full test suite is green.

# Open questions

- What is the cleanest parser encoding for `given` versus `given[...]` in formality-core?
- Do we want a temporary migration period with tailored diagnostics for old `given_from[...]` syntax, or should the rename land as a clean break?
