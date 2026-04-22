---
applyTo: "**/*.lean"
---

# Copilot Review Instructions for Lean 4

## Tactics

- **`rw` closes reflexive goals automatically.** In Lean 4, the `rw` tactic ends with an implicit `rfl` attempt: if the goal becomes syntactically reflexive after rewriting, `rw` closes it with no trailing `rfl`, `simp`, `simpa`, or `ring` needed. Do not flag Lean tactic proofs ending in `rw [...]` as incomplete merely because the last step is a rewrite. The same applies to `rewrite` (which does not auto-close) only when used explicitly. For `simp_rw`, the trailing-reflexivity behavior matches `rw`.
- **`simpa` and `exact` close goals.** Proofs that end in `simpa [...] using ...` or `exact ...` are complete; do not suggest adding further closing tactics.

## Linters

- **`@[nolint unusedArguments]` is the Mathlib-canonical way to silence the unused-argument linter** on a definition. The `_`-prefix binder convention (`_hq : P`) does not silence Mathlib's `unusedArguments` linter for `def`s; it only suppresses Lean core's unused-variable warnings. Either keep `@[nolint unusedArguments]` or consume the hypothesis with `have _ := h` inside the body. Do not suggest `_`-prefix renames as a drop-in replacement for `@[nolint unusedArguments]` on definitions.

## Style

- **Single-line docstrings and comments.** This project lets the editor handle visual wrapping; docstrings and comments are single long lines per paragraph. Do not flag Lean comment or docstring paragraphs for exceeding ~100 characters.
