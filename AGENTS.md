# AGENTS.md

This file provides guidance to AI coding agents when working with code in this repository.

## Project Overview

A Lean 4 formalization of Shannon's 1948 finite-alphabet entropy characterization theorem (Appendix 2). Fork of [SamuelSchlesinger/shannon-1948-formalization](https://github.com/SamuelSchlesinger/shannon-1948-formalization), maintained independently by Christopher Boone. Selected improvements are pushed upstream via pull requests.

## Fork Relationship

- **Origin:** `cboone/shannon-entropy` (this repo)
- **Upstream:** `SamuelSchlesinger/shannon-1948-formalization`
- **Vendored in:** the `strength-model` repo at `proofs/Shannon/`
- Changes flow: this repo to upstream (via PRs), this repo to strength-model (via vendoring)
- When modifying code here, consider whether the change is suitable for an upstream PR

## Build Commands

```bash
bin/bootstrap-worktree            # mandatory first-time setup (lake update + cache + build)
make bootstrap                    # same as bin/bootstrap-worktree
lake build Shannon                # build just the Shannon library
lake build Book                   # build the Verso companion book sources
lake build Shannon.Entropy.Core   # build a single module
lake test                         # run the ShannonTest example suite
lake lint                         # run batteries/runLinter over the Shannon library
make build                        # lake build Shannon (guards against missing Mathlib cache)
make book                         # render the companion book into `_site/html-multi/`
make serve                        # build and serve the companion book locally
make test                         # lake test
make lean-lint                    # lake lint
make check                        # markdown + spelling + lean-lint + build + test
```

CI: `.github/workflows/ci.yml` runs three jobs: a Lean job (build, lint, test via `leanprover/lean-action@v1`), a Markdown/spelling job (markdownlint-cli2 + cspell), and a book job that builds `Book` and renders `_site/`.

Lean toolchain: see `lean-toolchain` (currently v4.29.0).
Mathlib version: see `lakefile.toml` (pinned to v4.29.0).

Prefer `lake build <Module.Name>` over `lake env lean path/to/File.lean` for normal verification.

## Fresh Clone / Worktree Bootstrap

In a fresh clone or worktree, run:

```bash
bin/bootstrap-worktree
```

This is mandatory in every fresh clone or worktree. The script runs `lake update`,
`lake exe cache get`, verifies that Mathlib's prebuilt artifacts exist, and only
then runs `lake build Shannon` and `lake build Book`. Never bootstrap by running `lake build` directly
in a clean worktree or clone. Mathlib must always come from downloaded prebuilt
artifacts, not a local source compilation.

The `make build` target also guards against this: it checks for Mathlib artifacts
and refuses to proceed if they are missing, directing you to run `make bootstrap`
or `bin/bootstrap-worktree` first.

## Module Layout

- `Shannon.lean` -- project entrypoint (re-exports `Shannon.Entropy`)
- `Book.lean` -- root Manual document for the companion book
- `Main.lean` -- Verso executable entrypoint for rendering the companion book
- `Book/` -- companion-book chapters written in the Verso Manual genre
- `Shannon/Entropy.lean` -- facade import for all entropy modules
- `Shannon/Entropy/Core.lean` -- foundations: probability distributions, axiom bundle, core constructions
- `Shannon/Entropy/Uniform.lean` -- phase 1: equiprobable characterization
- `Shannon/Entropy/Rational.lean` -- phase 2: rational case via grouped equiprobable refinement
- `Shannon/Entropy/Approx.lean` -- phase 3: floor-count rational approximants and convergence lemmas
- `Shannon/Entropy/Final.lean` -- final uniqueness theorems (`entropyNat_unique`, `entropyBase_unique`)
- `Shannon/Entropy/Gibbs.lean` -- Gibbs inequality, negMulLog bridge, entropy nonnegativity
- `Shannon/Entropy/Joint.lean` -- joint distributions, marginals, conditional entropy, chain rule
- `Shannon/Entropy/Properties.lean` -- Section 6: deterministic iff, uniform iff, subadditivity, Schur-concavity
- `Shannon/Entropy/Converse.lean` -- converse: `entropyNat` satisfies the Shannon axioms
- `Shannon/Entropy/Bits.lean` -- base-2 public API (`entropyBits`, base-2 uniqueness bridge)

`entropyBits` is the primary public entropy API from Phase C onward; `entropyNat` remains the internal natural-log workhorse used throughout the Appendix 2 characterization proof.

### Book Import Discipline

Chapters under `Book/` must not `import Shannon` (or any `Shannon.*` module) directly. Lake links every transitive C object on the `generate-book` argv, and pulling Mathlib through `Shannon` pushes the macOS link command past `ARG_MAX` (~1 MB). Chapters that need to render Lean code should use `subverso` highlight artifacts instead of a direct import.

## Lean Conventions

- Tab size: 2 spaces (no hard tabs)
- No format-on-save (VS Code setting in `.vscode/settings.json`)
- Unicode: standard Lean 4 unicode symbols
- Follow existing proof style in this repo
- Final newline in all files; trim trailing whitespace

### Skill and Workflow

Invoke the `write-lean-code` skill before any Lean edit, read-for-review, or planning discussion. The skill carries generic Lean/Mathlib guidance; user-level overrides (no line-length limit, no hardwrapping in comments or docstrings) are documented in `~/.claude/CLAUDE.md`. This file (`AGENTS.md`, symlinked as `CLAUDE.md`) is authoritative for shannon-entropy-specific facts: bootstrap script, build targets, module layout, test-mirroring rule, namespace conventions.

### Namespace Conventions

Everything in this library lives under the `Shannon.Entropy.*` module hierarchy with flat per-file namespaces; there is no second-tier nesting by topic. New files go under `Shannon/Entropy/` unless a distinct concern justifies a new top-level `Shannon/<Area>/` tree.

### Vendored Lean Dependencies

None beyond Mathlib. This library is itself the one that strength-model vendors; it does not vendor any third-party Lean code of its own. When grepping for style examples or API confirmation, all of `Shannon/`, `ShannonTest/`, and Mathlib under `.lake/packages/mathlib/` are valid; there is no third-party Lean package to exclude.

## Linting and Testing

```bash
make lint              # markdownlint + cspell
make lint-markdown     # markdownlint only
make lint-spelling     # cspell only
make lean-lint         # lake lint (batteries/runLinter over the Shannon library)
make book              # render the companion book HTML
make serve             # serve the rendered companion book locally
make test              # lake test (run the ShannonTest example suite)
make check             # full pipeline: lint + lean-lint + build + test
```

When adding domain-specific terms (author names, Lean identifiers, math vocabulary), add them to `cspell-words.txt`.

The `ShannonTest/` library mirrors the Shannon library's public API with `example`-based tests. When adding, renaming, or removing public definitions or theorems, update the corresponding test file in the same change so `lake test` continues to pass.

## Key Files

- `lakefile.toml` -- Lake project config (library name, Mathlib dependency)
- `lean-toolchain` -- pinned Lean version
- `Makefile` -- build and lint targets
- `references/shannon1948.pdf` -- reference copy of Shannon's 1948 paper
