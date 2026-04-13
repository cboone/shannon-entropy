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
lake build Shannon.Entropy.Core   # build a single module
lake test                         # run the ShannonTest example suite
lake lint                         # run batteries/runLinter over the Shannon library
make build                        # lake build Shannon (guards against missing Mathlib cache)
make test                         # lake test
make lean-lint                    # lake lint
make check                        # markdown + spelling + lean-lint + build + test
```

CI: `.github/workflows/ci.yml` runs two parallel jobs: a Lean job (build, lint, test via `leanprover/lean-action@v1`) and a Markdown/spelling job (markdownlint-cli2 + cspell).

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
then runs `lake build Shannon`. Never bootstrap by running `lake build` directly
in a clean worktree or clone. Mathlib must always come from downloaded prebuilt
artifacts, not a local source compilation.

The `make build` target also guards against this: it checks for Mathlib artifacts
and refuses to proceed if they are missing, directing you to run `make bootstrap`
or `bin/bootstrap-worktree` first.

## Module Layout

- `Shannon.lean` -- project entrypoint (re-exports `Shannon.Entropy`)
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

## Lean Conventions

- Tab size: 2 spaces (no hard tabs)
- No format-on-save (VS Code setting in `.vscode/settings.json`)
- Unicode: standard Lean 4 unicode symbols
- Follow existing proof style in this repo
- Final newline in all files; trim trailing whitespace

## Linting and Testing

```bash
make lint              # markdownlint + cspell
make lint-markdown     # markdownlint only
make lint-spelling     # cspell only
make lean-lint         # lake lint (batteries/runLinter over the Shannon library)
make test              # lake test (run the ShannonTest example suite)
make check             # full pipeline: lint + lean-lint + build + test
```

When adding domain-specific terms (author names, Lean identifiers, math vocabulary), add them to `cspell-words.txt`.

The `ShannonTest/` library mirrors the Shannon library's public API with `example`-based tests. When adding, renaming, or removing public definitions or theorems, update the corresponding test file in the same change so `lake test` continues to pass.

## Key Files

- `lakefile.toml` -- Lake project config (library name, Mathlib dependency)
- `lean-toolchain` -- pinned Lean version
- `Makefile` -- build and lint targets
- `shannon1948.pdf` -- reference copy of Shannon's 1948 paper
