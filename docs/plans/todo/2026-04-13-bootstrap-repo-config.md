# Bootstrap Repo Config

## Context

This repo is a fork of SamuelSchlesinger/shannon-1948-formalization. The user is
maintaining it independently and pushing selected changes upstream. The repo
currently has minimal config (just `/.lake` in .gitignore, a bare AGENTS.md, and
CI). The goal is to bring it up to the user's personal standards by adapting
config patterns from `~/Development/strength-model`, which has a mature Lean 4
project under `proofs/` with extensive tooling.

## Files to Create or Modify

### 1. `AGENTS.md` (rewrite in place)

Replace the upstream author's content with full project conventions (build
commands, module layout, fork relationship, Lean conventions, linting). This
becomes the primary config file.

Key sections:

- Project overview (Shannon entropy formalization, fork of SamuelSchlesinger)
- Fork relationship (origin, upstream, vendored in strength-model)
- Build commands (`lake build`, `lake build Shannon`, module-level builds)
- Fresh clone/worktree bootstrap (`lake update`, `lake exe cache get`, then build)
- Module layout (from README)
- Lean conventions (2-space indent, no format-on-save, Unicode, proof style)
- Linting commands (`make lint`, `make check`, cspell-words.txt)
- Key files reference

Source: written fresh for this project, not copied from strength-model.

### 2. `CLAUDE.md` (new, symlink)

Create as a symlink to `AGENTS.md`:

```
CLAUDE.md -> AGENTS.md
```

### 3. `.gitignore` (expand existing)

Add standard entries beyond the current `/.lake`:

```gitignore
# Lean / Lake build artifacts
/.lake

# OS artifacts
.DS_Store

# Editor state
*.swp
*.swo
*~
```

No Python entries (not relevant to this repo).

Source: adapted from strength-model, trimmed to Lean-only.

### 4. `.ignore` (new)

Ripgrep/fd ignore for the massive `.lake/` directory:

```
# Lake build artifacts (Mathlib oleans, etc.)
.lake
```

### 5. `.vscode/settings.json` (new)

Take `[lean4]` and `[lean]` blocks verbatim from strength-model. Add a minimal
`[markdown]` block. Add `markdownlint.run: "onSave"`. No MPE/Pandoc/pandocciter
settings.

Source: `/Users/ctm/Development/strength-model/.vscode/settings.json` (lean4,
lean, and markdown sections only).

### 6. `.vscode/extensions.json` (new)

Recommend `leanprover.lean4` and `DavidAnson.vscode-markdownlint` only.

Source: adapted from strength-model, dropping paper-related extensions.

### 7. `.markdownlint-cli2.jsonc` (new)

Same rule config as strength-model (Pandoc accommodations: MD013 off, MD033 off,
MD041 off, MD040 off, MD024 siblings-only, MD025 off, MD026 trailing-colon OK,
MD010 tabs-in-code OK, MD060 off). Simplified ignores: just `.lake/**` and
`docs/plans/done/**`.

Source: `/Users/ctm/Development/strength-model/.markdownlint-cli2.jsonc` (rules
verbatim, ignores adapted).

### 8. `cspell.jsonc` (new)

Same structure as strength-model but with only `.lake/**` in ignorePaths. Keep
math/LaTeX regex ignores. Drop Pandoc citation regexes.

Source: `/Users/ctm/Development/strength-model/cspell.jsonc` (structure, adapted).

### 9. `cspell-words.txt` (new)

Seed by running `cspell --no-progress "**/*.md"` against the repo and capturing
legitimate flagged terms. Expected terms: Lean/Mathlib identifiers, author names,
math vocabulary.

### 10. `Makefile` (new)

Simple targets:

- `build`: `lake build Shannon`
- `build-all`: `lake build`
- `lint`: `lint-markdown` + `lint-spelling`
- `lint-markdown`: `markdownlint-cli2 "**/*.md"`
- `lint-spelling`: `cspell --no-progress "**/*.md"`
- `check`: lint then build
- `clean`: `lake clean`
- `help`: self-documenting grep

Source: adapted from strength-model's Makefile pattern, Lean-only targets.

### 11. `.workmux.yml` (new)

Two-pane layout:

```yaml
panes:
  - command: claude --dangerously-skip-permissions --enable-auto-mode
    focus: true
  - split: vertical
    percentage: 50
    command: echo "Run: lake update && lake exe cache get && lake build Shannon"
```

Source: adapted from strength-model's `.workmux.yml`.

## Files to Leave Alone

- `README.md`, `LICENSE`, `shannon1948.pdf`
- `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`
- `.github/workflows/lean_action_ci.yml`
- All `Shannon/` source files

## Execution Order

1. `.gitignore` (edit existing)
2. `.ignore` (new)
3. `.vscode/settings.json` + `.vscode/extensions.json` (new directory + files)
4. `.markdownlint-cli2.jsonc` (new)
5. `cspell-words.txt` (new, seeded from linter run)
6. `cspell.jsonc` (new, references cspell-words.txt)
7. `Makefile` (new)
8. `.workmux.yml` (new)
9. `AGENTS.md` (rewrite)
10. `CLAUDE.md` (symlink to AGENTS.md)

## Verification

1. `make lint` passes (markdownlint + cspell clean)
2. `make build` passes (lake build Shannon succeeds)
3. `make check` passes (lint + build together)
4. `ls -la CLAUDE.md` confirms symlink to AGENTS.md
5. Open repo in VS Code, confirm Lean 4 settings apply
