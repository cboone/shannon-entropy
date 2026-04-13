# Bootstrap Project

## Context

Continuing the repo bootstrap work. The previous batch of commits added editor
config, linting, Makefile, bootstrap script, AGENTS.md/CLAUDE.md, and reference
docs. This plan covers the remaining scaffolding gaps: repo boilerplate,
community files, CI expansion (Lean lint/test, markdown/spell checking), and a
test library.

## Execution Plan

### 1. scaffold-new-repo (scoped down)

Only the files not already present:

- `CHANGELOG.md` (from scaffold-new-repo template)
- `.github/copilot-instructions.md` (cross-references AGENTS.md)
- `docs/plans/todo/.gitkeep` and `docs/plans/done/.gitkeep`

Already present (skip): LICENSE, README.md, AGENTS.md, CLAUDE.md, .gitignore,
docs/plans/ directories.

Skipped per user: `.claude/settings.json`, secret scanning.

### 2. add-community-files

Run the add-community-files skill to add:

- `CONTRIBUTING.md`
- `CODE_OF_CONDUCT.md`
- `.github/SECURITY.md`
- `.github/PULL_REQUEST_TEMPLATE.md`

### 3. Enable `lake lint` (batteries lintDriver)

The lakefile.toml currently only requires `mathlib` (which transitively pulls in
batteries). To use `lake lint`:

- Add an explicit `batteries` dependency in `lakefile.toml`
- Set `lintDriver = "batteries/runLinter"` in the package section

Files to modify:

- `lakefile.toml`

After enabling, run `lake lint` locally. If it flags issues, either fix them or
create an initial `nolints.json` (by running `lake lint -- --update`).

### 4. Scaffold ShannonTest library

Create a test library following the strength-model pattern
(`StrengthModelTest/` mirrors `StrengthModel/` one-to-one with `example` proofs).

Files to create:

- `ShannonTest.lean` (entrypoint, imports all test modules)
- `ShannonTest/Entropy.lean` (facade import for test modules)
- `ShannonTest/Entropy/Core.lean` (smoke tests for core definitions)
- `ShannonTest/Entropy/Properties.lean` (tests exercising Section 6 properties)
- `ShannonTest/Entropy/Final.lean` (tests exercising uniqueness theorems)

Add to `lakefile.toml`:

- New `[[lean_lib]]` entry for `ShannonTest`
- Set `testDriver = "ShannonTest"`

Test content: `example` statements that exercise the public API, e.g.:

- `entropyNat` of a uniform distribution equals `log n`
- `entropyNat_eq_zero_iff` for a deterministic distribution
- Chain rule applied to a product distribution
- Converse: `entropyNat_shannonAxioms` type-checks

Source for patterns:
`/Users/ctm/Development/strength-model/proofs/StrengthModelTest/Entropy.lean`

### 5. Expand CI workflow

Replace the minimal `lean_action_ci.yml` with a comprehensive workflow:

**Lean job** (runs on ubuntu-latest):

- `actions/checkout@v5`
- `leanprover/lean-action@v1` (builds Shannon)
- `lake lint` step
- `lake test` step

**Lint job** (runs on ubuntu-latest, parallel with Lean job):

- `actions/checkout@v5`
- Install Node.js (for markdownlint-cli2 and cspell)
- `npx markdownlint-cli2 "**/*.md"`
- `npx cspell --no-progress "**/*.md"`

Files to modify:

- `.github/workflows/lean_action_ci.yml`

### 6. Update Makefile and AGENTS.md

Add new Makefile targets:

- `lean-lint`: `lake lint`
- `test`: `lake test`

Update `check` to include `lean-lint` and `test`.

Update AGENTS.md to document `lake lint`, `lake test`, and the ShannonTest
library.

### Commit Strategy

1. `chore: add changelog, copilot config, and .gitkeep files`
2. `docs: add community files` (from add-community-files skill)
3. `build: enable lake lint via batteries lintDriver`
4. `test: scaffold ShannonTest library`
5. `ci: expand workflow with lint, test, and markdown checks`
6. `build: add lean-lint and test Makefile targets`

## Verification

- `make lint` passes (markdownlint + cspell)
- `lake lint` passes (or produces a clean nolints.json)
- `lake test` passes (ShannonTest examples all type-check)
- `make check` passes (full lint + build pipeline)
- CI workflow YAML is valid
