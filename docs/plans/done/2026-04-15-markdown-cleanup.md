# 2026-04-15 Markdown cleanup for lint and style compliance

## Context

`make lint` currently fails on two concrete issues, and several project Markdown files violate your global style rules (em-dashes, underscores-in-prose). Separately, the CI workflow that should run the same lints on every PR is itself broken: every recent run on PR #4 reports `Invalid workflow file: error parsing called workflow`, so markdownlint and cspell never actually execute in CI. PR #4 merged red because `main` has no required status checks.

This plan captures a minimal, targeted cleanup: (1) fix the broken CI reference so future PRs catch what this one missed, (2) fix the current lint failures, then (3) sweep active Markdown files for user-preference violations that tooling doesn't enforce.

Scope excludes `.lake/packages/**` (vendored Mathlib and deps) and `docs/plans/done/**` (historical snapshots; markdownlint already ignores them per `.markdownlint-cli2.jsonc` line 31). `references/shannon1948-transcription.md` and `references/shannon1948-summary.md` are preserved as faithful source material and are not edited for em-dash style.

## What's broken vs. what's off-style

### Blocking `make lint` (must fix)

- `docs/reviews/2026-04-15-test-backfill-test-coverage.md:29` and `:37`: MD032 blanks-around-lists. Each list needs a blank line above and below.
- `cspell`: `shannontest` flagged at `docs/reviews/2026-04-15-test-backfill-test-coverage.md:24:77` and `:51:44`. The token appears inside backticked filenames (`…backfill-shannontest-coverage.md`), so cspell still scans it. Fix by adding `shannontest` to `cspell-words.txt` (sorted insertion). Renaming the done-plan file is out of scope.

### Style violations (user global rule, not tool-enforced)

Em-dashes must be replaced with commas, colons, semicolons, parens, or sentence breaks per `~/.claude/CLAUDE.md`. Active-doc counts confirmed by the Explore sweep:

- `README.md`: 9 em-dashes.
- `docs/plans/todo/2026-04-14-shannon-proofs-roadmap.md`: 23 em-dashes (the active roadmap, highest priority of the plans).
- `AGENTS.md` / `CLAUDE.md` (symlink): 0 em-dashes.
- `CHANGELOG.md`, `CONTRIBUTING.md`, `CODE_OF_CONDUCT.md`, `.github/*.md`: 0 em-dashes.

Done plans (`docs/plans/done/2026-04-14-*.md`) contain em-dashes but are historical snapshots. Per your "single living documents" preference applied in reverse, we leave these alone: they're records of what was written at the time, not living docs.

### CI workflow file is invalid (blocks every PR's text-lint job)

- `.github/workflows/ci.yml:25` pins the reusable workflow to `@2bbea614b90f8b96e991f630276893fcf67aa329`. That value is the **annotated tag object SHA** for `v2.1.3` in `cboone/gh-actions`, not the commit SHA. GitHub Actions' `uses:` with a pinned SHA expects the commit the tag resolves to; feeding it a tag object SHA produces `Invalid workflow file: error parsing called workflow` and the entire run aborts before any job starts.
- Verified via `gh api repos/cboone/gh-actions/git/tags/2bbea614b90f8b96e991f630276893fcf67aa329`: tag object `2bbea614…` points to commit `37896a7915c49270272a637ade714f2fea82655f`.
- The reusable workflow itself at `v2.1.3` is intact and accepts `run-cspell` and `run-prettier`, so no input changes are needed once the ref is corrected.

## Changes

### 1. `.github/workflows/ci.yml`

- Replace the pinned ref on the `markdown` job with the actual commit SHA: `@37896a7915c49270272a637ade714f2fea82655f # v2.1.3`.
- Keep the trailing `# v2.1.3` human-readable comment.
- After merge, confirm the next push triggers a run where the `Text lint / Text lint` job actually executes (not a workflow-file-level failure).

### 2. `docs/reviews/2026-04-15-test-backfill-test-coverage.md`

- Insert blank lines above the two lists reported at lines 29 and 37.
- Re-run `make lint-markdown` to confirm clean.

### 3. `cspell-words.txt`

- Add `shannontest` in sorted order (the existing file is sorted alphabetically).
- Re-run `make lint-spelling` to confirm clean.

### 4. `README.md`

- Replace all 9 em-dashes with comma, colon, or parens depending on clause relationship. Several are attached to bullet-list tail phrases (" — `Shannon/Entropy/…`") and read cleanly as "(`Shannon/Entropy/…`)" or as a following clause on a new sub-bullet.

### 5. `docs/plans/todo/2026-04-14-shannon-proofs-roadmap.md`

- Replace all 23 em-dashes. This is an active planning doc, so style rules apply.

## Out of scope (explicit non-goals)

- Done plans under `docs/plans/done/`: historical, not edited.
- `references/shannon1948-*.md`: source-derived content, preserve as-is.
- `.lake/packages/**`: vendored, never edited here.
- Code-fence language hints: `MD040` is intentionally disabled in `.markdownlint-cli2.jsonc:11` to accommodate Pandoc info strings. No change needed.
- Repo-wide prose rewrites beyond the em-dash sweep.

## Verification

Local:

```bash
make lint          # markdownlint + cspell, both must exit 0
make check         # full pipeline: lint + lean-lint + build + test
```

Spot-check: `grep -n "—" README.md docs/plans/todo/2026-04-14-shannon-proofs-roadmap.md` after edits; expect zero matches.

CI: after pushing the branch that bundles these changes, open the Actions run for that push and confirm the `Text lint / Text lint` job appears and executes (not just the Lean job). Inspect the run via `gh run view <id>` and verify `status=completed, conclusion=success` with a non-empty `jobs` array. Previously the `jobs` array was empty because the workflow file itself failed to parse.

Optional follow-up (not in this plan): once CI is known-green, consider adding branch protection to `main` requiring the `Build, lint, and test (Lean)` and `Text lint / Text lint` checks to pass before merge. Flagging only; needs your call.

## Critical files

- `.github/workflows/ci.yml`
- `docs/reviews/2026-04-15-test-backfill-test-coverage.md`
- `cspell-words.txt`
- `README.md`
- `docs/plans/todo/2026-04-14-shannon-proofs-roadmap.md`
- `.markdownlint-cli2.jsonc` (read-only reference; already correct)
