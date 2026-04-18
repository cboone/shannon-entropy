## Branch Review: docs/implement-phase-a-verso

Base: main (merge base: `ae68ffdb`)
Commits: 7
Files changed: 18 (6 added, 12 modified, 0 deleted, 0 renamed)
Reviewed through: `d081bdb`

### Summary

Implements Phase A of the Shannon proofs roadmap: a Verso Manual-genre companion book, `Shannon 1948: A Formalization Companion`, scaffolded in-repo as a `Book` lean_lib plus `generate-book` lean_exe pinned to Verso `v4.29.0`. Phase A content is deliberately narrow (Introduction + Bibliography) to prove the pipeline. The branch also carries a late-breaking revision to the Phase A plan itself (d877edb) that discarded a fabricated build pipeline in favor of the real reference-manual pattern before the scaffold was written.

### Changes by Area

#### Build and tooling

- `lakefile.toml`: adds Verso `v4.29.0` `[[require]]`, `Book` lean_lib, `generate-book` lean_exe with `root = "Main"`.
- `lake-manifest.json`: pulls in Verso, MD4Lean, subverso as transitive deps.
- `Makefile`: new `book` and `serve` targets; book target guards on Verso bootstrap; serve target runs `uv run python -m http.server` against `_site/html-multi`.
- `bin/bootstrap-worktree`: adds step `[5/5] Building Book library`.
- `.gitignore`: ignores `/_site`.
- `cspell.jsonc` / `cspell-words.txt`: `_site/**` ignored; new vocabulary (Verso, VersoManual, manualMain, subverso, Leanc, olean, MacKay, versowebcomponents).

#### CI

- `.github/workflows/ci.yml`: adds a `book` job `needs: lean` that runs `lake build Book` and then renders via `lake exe generate-book --depth 2 --output _site`, uploading `_site/html-multi` as an artifact.

#### Book sources (new)

- `Main.lean`: executable entry via `manualMain (%doc Book)` with `sourceLink`/`issueLink` pointing at this repo; suppresses `emitTeX` and `emitHtmlSingle`.
- `Book.lean`: root Manual document, includes Introduction and Bibliography at depth 0.
- `Book/Introduction.lean`: paper overview, fork relationship, current completed scope, reading order, bootstrap/build commands.
- `Book/Bibliography.lean`: Shannon 1948 with DOI, Cover and Thomas, MacKay.

#### Tests

- `ShannonTest/Book.lean`: one-line import smoke test.
- `ShannonTest.lean`: adds `import ShannonTest.Book`.

#### Documentation

- `AGENTS.md`: module layout lists `Book.lean`, `Main.lean`, `Book/`; new "Book Import Discipline" subsection documents the `import Shannon` prohibition; `make book`/`make serve` added to command tables.
- `README.md`: replaces bare `lake build` with full bootstrap-and-build recipe; adds a "Companion Book" section; corrects the stale CI workflow filename reference.
- `docs/plans/todo/2026-04-14-shannon-proofs-roadmap.md`: d877edb rewrote Phase A to match the reference-manual pattern before any code was scaffolded.

### File Inventory

- **New (6):** `Main.lean`, `Book.lean`, `Book/Introduction.lean`, `Book/Bibliography.lean`, `ShannonTest/Book.lean`, `docs/reviews/2026-04-18-docs-implement-phase-a-verso.md`
- **Modified (12):** `.github/workflows/ci.yml`, `.gitignore`, `AGENTS.md`, `Makefile`, `README.md`, `ShannonTest.lean`, `bin/bootstrap-worktree`, `cspell-words.txt`, `cspell.jsonc`, `docs/plans/todo/2026-04-14-shannon-proofs-roadmap.md`, `lake-manifest.json`, `lakefile.toml`
- **Deleted:** none
- **Renamed:** none

### Notable Changes

- **New external dependency**: Verso at `v4.29.0`, pulling in MD4Lean and subverso transitively. Pinning is tag-stable since Verso cuts a tag per Lean release.
- **New Lake targets**: `lean_lib Book` and `lean_exe generate-book`.
- **New build/CI surface**: `make book`, `make serve`, and a third CI job.
- **New invariant** (AGENTS.md + commit message): chapters under `Book/` must not `import Shannon` or `Shannon.*` because Lake puts every transitive C object on `generate-book`'s link argv, which blows past macOS `ARG_MAX` (~1 MB). Future cross-references will use subverso highlight artifacts. This is called out as a repo-wide convention, not just a local workaround.

### Plan Compliance

**Verdict: Good compliance.** All seven numbered tasks in Phase A are implemented end to end, the Phase A smoke-check from the Verification section is wired up (Introduction + Bibliography both appear in the rendered `_site/html-multi/` tree observed locally), and the documented deviations from the plan are either forced by a real platform constraint or aligned with user-global tooling preferences.

**Overall progress: 7/7 tasks fully done. All listed sub-bullets accounted for.**

#### Done

- **Task 1 (Verso dependency)**: `lakefile.toml` pins `verso` at `v4.29.0` with the one-line compatibility comment the plan asked for; `lake-manifest.json` records the resolved revision `7ae82ac2...`.
- **Task 2 (Scaffold)**: lean_lib and lean_exe are present; `Main.lean` and `Book.lean` follow the reference-manual pattern exactly; per-chapter modules live under `Book/`. `moreLeancArgs = ["-O0"]` is set at the package level in `lakefile.toml` per the plan (added in `ea95fb4`).
- **Task 3 (Initial chapters)**: `Book/Introduction.lean` covers paper overview, fork relationship, scope (Appendix 2 + Section 6 Properties 1-6 done, Theorems 3-7 planned), reading order, and bootstrap/build invocations. `Book/Bibliography.lean` lists Shannon 1948 with DOI and both supporting references.
- **Task 4 (Build targets)**: `Makefile` adds `book` (with the Verso-artifact guard the plan specified) and `serve`; `bin/bootstrap-worktree` adds `[5/5] Building Book library`; README documents both targets.
- **Task 5 (CI)**: `.github/workflows/ci.yml` appends a `book` job with `needs: lean` that runs `lake build Book` and then `lake exe generate-book`, and uploads the artifact (explicit build step added in `de7e5dd`).
- **Task 6 (Testing)**: `ShannonTest/Book.lean` adds the one-line `example` import smoke test; `cspell-words.txt` gains the Verso vocabulary the plan mentioned plus a few adjacent terms the scaffolding surfaced (`Leanc`, `olean`, `subverso`, `VersoManual`, `MacKay`).
- **Task 7 (Documentation)**: AGENTS.md (the canonical source; `CLAUDE.md` is a symlink) gets an updated module layout and a new "Book Import Discipline" subsection; README gets a "Companion Book" section.

#### Not started

- None.

#### Deviations

1. **Book chapters must not import Shannon** (new invariant not in the plan). The plan's Task 2 says "The `Book` library depends transitively on `Shannon` so chapters can `import Shannon.Entropy.*` modules and reference their definitions in prose." The implementation does the opposite and prohibits this. **Assessment: reasonable and necessary.** The commit message documents the `ARG_MAX` failure mode on macOS concretely, the constraint is recorded in AGENTS.md and README.md (not just the commit), and a future-compatible cross-referencing path (subverso highlight artifacts) is named. The deviation should land in the plan document itself when it graduates from `todo/` so Phases B+ do not re-trip the same wire.
2. **`make serve` uses `uv run python -m http.server`** instead of `python3` as the plan's sample Makefile snippet shows. **Assessment: reasonable.** Aligns with the user's global preference in `~/.claude/CLAUDE.md` ("Use `uv` to run Python scripts. Never use `python3` or `pip` directly.").
3. **Output path shape**: plan's sample expected tree names `_site/index.html` and `_site/book/`; the actual Verso output is `_site/html-multi/index.html`. Makefile, README, and CI all consistently use `_site/html-multi`. **Assessment: the plan was inaccurate; implementation matches Verso's real layout.**
4. **CI artifact path** is `_site/html-multi` rather than the plan's `_site/`. **Assessment: correct adjustment to actual Verso layout.**

#### Fidelity concerns

- The scope shrinkage on Task 3 (Foundations moved to Phase B) is written into the plan itself in d877edb and is fine.
- The Introduction chapter points readers at `references/shannon1948-transcription.md`. The file exists on `main` (committed alongside `references/shannon1948.pdf` and `references/shannon1948-summary.md`), so the cross-reference resolves.

### Code Quality Assessment

**Overall: ready to merge.** The scaffolding is small, internally consistent, and faithful to the reference-manual pattern it claims to follow. The ARG_MAX workaround is documented in the right places. Prose in the two chapters is accurate and appropriately minimal for a pipeline-proving Phase A. The `-O0`, explicit CI build step, and `htmlSplit` items flagged during the initial review pass all shipped in follow-up commits (`ea95fb4`, `de7e5dd`, `173091b`).

#### Strengths

- **Convention lands in three places, not one.** The `import Shannon` prohibition is in the commit message, AGENTS.md "Book Import Discipline" subsection, and README's Companion Book section. That makes the invariant durable without relying on lore.
- **Bootstrap path stays mandatory.** `bin/bootstrap-worktree` now builds Book; `Makefile book` target early-exits if `VersoManual.olean` is not present with a clear pointer back to bootstrap. This matches the existing strict-bootstrap discipline AGENTS.md already documents for Mathlib.
- **Scope discipline.** Foundations chapter explicitly deferred to Phase B to avoid splitting axiomatic content across phases; Phase A ships the narrowest possible book that is still a real Manual. Avoids the common trap of over-scaffolding.
- **Test coverage is proportionate.** `ShannonTest/Book.lean` is the smallest thing that exercises the Book namespace via the normal `lake test` path; no pretend-thorough tests that would rot.
- **Commits are well-shaped.** d877edb (plan revision) is separated from 7cf5f0c (scaffold) so the plan-vs-code distinction stays legible in history.
- **`Main.lean` config is explicit.** `emitTeX := false` and `emitHtmlSingle := .no` are set explicitly rather than relying on defaults; this will prevent accidental format drift if Verso upstream changes defaults.
- **Verso pin comment** in `lakefile.toml` includes the "why" (verified compatible with Mathlib v4.29.0 via `lake update`) rather than just a version.

#### Issues to address

None open. The items raised in the initial review pass were all addressed before merge:

1. ~~**Missing `moreLeancArgs = ["-O0"]`**~~: added at the package level in `lakefile.toml` by `ea95fb4`.
2. ~~**Introduction chapter's forward reference** to `references/shannon1948-transcription.md`~~: verified present on `main` alongside `references/shannon1948.pdf`, so the cross-reference resolves.

#### Suggestions (non-blocking)

- ~~**CI**: add an explicit `lake build Book` step before `lake exe generate-book` in the book job.~~ Shipped in `de7e5dd`.
- ~~**`htmlSplit := .never`** on the Introduction chapter~~: dropped in `173091b`; Verso's default applies uniformly across both chapters.
- **Plan graduation**: after this merges, the plan document should move from `docs/plans/todo/` to `docs/plans/done/` (matching existing projects' convention in this repo) or the plan should be updated in-place to mark Phase A complete and codify the `import Shannon` prohibition for Phases B+. The Phase A status line was updated in `759e72b`; the directory move remains.
