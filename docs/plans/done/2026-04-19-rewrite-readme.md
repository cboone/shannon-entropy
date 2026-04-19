# 2026-04-19 Rewrite README for the current project state

## Context

The current `README.md` is broadly accurate, but it still reads mostly like a theorem inventory for the Appendix 2 characterization proof. Since that structure was written, the repo has gained several things that materially change what a newcomer needs to see first: the Verso companion book, the `entropyBits` base-2 public API, explicit bootstrap-first build rules, the `NOTICE` and SPDX-backed license split, and an active roadmap that extends beyond the already-complete characterization theorem.

The active roadmap in `docs/plans/todo/2026-04-14-shannon-proofs-roadmap.md` makes the project's broader goal explicit: keep the completed Appendix 2 and Section 6 formalization, then extend the fork toward Shannon's Theorems 3 through 7 for finite-state sources, with the companion book growing in parallel. The README should reflect that real status clearly without turning into a duplicate of the roadmap.

The SPDX and bibliography workstream explicitly left `README.md` alone because it was expected to be rewritten separately. This plan is that rewrite.

## Goals

1. Reframe the README as the repository homepage, not just a theorem checklist.
2. State the current project status clearly:
   - Already formalized: Appendix 2 characterization, converse, Section 6 properties, base-2 API, companion book.
   - Planned next: Shannon Theorems 3 through 7 and the finite-state-source development described in the roadmap.
   - Explicit non-goal: full coverage of the entire 1948 paper, especially the continuous / differential-entropy side.
3. Preserve the important durable sections the user called out:
   - the top `NOTE`
   - the `AI Statement`
   - the `License` section
4. Keep the build story correct and prominent, especially the requirement to run `bin/bootstrap-worktree` first in a fresh clone or worktree.
5. Make the repo's main reader paths easier to understand: code, public API, tests, and companion book.
6. Reduce churn-prone detail in the main body so the README stays accurate longer between rewrites.

## Rewrite strategy

Keep the README as a concise orientation document. Push long enumerations and phase-by-phase future work back to the roadmap and the code itself.

Concretely:

- Keep a short mathematical statement of the main result, but do not let the opening screen be dominated by theorem bullets.
- Replace the current long theorem and module dump with a tighter status-first narrative.
- Keep a curated list of the most important exported results and entrypoints, not every notable theorem currently in the repo.
- Keep the companion book visible as a first-class project surface, not an afterthought.
- Preserve licensing and provenance detail near the end, where readers expect it.

## Proposed README outline

### 1. Title and top note

- Keep the current title unless a clearer one emerges during drafting.
- Keep the top `NOTE` block at the top of the file.
- Allow only light editing to the note if needed to align with the roadmap's wording about expanding the formalization beyond Appendix 2.

### 2. Opening overview

- One short paragraph explaining that this is a Lean 4 formalization of Shannon's finite-alphabet entropy theory from the 1948 paper, starting with Appendix 2 and Section 6.
- One short paragraph explaining the current fork status: Appendix 2 and Section 6 are done, the companion book is live, and Theorems 3 through 7 remain planned work.

### 3. Project status

Add a compact status section with three subsections or grouped bullet lists:

- `Done today`
  - Appendix 2 uniqueness theorem
  - Converse showing `entropyNat` satisfies the Shannon axioms
  - Section 6 properties already formalized
  - `entropyBits` as the primary base-2 public API
  - companion book infrastructure and current chapters
- `Planned next`
  - roadmap phases for AEP, typical sets, finite-state sources, and Shannon Theorems 3 through 7
- `Out of scope`
  - continuous / differential entropy, channel capacity, and the noisy-channel coding theorem unless the roadmap changes later

This section should replace the current need for readers to infer scope from scattered sections.

### 4. Repo surfaces

Add a short section that explains the role of each major surface:

- `Shannon/`: Lean library
- `ShannonTest/`: `example`-based API regression tests
- `Book/`, `Book.lean`, `Main.lean`: Verso companion book
- `references/`: study materials and the bundled Shannon paper

This can absorb most of the current `Module Layout` detail, while still linking readers to the important files.

### 5. Main entrypoints and representative results

Keep a compact list of the main things a reader will actually look for:

- `Shannon.lean` and `Shannon/Entropy.lean`
- `entropyBits` in `Shannon/Entropy/Bits.lean`
- `entropyNat_unique` and `entropyBase_unique` in `Shannon/Entropy/Final.lean`
- representative Section 6 and chain-rule results

Do not try to preserve the full current theorem inventory verbatim. That level of detail is useful in module files and tests, but it makes the README harder to scan and easier to age badly.

### 6. Reading paths

Replace `How To Read The Proof` with a more reader-oriented section that offers three paths:

- `Proof path`: `Core -> Uniform -> Rational -> Approx -> Final`
- `API path`: `Bits -> Joint -> Properties -> Converse`
- `Book path`: start with the companion book chapters if the reader wants exposition first

This keeps the good part of the current reading-order guidance, but makes it easier for different readers to choose a route.

### 7. Build and verification

Rewrite the build section so it leads with the bootstrap rule and mirrors the actual project commands:

```bash
bin/bootstrap-worktree
lake build Shannon
lake build Book
lake test
lake lint
make check
make book
make serve
```

Requirements to keep explicit:

- `bin/bootstrap-worktree` is mandatory in a fresh clone or worktree.
- `make build` and `make book` assume Mathlib artifacts are already bootstrapped.
- `lake build Book` is a compile-only check for the companion book.

### 8. Companion book

Keep a dedicated companion-book section, but tighten it:

- what it is
- how to build and preview it
- the current chapter set in one sentence
- the `Book/` import discipline in one short note, since that constraint is operationally important on macOS

### 9. Formalization notes

Either keep a small note about the explicit relabel-invariance axiom, or fold it into another short section if it still helps explain the proof style. This should stay only if it earns the space.

### 10. AI statement

- Preserve the `AI Statement` section.
- Update names or versions only if the current text is known to be stale at rewrite time.

### 11. Reference

- Keep the Shannon 1948 citation.
- Keep the mention that `references/shannon1948.pdf` is bundled for study context.

### 12. License and provenance

- Preserve the `License` section.
- Keep the fork relationship and split-license explanation.
- Cross-check the wording against `NOTICE`, `LICENSES/`, and current SPDX policy so the README summary stays accurate.

## Specific changes to make during the rewrite

1. Replace the current opening theorem block with a shorter project-level overview plus status summary.
2. Compress `Main Theorems` into a curated list of anchor results.
3. Compress `Module Layout` into repo-surface and entrypoint sections.
4. Convert `How To Read The Proof` into `Reading paths`.
5. Expand `Build and Verify` just enough to cover bootstrap, build, lint, test, and book workflows.
6. Keep `Companion Book`, but shorten the prose and keep the operationally important `Book` import constraint.
7. Preserve the `AI Statement`, `Reference`, and `License` sections near the end.

## Important content to preserve

These elements should survive the rewrite verbatim or very close to verbatim unless there is a concrete accuracy reason to adjust them:

- the top `NOTE`
- the `AI Statement`
- the `License` section's fork-and-split-license explanation
- the reference to `references/shannon1948.pdf`
- the statement that `entropyBits` is the primary public entropy API

## Non-goals

- Do not turn the README into a full roadmap mirror.
- Do not keep a theorem-by-theorem catalogue if it makes the page harder to maintain.
- Do not duplicate contributor-process material that belongs in `AGENTS.md`, `CONTRIBUTING.md`, or plan docs.
- Do not change Lean code, tests, or book chapters as part of the README-only rewrite.

## Verification

After the README rewrite lands, verify:

1. The top `NOTE`, `AI Statement`, and `License` sections are still present.
2. The scope statements match `docs/plans/todo/2026-04-14-shannon-proofs-roadmap.md`.
3. The build commands match `Makefile`, `AGENTS.md`, and `.github/workflows/ci.yml`.
4. The companion-book description matches the actual `Book/` surface and `_site/html-multi/` output.
5. The licensing summary still matches `NOTICE` and `LICENSES/`.
6. `make lint-markdown` passes.

## Critical files

- `README.md`
- `docs/plans/todo/2026-04-14-shannon-proofs-roadmap.md`
- `AGENTS.md`
- `Makefile`
- `.github/workflows/ci.yml`
- `NOTICE`
- `LICENSES/Apache-2.0.txt`
- `LICENSES/MIT.txt`
- `LICENSES/CC-BY-4.0.txt`
- `docs/references.bib`
