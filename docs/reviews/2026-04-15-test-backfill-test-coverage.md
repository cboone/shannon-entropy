## Branch Review: test/backfill-test-coverage

Base: main (merge base: 2312e6d)
Commits: 1 committed + working-tree changes (the core backfill is uncommitted)
Files changed: 9 (6 added, 3 modified, 0 deleted, 0 renamed)
Reviewed through: e33a679 + uncommitted working tree

### Summary

This branch backfills the `ShannonTest/` mirror with six new smoke-test modules (Uniform, Rational, Approx, Joint, Gibbs, Converse), wires them into the `ShannonTest.Entropy` aggregator, trims the now-redundant converse example from `ShannonTest/Entropy/Final.lean`, and extends `cspell-words.txt` with the vocabulary introduced by the new tests and recent plan docs. The single committed change on the branch so far is a polish pass on the plan document itself; all test code is staged in the working tree awaiting commit.

### Changes by Area

**Tests (new smoke-coverage modules)**
Six new `example`-based test files covering the headline results and a handful of cheap supporting lemmas per library module. Files: `ShannonTest/Entropy/{Uniform,Rational,Approx,Joint,Gibbs,Converse}.lean`.

**Test aggregator / existing tests**
`ShannonTest/Entropy.lean` gains six `import` lines so `lake test` picks the new modules up. `ShannonTest/Entropy/Final.lean` drops its `Shannon.Entropy.Converse` import and the `entropyNat_shannonAxioms` example, now that `ShannonTest/Entropy/Converse.lean` owns that assertion; its module docstring is retitled accordingly.

**Spelling dictionary**
`cspell-words.txt` grows by 30 entries (sorted in-place alongside existing terms). Additions split roughly into Lean/Mathlib identifiers used by the new tests (`Fintype`, `Finset`, `Tendsto`, `tendsto`, `simpa`, `symm`, `logb`, `rpow`, `hsupp`, `nonneg`, `pointwise`), math vocabulary from plan docs and roadmap (`Brouwer`, `Chebyshev`, `Fano`, `Frobenius`, `memoryless`, `agnostically`, `degenericize`, `Degenericize`, `degenericized`), and tooling/writing terms (`cleveref`, `docstrings`, `frontmatter`, `hardwrap`, `hardwrapped`, `hardwrapping`, `latexmk`, `natbib`, `nocite`, `tikz`, `worktrees`).

**Docs**
The committed commit `e33a679` refines `docs/plans/todo/2026-04-14-backfill-shannontest-coverage.md`: 35/34 line churn, no behavior change.

### File Inventory

New (6):
- `ShannonTest/Entropy/Approx.lean`
- `ShannonTest/Entropy/Converse.lean`
- `ShannonTest/Entropy/Gibbs.lean`
- `ShannonTest/Entropy/Joint.lean`
- `ShannonTest/Entropy/Rational.lean`
- `ShannonTest/Entropy/Uniform.lean`

Modified (3):
- `ShannonTest/Entropy.lean` (aggregator imports)
- `ShannonTest/Entropy/Final.lean` (trim converse example)
- `cspell-words.txt` (30 new entries)

Deleted: none. Renamed: none.

### Notable Changes

- No library (`Shannon/`) code is touched on this branch, consistent with the plan's explicit out-of-scope note.
- No dependency, toolchain, CI, or lakefile changes.
- `ShannonTest/Entropy/Final.lean`'s public surface shrinks by one `example`; nothing else references the removed assertion because its replacement lives in the new `Converse.lean`.

### Plan Compliance

Plan: `docs/plans/todo/2026-04-14-backfill-shannontest-coverage.md` (auto-detected by branch-name match).

**Verdict:** Strong compliance. Every planned test file exists, every headline result listed in the plan is exercised by a direct `example`, and every "good supporting example" the plan suggested is also present. The plan's "file to simplify" step (`ShannonTest/Entropy/Final.lean` dropping the converse example) is also done. No scope additions, no scope omissions.

**Overall progress:** 6/6 test files complete, 1/1 aggregator update complete, 1/1 `Final.lean` simplification complete. Effectively 100% on plan items, though the work is uncommitted and `lake test` / `make check` have not been run as part of this review, so the "verification" step of the plan is not yet independently confirmed in this session.

**Per-module check:**

- **Converse** (`ShannonTest/Entropy/Converse.lean`): covers `entropyNat_shannonAxioms` (headline), `entropyNat_relabelInvariant`, `entropyNat_uniformMonotone`, `entropyNat_grouping`. All four plan items done. Note: the plan says "Exports 4 public declarations; cover most of it" -- this file covers all four.
- **Gibbs** (`ShannonTest/Entropy/Gibbs.lean`): `gibbs_inequality`, `entropyNat_nonneg`, `entropyNat_le_log_card` (headline), plus `entropyNat_eq_sum_negMulLog` and `entropyNat_uniformPNat`. All five plan items done.
- **Joint** (`ShannonTest/Entropy/Joint.lean`): `chain_rule`, `entropyNat_prodDist`, `marginalFst_prodDist`, `marginalSnd_prodDist` (headline), plus `IsIndependent`, `condEntropy`, and `mutualInfo` on concrete two-point products. All planned items done; the concrete-distribution choice is sensible (`uniformPNat 2 × uniformPNat 1`, whose entropy reduces via `entropyNat_uniformPNat 1 = 0`).
- **Approx** (`ShannonTest/Entropy/Approx.lean`): `tendsto_approxProb`, `approxProb_error_bound`, `entropyNat_approxProb` (headline), plus `approxCount_pos`, `approxTotal_pos`, `approxProb_apply`. All planned items done.
- **Rational** (`ShannonTest/Entropy/Rational.lean`): `entropyNat_of_rational_counts`, `worked_grouping_identity`, `grouping_on_rational_counts` (headline), plus `relabel_compose_rational_eq_uniform` and `workedCompose_masses`. All planned items done.
- **Uniform** (`ShannonTest/Entropy/Uniform.lean`): `Apos_mul`, `Apos_eq_K_mul_log`, `K_pos`, `Apos_pow` (headline), plus `Apos_one_zero`, `Apos_pos_of_one_lt`, `Apos_monotone`, and the optional `Apos_eq_K_mul_logb`. All planned items done, including the "optional" base-parametric variant.

**Deviations:** none substantive. The one stylistic choice worth flagging: the new tests `open Shannon` in every file as called for, but several also use `open Filter` / `open scoped Topology` (Approx) or rely on `Equiv.swap`/`Fintype.equivFinOfCardEq` (Converse, Rational). These are necessary for the referenced library APIs and match the implicit spirit of "add a small extra import only when it keeps the test simple."

**Fidelity concerns:** none. The tests consistently call library declarations rather than reproving anything, match the lightweight docstring style of the existing three test files, and stay well short of "a second proof development."

### Code Quality Assessment

**Overall quality:** The test code itself is ready to merge *once committed and verified by `lake test`*. As a reviewer I would want to see `make check` pass before approving, because several of the new examples use arithmetic or rewriting that could catch on a Mathlib or library-API change that is not obvious from the diff (e.g., the `chain_rule` rewrite chain in `Joint.lean`, the `relabel_compose_rational_eq_uniform` application with `Fintype.equivFinOfCardEq`, or `native_decide` in `Rational.lean`).

**Strengths:**

- The files faithfully mirror the existing test style: single-module `import`, `open Shannon`, one-line module docstring, `example`-only bodies. A future reader will not be able to tell these files were written after the originals.
- Coverage density is well-judged: each file is short enough to read in one screen yet pins both the headline export and enough supporting surface to catch accidental renames of helpers like `approxCount_pos` or `Apos_one_zero`.
- Concrete-distribution choices are cheap and intentional. Using `uniformPNat 1` as the second factor in `Joint.lean` makes `condEntropy` and `mutualInfo` both reduce to zero via `entropyNat_uniformPNat 1 = 0`, which is a nice deterministic smoke test.
- `cspell-words.txt` additions are integrated in the existing sorted list and look correct for the current diff (no obviously stray entries; math names are capitalized, identifiers are not).
- The `Final.lean` simplification is the right follow-through: the plan called for it, and the remaining file is now strictly about uniqueness.

**Issues to address:**

- **Uncommitted work.** The core of the branch is not committed. The plan's execution order suggests per-module commits (`test: add ShannonTest/Entropy/<Module>.lean smoke coverage`) or a single `test: backfill ShannonTest coverage for six modules` commit if done in one run; neither has happened yet. Commit before pushing / opening a PR.
- **Verification not independently run.** `lake test` and `make check` (required by the plan's Verification section) have not been confirmed in this session. Confirm locally before merging.
- **`native_decide` in `Rational.lean`.** Two examples rely on `native_decide` to prove equalities about `Fintype.equivFinOfCardEq` parameters. `native_decide` pulls in the compiler and is generally fine for tests, but it does bloat test-run time vs. `decide`. If `decide` works, prefer it; if not, this is acceptable as-is.
- **Doc-comment punctuation style.** The module docstrings in the new files end sentences without trailing periods in a couple of places (e.g., the multi-sentence docstring in `Rational.lean` is fine, but scan once more for consistency with the existing `Core.lean`/`Properties.lean` phrasing). Minor.

**Suggestions (non-blocking):**

- Consider consolidating `entropyNat_uniformPNat 1 = 0` into a `have` reused across Joint's two last examples, or pushing it into a tiny helper; right now it is restated in two adjacent examples. Left as-is is also fine because these are `example`s, not library lemmas.
- The plan's "Follow-up" section suggests a mechanical mirror-check (a shell script or `lake exe` that fails when `Shannon/Entropy/Foo.lean` has no `ShannonTest/Entropy/Foo.lean`). Worth filing as an issue now that the structural gap is closed.
- When committing, consider per-module commits in the plan's ascending-size order (Converse, Gibbs, Joint, Approx, Rational, Uniform) plus a final commit for the `Entropy.lean` aggregator, `Final.lean` trim, and `cspell-words.txt`. That keeps `git log` readable and matches the plan's suggested workflow. A single bundled `test: backfill ShannonTest coverage for six modules` commit is also acceptable per the plan.
