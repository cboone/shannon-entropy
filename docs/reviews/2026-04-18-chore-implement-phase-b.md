## Branch Review: chore/implement-phase-b

Base: main (merge base: e0851823)
Commits: 10
Files changed: 24 (6 added, 18 modified, 0 deleted, 0 renamed)
Reviewed through: 761db70

### Summary

Phase B of the Shannon proofs roadmap. The branch adds a base-2 public API (`entropyBits` and friends), expands Shannon-narrative docstrings across the four Appendix 2 modules, adds a Shannon-summation form of conditional entropy, attempts an upstream tactic-style sync across three modules, and ships three new Verso book chapters (AxiomaticEntropy, Properties, Logarithm) plus supporting tests and cross-reference updates. `lake build Shannon`, `lake build Book`, `lake test`, and `lake lint` all pass on the current HEAD.

### Changes by Area

**Base-2 public API (Task 1)**

- New `Shannon/Entropy/Bits.lean` defines `entropyBits p := entropyBase 2 p`, a bridge to `entropyNat` (`entropyBits_eq_entropyNat_div_log_two`, `entropyNat_eq_entropyBits_mul_log_two`), base-2 analogues of the single-variable bounds (`entropyBits_nonneg`, `entropyBits_uniformPNat`, `entropyBits_le_logb_two_card`), and base-2 restatements of uniqueness (`entropyBits_unique` existential form, `entropyBits_unique_const` with `K H * Real.log 2` named).
- `Shannon/Entropy.lean` facade updated to import `Bits` and advertise the base-2 API; module-chain diagram shows `Bits` as a second leaf parallel to `Converse`.
- Files: `Shannon/Entropy/Bits.lean` (new), `Shannon/Entropy.lean`.

**Conditional-entropy Shannon form (Task 3)**

- `condEntropy_eq_shannon_form` added to `Shannon/Entropy/Joint.lean`, reshaping the `∑ ab` single-sum into the `∑ i, ∑ j` double-sum form Shannon uses in the defining equation of Property 5.
- Files: `Shannon/Entropy/Joint.lean`.

**Shannon narrative docstrings (Task 2)**

- `Uniform.lean`, `Rational.lean`, `Approx.lean`, `Final.lean` each gain a "Shannon narrative" docstring section citing Shannon 1948 by page and pointing at the corresponding Lean identifiers (`Apos_mul`, `Apos_pow`, `Apos_eq_K_mul_log`, `grouping_on_rational_counts`, `workedCompose`, `approxProb`, `entropyNat_unique`).
- Files: `Shannon/Entropy/{Uniform, Rational, Approx, Final}.lean`.

**Upstream stylistic sync (Task 4)**

- Commit 90f85c7 moved `Properties.lean` (`push Not` to `push_neg`), `Uniform.lean` (`Apos_mul` calc head), and `Rational.lean` (`grouping_on_rational_counts` sum-congr body) toward upstream tactic style. Commit 761db70 subsequently reverted `Properties.lean` back to `push Not at _` (because Mathlib v4.29 marks `push_neg` as deprecated in favor of `push Not`) and rewrote `Rational.lean`/`Uniform.lean` to different forms again. See Plan Compliance for the intent gap.
- Files: `Shannon/Entropy/{Properties, Uniform, Rational}.lean`.

**Verso book chapters (Task 6)**

- New chapters `Book/AxiomaticEntropy.lean` (three axioms, equiprobable case, rational case, continuity extension, Theorem 2), `Book/Properties.lean` (Section 6 Properties 1-6 with Lean theorem names and proof sketches), `Book/Logarithm.lean` (scale constant `K`, base choice / bits vs nats, `entropyBits_unique`).
- `Book.lean` and `Book/Introduction.lean` updated to include the chapters in reading order.
- All three chapters comply with the Phase A "no `import Shannon`" rule; identifiers are referenced by backticks only.
- Files: `Book.lean`, `Book/Introduction.lean`, `Book/AxiomaticEntropy.lean` (new), `Book/Properties.lean` (new), `Book/Logarithm.lean` (new).

**Tests (Task 5)**

- New `ShannonTest/Entropy/Bits.lean` covers `entropyBits (uniformPNat 2) = 1`, `entropyBits (uniformPNat 4) = 2`, the natural-log bridge, nonnegativity, the card bound, and both uniqueness forms (existential and named-constant).
- Existing test files extended: `Uniform.lean` (`Apos_pow n = 4` equality), `Rational.lean` (flat `(1/2, 1/3, 1/6)` direct `entropyNat_of_rational_counts` plus an exact `entropyNat` value), `Gibbs.lean` (concrete non-equal `(1/4, 3/4)` Gibbs pair plus an exact sum), `Final.lean` (`entropyBits_unique` example), `Joint.lean` (`condEntropy_eq_shannon_form` example).
- `ShannonTest/Entropy.lean` aggregator imports the new `Bits` test module.
- Files: `ShannonTest/Entropy.lean`, `ShannonTest/Entropy/Bits.lean` (new), `ShannonTest/Entropy/{Uniform, Rational, Gibbs, Joint, Final}.lean`.

**Documentation / supporting (Tasks 7, 8)**

- `references/shannon1948-transcription.md`: extended Property 5 entry and added Theorem 2 base-2 entry.
- `AGENTS.md`: added `Bits.lean` to module layout with a one-liner on the `entropyBits` / `entropyNat` public-vs-internal split.
- `cspell-words.txt`: added `congr`, `hident`, `hrelab`, `hsum`, `noncomputable`, `recursivity` (contradicting Task 8's "no additions expected" note; see Plan Compliance).
- `docs/plans/done/2026-04-18-implement-phase-b.md` (new): the Phase B plan itself, moved from `todo/` on commit 5fd1ced.
- `docs/plans/todo/2026-04-14-shannon-proofs-roadmap.md`: four corrections reconciling the roadmap with the actual state of Phase A and the 2026-04-14 test backfill.

### File Inventory

**New files (6)**: `Book/AxiomaticEntropy.lean`, `Book/Logarithm.lean`, `Book/Properties.lean`, `Shannon/Entropy/Bits.lean`, `ShannonTest/Entropy/Bits.lean`, `docs/plans/done/2026-04-18-implement-phase-b.md`.

**Modified files (18)**: `AGENTS.md`, `Book.lean`, `Book/Introduction.lean`, `Shannon/Entropy.lean`, `Shannon/Entropy/Approx.lean`, `Shannon/Entropy/Final.lean`, `Shannon/Entropy/Joint.lean`, `Shannon/Entropy/Rational.lean`, `Shannon/Entropy/Uniform.lean`, `Shannon/Entropy/Properties.lean` (via sync then revert), `ShannonTest/Entropy.lean`, `ShannonTest/Entropy/Final.lean`, `ShannonTest/Entropy/Gibbs.lean`, `ShannonTest/Entropy/Joint.lean`, `ShannonTest/Entropy/Rational.lean`, `ShannonTest/Entropy/Uniform.lean`, `cspell-words.txt`, `docs/plans/todo/2026-04-14-shannon-proofs-roadmap.md`, `references/shannon1948-transcription.md`.

**Deleted files**: none.

**Renamed files**: none (the Phase B plan moves via separate add/delete because it lives under `docs/plans/`, which git diff does not detect as a rename here).

### Notable Changes

- **New public API surface**: `entropyBits` becomes the advertised entropy for Phase C onward. Existing `entropyNat` and `entropyBase` public names are unchanged. The bridge lemmas make cross-unit reasoning clean.
- **Conditional-entropy lemma**: `condEntropy_eq_shannon_form` is a summation reshape only (no new mathematical content) but anchors the Lean definition to Shannon's prose.
- **Lean 4.29 deprecation surfaced**: `push_neg` now emits a deprecation warning; the branch uses `push Not at _` throughout `Properties.lean`. Upstream (`SamuelSchlesinger/shannon-1948-formalization`) still uses `push_neg`. The diff against upstream therefore remains nonempty on all three of `Properties`, `Uniform`, `Rational`, undercutting Task 4's "minimum-diff footprint" framing.
- **Book `ARG_MAX` constraint holds**: all three new chapters satisfy the Phase A rule against `import Shannon`.
- **Docstring style**: the new narrative paragraphs use single long lines per paragraph with blank lines between, consistent with the user-level "no hardwrap in docstrings" rule.

### Plan Compliance

**Compliance verdict**: Strong partial compliance. Eight of nine tasks land fully and correctly. Task 4 (upstream stylistic sync) is the one weak spot: commit 90f85c7 did the sync as specified, but commit 761db70 undid most of it, leaving the branch diverged from upstream on exactly the sites Task 4 aimed to clean up. The revert is justified (Mathlib v4.29 deprecated `push_neg`), but the plan's intent of minimizing the future-upstream-PR diff is not actually met, and the commit that walked back the sync does not spell this out. Task 8 has one minor plan deviation (`cspell-words.txt` additions not flagged in the plan).

**Overall progress**: 8/9 tasks fully compliant (89%); 1 partially compliant (Task 4).

**Done items**:

- Task 1 (base-2 public API): all specified definitions and lemmas present in `Shannon/Entropy/Bits.lean` with the exact names the plan named. Facade and module-chain diagram updated. Caveat: none.
- Task 2 (narrative docstrings): all four modules (`Uniform`, `Rational`, `Approx`, `Final`) got the specified paragraphs. The Uniform and Rational docstrings are the most developed; Approx and Final are shorter single-paragraph additions but still land the page references and the identifier pointers the plan asked for.
- Task 3 (Shannon-form conditional entropy): `condEntropy_eq_shannon_form` placed as specified after `condEntropy` definition, before `chain_rule`. Proof is the one-line `Fintype.sum_prod_type` reshape the plan predicted.
- Task 5 (testing): `ShannonTest/Entropy/Bits.lean` created with the full slate of examples. Extensions to `Uniform.lean`, `Rational.lean`, `Gibbs.lean`, `Final.lean`, `Joint.lean` all present. `ShannonTest/Entropy.lean` imports the new test module. The `(1/2, 1/3, 1/6)` example was in fact added in two forms: the roadmap-required direct `entropyNat_of_rational_counts` instance with counts `(3, 2, 1)`, plus a bonus exact-value check `entropyNat p = (2/3)·log 2 + (1/2)·log 3`. Caveat: none.
- Task 6 (Verso book chapters): `AxiomaticEntropy.lean`, `Properties.lean`, `Logarithm.lean` created with the exact section slugs and section structure the plan enumerated. `Book.lean` includes them in the specified order. `Book/Introduction.lean` reading-order list updated to mention the new chapters and `Shannon/Entropy/Bits.lean`. All chapters compile under `lake build Book`.
- Task 7 (transcription cross-refs): Property 5 entry extended in place; Theorem 2 base-2 entry added directly below the existing Theorem 2 entry. Exactly the edits the plan listed.
- Task 8 (AGENTS.md module layout): added `Shannon/Entropy/Bits.lean` to the module list with the `entropyBits` / `entropyNat` split described in one line. Partial caveat on `cspell-words.txt` (see Deviations below).
- Commit strategy (non-task but plan-specified): five commits as the plan described (`chore(style)`, `feat(entropy): add entropyBits`, `feat(entropy): Shannon-form conditional entropy`, `docs(shannon): expand ... docstrings`, `docs(book): add ... chapters`), plus two plan-iteration commits (`docs: reconcile ... details`, `docs: correct ... details flagged during review`), a plan-move commit, and one `fix(entropy): address Phase B review findings` follow-up. The follow-up is not an anti-pattern but deserves the call-out in Task 4 below.

**Partially done items**:

- Task 4 (upstream stylistic sync): the sync commit 90f85c7 lands as designed (three `push_neg` changes in Properties, `simp [Apos, hident] at hrelab ⊢` form in Uniform, `simpa only [Apos, hident] using hrelab` plus `simp only [Apos, q]; rfl` in Rational), but commit 761db70 then reverts Properties back to `push Not at _` (three sites) and rewrites the Uniform and Rational forms again (`simpa [Apos] using (congrArg H hident.symm).trans hrelab` in Uniform; `show ... rfl` in Rational's sum-congr body, `simpa [Apos, hident] using hrelab` in the calc head). The end state is farther from upstream than where the sync commit left it. `git diff upstream/main..HEAD -- Shannon/Entropy/Properties.lean` still shows the three `push Not`/`push_neg` hunks (reversed now: HEAD has `push Not`, upstream has `push_neg`). What remains: reconcile with upstream. Either upstream needs to move to Lean 4.29 (and flip to `push Not`), or the plan's "minimum-diff upstream footprint" framing needs to be replaced with "minimum-diff against Lean 4.29 idioms"; a brief note in the commit message or an updated plan entry should record that the revert was forced by Mathlib deprecation, not by taste.

**Not started items**: none.

**Deviations**:

- **`cspell-words.txt` (Task 8)**: the plan says "no additions expected"; the branch adds six words (`congr`, `hident`, `hrelab`, `hsum`, `noncomputable`, `recursivity`). Reasonable because the new narrative docstrings and book chapters introduce those tokens as literal prose fragments, and cspell scans markdown-rendered docstrings. Minor and arguably correct; the plan's assertion was just wrong.
- **Plan move to `done/`**: the plan file was moved from `docs/plans/todo/` to `docs/plans/done/` in commit 5fd1ced. Not a deviation per se, just a housekeeping step the plan itself did not enumerate.
- **Roadmap edits (`docs/plans/todo/2026-04-14-shannon-proofs-roadmap.md`)**: four small corrections to the roadmap's Phase A/B rows, folding the Foundations placeholder into AxiomaticEntropy and calling out the already-backfilled Phase-1 test files. Not required by the Phase B plan but sensible.
- **Extra `entropyNat` exact-value example in `Rational` tests**: beyond the plan's required direct `entropyNat_of_rational_counts` instantiation, the branch adds a second `(1/2, 1/3, 1/6)` example that computes the exact entropy value `(2/3)·log 2 + (1/2)·log 3`. Nice-to-have, not scope creep; no plan conflict.
- **Gibbs test extension**: the plan specified "example invoking `gibbs_inequality` on a concrete non-equal pair"; the branch delivers that plus a separate exact-value computation of the Gibbs sum `= log(3/4) / 2`. Again a bonus, consistent with the task's intent.

**Fidelity concerns**:

- The commit message for 761db70 ("Remove deprecated tactic usage and strengthen the concrete regression checks") does not spell out that it is walking back the stylistic-sync commit 90f85c7's changes on three sites. A reader picking over the branch will see two commits moving the same lines in opposite directions and have to guess at the rationale. Fix: amend or supplement with a note that `push_neg` was deprecated in Mathlib v4.29 and the Uniform/Rational rewrites were needed to keep the build green (if they were) or to remove redundant tactic hints (if cosmetic).
- Task 4's "minimum-diff upstream footprint" is not achieved. The plan should probably be updated after merge to reflect the Lean-4.29-induced constraint. If a future upstream PR is still in scope, it cannot be a literal cherry-pick; it will have to be gated on upstream's own Lean-4.29 migration.

### Code Quality Assessment

**Overall quality**: Ready to merge with minor clarification asks. The Lean is clean, the tests are thorough, the book chapters are well-written narrative, and the plan was followed closely on content. The one weakness is process-level (Task 4's intent and its commit-message story) rather than code-level.

**Strengths**:

- `Shannon/Entropy/Bits.lean` is a tight, well-scoped module. The bridge proof `entropyBits_eq_entropyNat_div_log_two` is direct (`neg_div` plus `Finset.sum_div` plus the `Real.logb` unfold), and the uniqueness restatements avoid re-proving the heavy machinery by invoking `entropyBase_unique` and `entropyNat_unique`. `entropyBits_unique_const` spells out the constant as `K H * Real.log 2`, which is strictly more informative than the existential `entropyBits_unique` and will be the more useful form for downstream Phase C work.
- `condEntropy_eq_shannon_form` is a one-line proof that does exactly what it advertises. The statement uses `∑ a, ∑ b` rather than `∑ ab` specifically so the prose-level correspondence with Shannon's `∑_{i,j}` is visible in the Lean goal, a nice bit of API hygiene.
- Test coverage is good. The `(1/2, 1/3, 1/6)` exact-value example is the strongest numeric check the mirror has; the concrete Gibbs pair exercises `gibbs_inequality` on genuinely non-equal distributions; the `entropyBits (uniformPNat 4) = 2` proof lands the base-2 / `Real.logb_pow` pattern that Phase C will need.
- The new book chapters are good mathematical exposition: they cite Shannon 1948 by section and page, reference the Lean theorem names in backticks, and state proof sketches in one sentence each. The `Logarithm` chapter in particular does a clean job of motivating the `K · log b` base-change rule and slotting `entropyBits` into the narrative.
- Docstring narrative additions use consistent phrasing ("Our Lean counterparts are X, Y, Z") across the four Appendix 2 modules. Readers working through `references/shannon1948.pdf` alongside the Lean files will have a single-unit-of-attention mapping at each module top.

**Issues to address**:

- **Commit-message clarity for 761db70**: add a follow-up commit (or amend on a rebase if the branch is not yet pushed elsewhere) that explicitly records the reason for walking back the Properties sync — `push_neg` deprecation in Mathlib v4.29 — so readers do not have to reconstruct the rationale. Similarly, the Uniform and Rational tactic rewrites should be justified (build failure on v4.29, cosmetic preference, or something else) rather than shipped under "Remove deprecated tactic usage".
- **Plan annotation for Task 4**: update `docs/plans/done/2026-04-18-implement-phase-b.md` (or add a trailing "Post-merge notes" section) to record that Task 4's upstream-sync goal was met in spirit on two files (where the sync form landed) and then partially undone on Properties.lean by the Lean 4.29 deprecation. Alternatively, open an issue tracking a second upstream-sync pass once upstream migrates to Lean 4.29.
- **`entropyBits_unique_const` naming**: the `_const` suffix reads as "constant form" (constant named) vs "existential form", but at first encounter it can parse as "constant entropy", which is misleading. Consider `entropyBits_eq_neg_K_log_two_mul_sum` or at least a rename to `entropyBits_unique_eq` for the next pass. Not blocking.

**Suggestions**:

- `ShannonTest/Entropy/Bits.lean`: the second uniqueness example is a fine mirror of the existential form but arguably redundant with the `Final.lean` sibling; consider trimming to just the named-constant `entropyBits_unique_const` example here and leaving the existential to `Final.lean`, to keep the mirror test surface tight.
- The `entropyBits_def` docstring calls it "definitional expansion" but the lemma is `rfl`. Since `Real.logb` unfolds on the right, this is fine; a one-line note that this `rfl`-holds by the `entropyBase`-to-`Real.logb` definition chain would help future readers understand why no rewriting is needed.
- `Book/AxiomaticEntropy.lean` mentions `Apos_ratio_logb_close` / `Apos_ratio_eq_logb` / `Apos_eq_K_mul_log` but skips the fact that the ratio-squeeze interval `[m/n, (m+1)/n]` is what delivers the `1/n` bound. One more sentence on "letting `n → ∞` pins `A(t)/A(s)` to `log_s t`" in the "Equiprobable Case" section would make the narrative slightly more self-contained. Minor.
- Consider adding an `Shannon/Entropy/Bits.lean` lemma `entropyBits_prodDist : entropyBits (prodDist p q) = entropyBits p + entropyBits q` as a free-standing corollary of `entropyNat_prodDist` and the bridge. It will be wanted by any Phase C statement in bits and is a one-line proof. Out of scope for this PR; note for Phase C.
