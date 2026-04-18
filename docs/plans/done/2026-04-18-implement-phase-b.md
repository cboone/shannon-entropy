# 2026-04-18 Phase B: tighten Shannon correspondence and introduce the base-2 API

Date: 2026-04-18
Status: Draft. Targets Phase B of `docs/plans/todo/2026-04-14-shannon-proofs-roadmap.md`.

## Context

Phase A shipped on 2026-04-18 (merged as `docs/implement-phase-a-verso`, commit `e085182`). The Verso Manual-genre companion book is scaffolded with `Book/Introduction.lean` and `Book/Bibliography.lean`, and CI already builds and renders it. Phase A also pinned one cross-cutting invariant: chapters under `Book/` must not `import Shannon` or any `Shannon.*` module, because Lake's link argv otherwise exceeds macOS `ARG_MAX`. This rule applies to every new chapter Phase B adds.

The Lean side currently covers Shannon Appendix 2 (`entropyNat_unique`, `entropyBase_unique` in `Shannon/Entropy/Final.lean`) plus Section 6 Properties 1-6 (in `Shannon/Entropy/Properties.lean` and `Shannon/Entropy/Joint.lean`). The `ShannonTest/` mirror is complete as of the 2026-04-14 backfill: every `Shannon/Entropy/<M>.lean` has a matching `ShannonTest/Entropy/<M>.lean`.

Three observations from reading the current code that shape Phase B:

- `entropyNat` and `entropyBase` both already live in `Shannon/Entropy/Uniform.lean`; `entropyBase b` already takes an arbitrary base `b`. A Phase B `entropyBits` wrapper can be a very thin layer on top of `entropyBase 2`, plus a handful of bridge lemmas.
- `condEntropy` in `Shannon/Entropy/Joint.lean` is already defined exactly as `-∑ ab, p ab * log (p ab / marginalFst p ab.1)`. Shannon's Property 5 writes this as `-∑_{i,j} p(i,j) log p_i(j)` with `p_i(j) := p(i,j)/p(i)`. A `condEntropy_eq_shannon_form` lemma ties these together as a product-type double sum. It is a narrative lemma (essentially a summation reshape), not a new mathematical fact.
- Diffing `HEAD` against `upstream/main` shows the three drift points named in the roadmap: `push Not` vs `push_neg`, and verbose `simp only ... rw ...` versus upstream `simpa`. I confirmed these are exactly the sites flagged. The current repo also renumbered some Property headers ("Property 6" vs upstream's "Properties 5-6") to match the transcription, and that renumbering is deliberate and stays.

Roadmap sub-item count that the current test backfill has partially already covered: `ShannonTest/Entropy/{Uniform, Rational, Gibbs}.lean` already exist from 2026-04-14. For those three modules Phase B adds _extra cases_ rather than creating new files. Only `ShannonTest/Entropy/Bits.lean` is truly new.

## Goal

Deliver five things in one branch:

1. A base-2 public API (`entropyBits`, bridge lemmas, base-2 corollaries of the uniqueness theorems) so later phases can state results directly in bits.
2. Shannon-narrative docstrings on the Appendix 2 modules, with explicit page references to Shannon 1948.
3. A `condEntropy_eq_shannon_form` lemma that anchors the Lean conditional entropy definition to the summation form Shannon uses in Property 5.
4. Upstream stylistic sync for three modules, so a future upstream PR has a minimum-diff footprint.
5. Three new Verso chapters (`AxiomaticEntropy`, `Properties`, `Logarithm`) covering the currently-formalized Appendix 2 and Section 6 material, plus the corresponding test additions.

Non-goals (reserved for Phase C+): mutual-information/KL-divergence primitives, i.i.d. AEP, finite-state source machinery.

## Tasks

### 1. Base-2 public API (`Shannon/Entropy/Bits.lean`)

Create `Shannon/Entropy/Bits.lean`:

- Imports `Shannon.Entropy.Gibbs`. `Gibbs` already imports `Shannon.Entropy.Final` (which in turn imports `Approx → Rational → Uniform`), so a single `import Shannon.Entropy.Gibbs` transitively provides everything `Bits` needs: `entropyBase`, `K`, and `K_pos` from `Uniform.lean`; `entropyBase_unique` from `Final.lean`; and the single-variable lemmas (`entropyNat_nonneg`, `entropyNat_uniformPNat`, `entropyNat_le_log_card`) from `Gibbs.lean` that the Phase B base-2 bridge lemmas reuse.
- `namespace Shannon`, `noncomputable section`.
- Module docstring describing `entropyBits` as the base-2 specialization, the primary public entropy API going forward, while `entropyNat` stays as the internal natural-log workhorse.

Definitions:

```lean
/-- Base-2 Shannon entropy (bits). Defined via `entropyBase 2`.
This is the primary public entropy API for Phase C and later. -/
noncomputable def entropyBits {α : Type} [Fintype α] (p : ProbDist α) : ℝ :=
  entropyBase 2 p
```

Lemmas:

- `entropyBits_def` (definitional expansion): `entropyBits p = -∑ a, p a * Real.logb 2 (p a)`.
- `entropyBits_eq_entropyNat_div_log_two` : for any `p`, `entropyBits p = entropyNat p / Real.log 2`. Proof: unfold both defs, rewrite `Real.logb` as `Real.log / Real.log 2`, factor the sum. `Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1)` handles the nonzero divisor.
- `entropyNat_eq_entropyBits_mul_log_two` (reverse direction).
- `entropyBits_nonneg`: `0 ≤ entropyBits p`. Proof: `entropyBits p = entropyNat p / log 2`, `entropyNat_nonneg p` from `Gibbs.lean`, `log 2 > 0`.
- `entropyBits_uniformPNat` : `entropyBits (uniformPNat n) = Real.logb 2 n` for `n : ℕ+`. Proof: rewrite via `entropyNat_uniformPNat`.
- `entropyBits_le_logb_two_card` (analogue of `entropyNat_le_log_card`) for nonempty `α`.

Corollaries of existing uniqueness theorems (new names; keep old names untouched):

- `entropyBits_unique` : for `H` satisfying `ShannonEntropyAxioms`, there exists `Kb > 0` with `H p = -Kb * ∑ a, p a * Real.logb 2 (p a)` for every `p`. Obtained by invoking `entropyBase_unique H hH 2 (by norm_num : (1:ℝ) < 2)`.
- `entropyBits_unique_eq` (tighter statement that names the constant; originally drafted as `entropyBits_unique_const`, renamed in commit `bc31a19`): `H p = -(K H * Real.log 2) * ∑ a, p a * Real.logb 2 (p a)`. Follows the `entropyBase_unique` proof inlined with `b := 2`.

Facade update in `Shannon/Entropy.lean`:

- Add `import Shannon.Entropy.Bits`.
- Update the module-chain diagram in the docstring to place `Bits` as a leaf after `Gibbs`, parallel to the existing `Converse` branch. `Converse` already branches off `Gibbs` (see `Shannon/Entropy/Converse.lean:1`, `import Shannon.Entropy.Gibbs`), and the current diagram places it there; the Phase B update adds `Bits` as a second leaf at the same level:

  ```
  Core → Uniform → Rational → Approx → Final → Gibbs → Joint → Properties
                                                    ↘ Converse
                                                    ↘ Bits
  ```

- Extend the "Import this file to access..." bullet list with "base-2 API: `entropyBits`, `entropyBits_unique`".

No changes to `Core`, `Uniform`, `Rational`, `Approx`, `Final`, `Gibbs`, `Joint`, `Properties`, or `Converse` are required for this task; `Bits` is a strict addition.

### 2. Narrative docstrings in Appendix 2 modules

Expand the top-of-module docstrings in the four Appendix 2 modules to add Shannon narrative content. Do not touch statements or proofs. Target a Shannon-paper reader who has just opened the Lean file alongside `references/shannon1948.pdf`.

Per-file prose additions (single long lines per paragraph, one blank line between paragraphs, per the repo-wide "no hardwrap in docstrings" rule from `~/.claude/CLAUDE.md`):

- `Shannon/Entropy/Uniform.lean`: one paragraph summarizing Shannon's `A(sⁿ) = n · A(s)` mnemonic (Appendix 2, first half, pp. 48-49), one paragraph on the ratio-squeeze `sᵐ ≤ tⁿ < sᵐ⁺¹` that proves `A(n) = K log n`. Reference `Apos_mul` / `Apos_pow` / `Apos_eq_K_mul_log` by name as the Lean counterparts.
- `Shannon/Entropy/Rational.lean`: one paragraph summarizing the grouped-equiprobable refinement: a rational distribution `p_i = n_i/N` is recovered by splitting a size-`N` uniform into `|α|` blocks of sizes `n_i`; applying grouping plus the Phase-1 formula gives `H p = -K ∑ p_i log p_i`. One paragraph on the `(1/2, 1/3, 1/6)` tree example Shannon uses on p. 49 and its Lean counterpart (`workedCompose`, `worked_grouping_identity`).
- `Shannon/Entropy/Approx.lean`: one paragraph on the continuity-extension trick: floor-count approximants `approxProb p N` are rational with denominator near `N + 1`; their limit is `p`; continuity upgrades the rational formula to all real probabilities.
- `Shannon/Entropy/Final.lean`: one paragraph naming this as Shannon's Theorem 2 and pointing at the transcription entry. Keep the existing "Theorem Index" section.

These docstrings are narrative only. They must cite Shannon 1948 by section and page but not rely on LaTeX-heavy math rendering (docstrings are rendered as plain Markdown in hover tooltips and in Verso's docstring-fetch tooling).

### 3. Shannon-form conditional entropy lemma

Add in `Shannon/Entropy/Joint.lean`, after the `condEntropy` definition but before `chain_rule`:

```lean
/-- Shannon's Property 5 form: the conditional entropy unfolds to the double
sum `-∑_i ∑_j p(i, j) log p_i(j)` with `p_i(j) = p(i, j) / p_X(i)`. Ties the
Lean definition of `condEntropy` to the summation form Shannon writes in the
defining equation of Property 5 (Section 6, pp. 11-12). -/
theorem condEntropy_eq_shannon_form
    {α β : Type} [Fintype α] [Fintype β] (p : ProbDist (α × β)) :
    condEntropy p
      = -∑ a, ∑ b, p (a, b) * Real.log (p (a, b) / marginalFst p a) := by
  unfold condEntropy
  rw [Fintype.sum_prod_type]
```

The statement uses `∑ a, ∑ b` rather than `∑ ab` so the prose-level correspondence with Shannon's `∑_{i,j}` is visible in the Lean goal. The proof is a one-line `Fintype.sum_prod_type` reshape.

No rename or change to the existing `condEntropy` definition. No new namespace.

### 4. Upstream stylistic sync

Apply three point changes so `HEAD` matches `upstream/main` on tactic style for these files. `git diff upstream/main..HEAD -- Shannon/Entropy/{Uniform, Rational, Properties}.lean` confirms exactly these sites:

- `Shannon/Entropy/Properties.lean`: three `push Not at <h>` → `push_neg at <h>` (lines around 36, 106, 118 in the current file).
- `Shannon/Entropy/Uniform.lean`: in `Apos_mul`, replace the three-line `simp only [Apos]; rw [hident] at hrelab; exact hrelab` with upstream's two-line form `simp [Apos, hident] at hrelab ⊢` followed by `exact hrelab` (~lines 55-58). Note that upstream does _not_ collapse these into a single `simpa ... using hrelab`; the goal-and-hypothesis `simp ... at hrelab ⊢` form is what `git diff upstream/main..HEAD -- Shannon/Entropy/Uniform.lean` flags.
- `Shannon/Entropy/Rational.lean`: in `grouping_on_rational_counts`, replace the three-line `simp only [Apos]; rw [hident] at hrelab; exact hrelab` with `simpa [Apos, hident] using hrelab` (~lines 72-76). This file _does_ use the one-line `simpa` form upstream; the site is distinct from the `Uniform.lean` one above despite the visible similarity. Also replace the `congr 1` inside `hsumA` with upstream's `simp [Apos, q]` (~line 70).

Do _not_ revert the `Properties.lean` Property 5 / Property 6 header / docstring renumbering. That renumbering is intentional and aligns with the transcription; it is a correctness improvement, not stylistic drift. The roadmap explicitly scopes this task to tactic style.

One commit for the sync, separate from the Phase B content commits, so a future upstream PR can cherry-pick it cleanly. Verify with `lake build Shannon` and `lake test` after the change.

### 5. Testing

The ShannonTest mirror must remain complete. Phase B's test surface adds exactly one new file (`ShannonTest/Entropy/Bits.lean`) and extends five existing entropy test files, plus the `ShannonTest/Entropy.lean` aggregator.

New: `ShannonTest/Entropy/Bits.lean`

Template (opens `Shannon`, imports `Shannon.Entropy.Bits`):

```lean
example : entropyBits (uniformPNat 2) = 1 := by
  simpa [entropyBits_uniformPNat] using Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)

example : entropyBits (uniformPNat 4) = 2 := by
  rw [entropyBits_uniformPNat]
  -- logb 2 4 = 2
  sorry  -- placeholder; real proof uses `Real.logb_pow` or a `norm_num` extension

example (p : ProbDist (Fin 3)) : entropyBits p = entropyNat p / Real.log 2 :=
  entropyBits_eq_entropyNat_div_log_two p

example (p : ProbDist (Fin 3)) : 0 ≤ entropyBits p :=
  entropyBits_nonneg p

example (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H) :
    ∃ Kb : ℝ, 0 < Kb ∧
      ∀ {α : Type} [Fintype α] (p : ProbDist α),
        H p = -Kb * ∑ a, p a * Real.logb 2 (p a) :=
  entropyBits_unique H hH
```

The `entropyBits (uniformPNat 4) = 2` goal does need actual proof, not `sorry`; the placeholder above marks the spot. Expected approach: rewrite `(4 : ℝ) = 2^2` and apply `Real.logb_pow` (or `Real.logb_rpow`) plus `Real.logb_self`. Verify exact Mathlib names (`Real.logb_self_eq_one`, `Real.logb_pow`, `Real.logb_rpow`) against the pinned Mathlib v4.29.0 at implementation time; if any have been renamed or moved, grep `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/` for the current canonical name rather than inventing a local wrapper.

Extensions to existing test files:

- `ShannonTest/Entropy/Uniform.lean`: add `example : Apos entropyNat 4 = 2 * Apos entropyNat 2` (chains `Apos_pow entropyNat entropyNat_shannonAxioms 2 2` with `show (4 : ℕ+) = 2 ^ 2 from rfl`) to exercise the `Apos_eq_K_mul_log` / `Apos_pow` pair as the roadmap requests.
- `ShannonTest/Entropy/Rational.lean`: add an example computing `entropyNat_of_rational_counts` on a concrete `(1/2, 1/3, 1/6)` distribution. Encode as `ProbDist (Fin 3)` with masses `![1/2, 1/3, 1/6]` and counts `![3, 2, 1]` summing to `N = 6`. This is the numeric complement to the tree-shaped `workedCompose` example already present.
- `ShannonTest/Entropy/Gibbs.lean`: add an example invoking `gibbs_inequality` on a concrete non-equal pair, e.g. `p := uniformPNat 2` against `q : ProbDist (Fin 2)` with masses `(1/4, 3/4)`, checking the inequality numerically.
- `ShannonTest/Entropy/Final.lean`: add an example calling `entropyBits_unique` (the base-2 corollary), mirroring the existing `entropyBase_unique` example.
- `ShannonTest/Entropy/Joint.lean`: add an example calling `condEntropy_eq_shannon_form` on `prodDist (uniformPNat 2) (uniformPNat 3)` to exercise the new lemma.

Update `ShannonTest/Entropy.lean` to add `import ShannonTest.Entropy.Bits`.

Run `lake test` to confirm all new examples type-check, then `make check` for the full local pipeline.

### 6. Verso book chapters

All three new chapters live under `Book/` and must not `import Shannon` or any `Shannon.*` module. Chapter content references Lean identifiers by name in code fences and inline backticks; it does not render highlighted Lean blocks via `subverso` in Phase B (defer that enrichment to Phase C, where more material justifies the plumbing cost). Each chapter follows the Phase-A template: `import VersoManual`; `open Verso.Genre Manual` and `open Verso.Genre.Manual.InlineLean`; `#doc (Manual) "<Title>" => %%% tag := "<slug>" %%%`; section headers (`#`) for subdivisions.

New: `Book/AxiomaticEntropy.lean`

Sections (approximate):

- "The Three Axioms": narrate `ShannonEntropyAxioms` in prose, listing `continuous`, `uniformMonotone`, `relabelInvariant`, `grouping` with Shannon's informal wording (continuity, monotonicity on uniforms, invariance, grouping / recursivity).
- "Equiprobable Case": walk `Apos_mul`, `Apos_pow`, the ratio squeeze `sᵐ ≤ tⁿ < sᵐ⁺¹`, and `Apos_eq_K_mul_log`. Cite `Shannon/Entropy/Uniform.lean` by name.
- "Rational Case": grouping refinement; reference `grouping_on_rational_counts` and the worked `(1/2, 1/3, 1/6)` example. Cite `Shannon/Entropy/Rational.lean`.
- "Continuity Extension": `approxProb`, `tendsto_approxProb`. Cite `Shannon/Entropy/Approx.lean`.
- "Theorem 2": the final statement `entropyNat_unique` and its base-parametric form `entropyBase_unique`. Cite `Shannon/Entropy/Final.lean`.

This chapter subsumes the older roadmap placeholder name `Foundations`; no separate `Book/Foundations.lean` file is planned for Phase B.

New: `Book/Properties.lean`

Sections, in transcription order:

- "Property 1: Nonnegativity (`entropyNat_eq_zero_iff`)".
- "Property 2: Maximum at Uniformity (`entropyNat_eq_log_card_iff`)".
- "Property 3: Subadditivity (`entropyNat_joint_le_add`)".
- "Property 4: Schur-Concavity (`entropyNat_doublyStochastic_le`)".
- "Property 5: Chain Rule (`chain_rule`, `condEntropy_eq_shannon_form`)".
- "Property 6: Conditioning Reduces Entropy (`condEntropy_le_entropyNat`)".

Each section: Shannon's informal statement, the Lean theorem name in backticks, one-sentence sketch of the proof idea. Cite `Shannon/Entropy/Joint.lean`, `Shannon/Entropy/Properties.lean`, `Shannon/Entropy/Gibbs.lean` for the Gibbs inequality used as the analytical workhorse.

New: `Book/Logarithm.lean`

Sections:

- "The Scale Constant `K`": Shannon's proof delivers `H p = -K ∑ p_i log p_i` for an implementation-defined positive `K`; changing the logarithm base changes `K`. Reference `K`, `K_pos` from `Shannon/Entropy/Uniform.lean`.
- "Base Choice": discuss natural log (nats, `entropyNat`), base 2 (bits, `entropyBits`), base e vs base 2 as conventions in the literature; reference `entropyBase_unique` in `Shannon/Entropy/Final.lean` as the base-parametric statement, and `entropyBits_unique` in `Shannon/Entropy/Bits.lean` as its base-2 specialization.
- "Going Forward": signal that Phase C onward will state results in bits via `entropyBits`.

The converse theorem `entropyNat_shannonAxioms` remains part of the Lean public surface in Phase B, but it is not one of the Shannon-paper-facing narrative targets for these three chapters. The book scope here is Appendix 2, Section 6 Properties 1-6, and the new base-2 API layer.

Update `Book.lean` (root document) to include the new chapters in reading order, between Introduction and Bibliography:

```
{include 0 Book.Introduction}
{include 0 Book.AxiomaticEntropy}
{include 0 Book.Properties}
{include 0 Book.Logarithm}
{include 0 Book.Bibliography}
```

Update the "Reading Order" bullet list in `Book/Introduction.lean` to mention the new chapters and add a pointer to `Shannon/Entropy/Bits.lean` alongside the existing module list.

After chapter additions, run `make book` and open `_site/html-multi/index.html` (or `make serve`) to spot-check that chapters render, that internal cross-references resolve, and that the TOC depth-2 view still looks right.

### 7. Transcription cross-references

Update `references/shannon1948-transcription.md` in its `## Formalization Cross-References` section:

- Extend the Property 5 entry in place: `- **Property 5** (chain rule): \`chain_rule\` in \`Shannon/Entropy/Joint.lean\`, with the summation form given by \`condEntropy_eq_shannon_form\`.`
- Add a new bullet directly below the Theorem 2 entry: `- **Theorem 2** (base 2 specialization): \`entropyBits_unique\` in \`Shannon/Entropy/Bits.lean\`.`

Per the roadmap's explicit note, no other entries change in Phase B; Phase B does not introduce a new Shannon theorem.

### 8. Documentation and vocabulary

- `AGENTS.md` / `CLAUDE.md` (symlink): update the "Module Layout" block to list `Shannon/Entropy/Bits.lean` alongside the existing modules; add one line stating that `entropyBits` is the primary public entropy API for Phase C and later while `entropyNat` stays as the natural-log internal workhorse.
- `cspell-words.txt`: no additions expected (`logb`, `Verso`, `subverso` are already present; `entropyBits` is a Lean identifier, not a dictionary word).

No README or Makefile changes in Phase B (Phase A already installed the book-building workflow).

## Critical files

Existing, to modify (in rough task order):

- `Shannon/Entropy/Uniform.lean`: docstring expansion (Task 2); upstream stylistic sync (Task 4).
- `Shannon/Entropy/Rational.lean`: docstring expansion (Task 2); upstream stylistic sync (Task 4).
- `Shannon/Entropy/Approx.lean`: docstring expansion (Task 2).
- `Shannon/Entropy/Final.lean`: docstring expansion (Task 2).
- `Shannon/Entropy/Joint.lean`: add `condEntropy_eq_shannon_form` (Task 3).
- `Shannon/Entropy/Properties.lean`: upstream stylistic sync (Task 4).
- `Shannon/Entropy.lean`: facade imports + diagram update for `Bits` (Task 1).
- `ShannonTest/Entropy.lean`: register `ShannonTest.Entropy.Bits` (Task 5).
- `ShannonTest/Entropy/Uniform.lean`: add `Apos_pow`-based `n = 4` example (Task 5).
- `ShannonTest/Entropy/Rational.lean`: add `(1/2, 1/3, 1/6)` direct example (Task 5).
- `ShannonTest/Entropy/Gibbs.lean`: add concrete non-equal-pair example (Task 5).
- `ShannonTest/Entropy/Final.lean`: add `entropyBits_unique` example (Task 5).
- `ShannonTest/Entropy/Joint.lean`: add `condEntropy_eq_shannon_form` example (Task 5).
- `Book.lean`: include three new chapters in reading order (Task 6).
- `Book/Introduction.lean`: extend reading-order list (Task 6).
- `references/shannon1948-transcription.md`: extend Property 5 and Theorem 2 cross-refs (Task 7).
- `AGENTS.md`: mention `Shannon/Entropy/Bits.lean` and the `entropyBits` public-API policy (Task 8).

New, to create:

- `Shannon/Entropy/Bits.lean` (Task 1).
- `ShannonTest/Entropy/Bits.lean` (Task 5).
- `Book/AxiomaticEntropy.lean` (Task 6).
- `Book/Properties.lean` (Task 6).
- `Book/Logarithm.lean` (Task 6).

## Commit strategy

Five commits keep the branch reviewable:

1. `chore(style): sync upstream tactic style in Uniform/Rational/Properties` (Task 4, cherry-pick-friendly).
2. `feat(entropy): add entropyBits base-2 public API` (Task 1, facade update, cross-ref update, `ShannonTest/Entropy/Bits.lean`, `ShannonTest/Entropy.lean`).
3. `feat(entropy): Shannon-form conditional entropy lemma` (Task 3, corresponding test extension).
4. `docs(shannon): expand Appendix 2 module docstrings` (Task 2).
5. `docs(book): add AxiomaticEntropy, Properties, Logarithm chapters` (Task 6, `Book.lean` update, Introduction reading-order update).

Any extra test-only changes (the `entropyNat_of_rational_counts` rational example, the concrete `gibbs_inequality` pair, the `Apos_pow n=4` case) go into whichever feat commit first exposes the target surface; the new `entropyBits_unique` test rides commit 2. Task 7 and Task 8 (transcription cross-refs, `AGENTS.md` vocabulary) ride commit 2 or 5 as fits.

If any commit's scope grows unexpectedly (for example, the `entropyBits_uniformPNat` proof needing a substantive lemma chain), split off that sub-change into its own commit rather than bloating the feat commit.

## Verification

Per-task tripwires (local; run before committing each task):

- Task 1: `lake build Shannon.Entropy.Bits` compiles cold; `lake build Shannon` compiles with the updated facade; `lake test` runs the new `ShannonTest/Entropy/Bits.lean` examples.
- Task 2: `lake build Shannon` still compiles (docstring-only diffs shouldn't change anything, but the compiler does lint docstrings via `lake lint`).
- Task 3: `lake build Shannon.Entropy.Joint` compiles; `lake test` runs the new joint-entropy test example.
- Task 4: `git diff upstream/main..HEAD -- Shannon/Entropy/{Uniform, Rational, Properties}.lean` on those three files shrinks to just content differences (no tactic-style differences left). `lake test` green.
- Task 5: `lake test` runs the full mirrored suite.
- Task 6: `lake build Book` compile-only check; then `make book` produces `_site/html-multi/index.html` listing the three new chapters in the TOC.

End-of-phase checks (`make check` is the blanket command):

- `make check` passes end-to-end: markdownlint, cspell, `lake lint`, `lake build`, `lake test`.
- `make book` produces non-empty rendered output under `_site/html-multi/` with the expected five-chapter TOC.
- `bin/bootstrap-worktree` still works from a clean worktree (spot-check by deleting `.lake/` and re-running).
- Spot-check the rendered book at `make serve` to confirm chapter cross-references (where added) resolve and the TOC depth-2 view renders sensibly.

Roadmap-level sanity checks (Phase B row):

- `entropyBits (uniformPNat 2) = 1` and `entropyBits (uniformPNat 4) = 2` compile as `example` statements in `ShannonTest/Entropy/Bits.lean`.
- Shannon's worked `(1/2, 1/3, 1/6)` distribution resolves to its expected entropy value in `ShannonTest/Entropy/Rational.lean`.

Keep the diff clean against `upstream/main` for `Shannon/Entropy/Uniform.lean`, `Shannon/Entropy/Rational.lean`, and `Shannon/Entropy/Properties.lean` apart from the deliberate docstring expansions and the Properties renumbering that already exists on `HEAD`. `git diff upstream/main..HEAD -- Shannon/Entropy/` after Phase B should read as "docstrings expanded, one new module `Bits.lean`, `Joint.lean` has one extra lemma", with no lingering tactic-style drift.

## Post-merge notes

Task 4's upstream-sync goal landed only partially, captured here so a future reader does not have to reconstruct the story from the commit graph.

- **`push_neg` deprecation in Mathlib v4.29.** Commit 90f85c7 moved the three `push Not at _` sites in `Shannon/Entropy/Properties.lean` over to `push_neg at _` to match `upstream/main`. Lean 4.29's Mathlib (`.lake/packages/mathlib/Mathlib/Tactic/Push.lean:278, 345`) prints a deprecation warning on `push_neg` and directs callers to `push Not`. Commit 761db70 therefore reverted Properties.lean back to `push Not at _`. The net effect: `git diff upstream/main..HEAD -- Shannon/Entropy/Properties.lean` still shows the three hunks, now reversed (HEAD has `push Not`, upstream has `push_neg`). A literal upstream cherry-pick of the sync commit is no longer possible; a future upstream PR will have to wait until `upstream/main` migrates to Lean 4.29 and adopts `push Not` itself.
- **Uniform and Rational tactic rewrites in 761db70.** The same follow-up commit rewrote `Apos_mul`'s calc head in `Uniform.lean` to `simpa [Apos] using (congrArg H hident.symm).trans hrelab` and `grouping_on_rational_counts`'s sum-congr body in `Rational.lean` to a `show ... ; rfl` form, moving both back toward the pre-sync state. These changes were not driven by deprecation; the commit bundled them under the same "address review findings" heading. For a cleaner upstream diff on those two files the pre-revert form from 90f85c7 should be restored once upstream moves to Lean 4.29.
- **`cspell-words.txt` additions.** Task 8 of this plan claimed "no additions expected" in `cspell-words.txt`; in fact six tokens landed (`congr`, `hident`, `hrelab`, `hsum`, `noncomputable`, `recursivity`), driven by new prose in the narrative docstrings and book chapters. The assertion in Task 8 was wrong on arrival; treat the shipped list as the source of truth.
