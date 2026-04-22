## Branch Review: formalize/phase-d-iid-aep-and-typical-sets

Base: `main` (merge base: `7c29b4a`)
Commits: 8
Files changed: 16 (7 added, 9 modified, 0 deleted, 0 renamed)
Reviewed through: `479449e`

### Summary

Phase D lands the i.i.d. special case of Shannon's Theorems 3 and 4. Two new Shannon modules (`IID.lean`, `AEP.lean`) introduce the product distribution `iidDist`, the base-2 typical set, N-fold entropy additivity, a finite Chebyshev helper, the AEP `aep_iid`, typical-set cardinality bounds, and the `minCover` asymptotic rate. Supporting changes add `entropyBits_relabelInvariant` to `Bits.lean`, a Verso companion chapter `Book/IIDAndAEP.lean`, mirrored test files, transcription cross-references for Theorems 3 and 4, roadmap / plan sync, and `cspell` vocabulary. `lake build`, `lake lint`, and `lake test` all pass on the branch head.

### Changes by Area

**Entropy library (new modules).** `Shannon/Entropy/IID.lean` (213 lines) defines `iidDist p N : ProbDist (Fin N → α)` by pointwise product, plus `iidDist_apply`, `iidDist_succ_relabel` (relabels `Fin (N+1) -> α` as a head-plus-tail pair via `Fin.consEquiv`), and the N-fold additivity identities `iidDist_entropyNat` and `iidDist_entropyBits`. It also introduces the per-symbol self-information `logProbBits`, the identity `sum_mul_logProbBits`, the support-restricted base-2 typical set `typicalSet`, and the pointwise typical-set bounds `iidDist_le_of_mem_typicalSet` and `iidDist_ge_of_mem_typicalSet`. `Shannon/Entropy/AEP.lean` (628 lines) builds a local `ProbDist -> PMF -> Measure` bridge (`probDistToPMF`, `probDist_integral_eq_sum`, `probDist_variance_eq_sum`, `iidDist_toMeasure_eq_pi`) so it can invoke Mathlib's `ProbabilityTheory.meas_ge_le_variance_div_sq` and `ProbabilityTheory.variance_sum_pi`. The public Phase D API on top of that bridge is `chebyshev_finite`, `aep_iid`, `typicalSet_iidDist_card_le`, `typicalSet_iidDist_card_ge`, `minCover`, and `tendsto_logb_minCover_iid`. Files: `Shannon/Entropy/IID.lean` (new), `Shannon/Entropy/AEP.lean` (new).

**Entropy library (feeder lemma).** `entropyBits_relabelInvariant` is added to `Bits.lean` as a one-line consequence of `entropyNat_relabelInvariant` via the bits / nats bridge; it is what the N-fold additivity induction relies on. Files: `Shannon/Entropy/Bits.lean`.

**Facade and module chain.** The `Shannon.Entropy` facade imports the two new modules, lists the new public API in its module docstring, and adds the Phase D row (`{Joint, Bits} -> IID -> AEP`) to the module-chain DAG. Files: `Shannon/Entropy.lean`.

**Tests.** `ShannonTest/Entropy/IID.lean` (new, 112 lines) mirrors every exported IID symbol with `example`-based regression tests, including a concrete `alternatingWord` membership check against the uniform two-letter typical set and `entropyBits (iidDist (uniformPNat 2) 4) = 4`. `ShannonTest/Entropy/AEP.lean` (new, 68 lines) mirrors the AEP surface and adds concrete `chebyshev_finite` and `aep_iid` / `typicalSet_iidDist_card_le` smoke tests on `uniformPNat 2`. `ShannonTest/Entropy/Bits.lean` gains an `entropyBits_relabelInvariant` example. The aggregator picks up both new modules. Files: `ShannonTest/Entropy.lean`, `ShannonTest/Entropy/Bits.lean`, `ShannonTest/Entropy/IID.lean` (new), `ShannonTest/Entropy/AEP.lean` (new).

**Companion book.** `Book/IIDAndAEP.lean` walks through the product distribution, per-symbol self-information, typical set, Theorem 3, Theorem 4, a numerical `(0.3, 0.7)` walk-through, and a forward pointer to Phase E. The chapter is wired into `Book.lean` between `FanoInequality` and `Bibliography`, and the reading-order list in `Book/Introduction.lean` is extended to include `Shannon/Entropy/{IID,AEP}.lean` and the new chapter title. The chapter respects the book import discipline: no `import Shannon` or `Shannon.*` module. Files: `Book.lean`, `Book/IIDAndAEP.lean` (new), `Book/Introduction.lean`.

**Documentation and metadata.** `references/shannon1948-transcription.md` gains Theorem 3 and Theorem 4 cross-reference bullets (explicitly flagged as the i.i.d. case with a Phase E forward pointer). `AGENTS.md` gains module-layout entries for `IID.lean` and `AEP.lean` and mentions the Phase D public API in the `entropyBits` paragraph. The roadmap (`docs/plans/todo/2026-04-14-shannon-proofs-roadmap.md`) status line is updated to mark Phase D shipped and its open `Real.logb` / `rpow` question resolved "no wrapper needed." The plan file `docs/plans/done/2026-04-21-implement-phase-d.md` was promoted from `todo/` to `done/` with a completion status and an implementation note that the landed proof uses a PMF / Measure bridge. `cspell-words.txt` gains 10 new terms (`aep`, `Exponentiating`, `iid`, `logprob`, `mincover`, `nhds`, `nonemptiness`, `typable`, `typicalset`, and case-distinguished already-present terms). Files: `AGENTS.md`, `cspell-words.txt`, `docs/plans/done/2026-04-21-implement-phase-d.md` (new), `docs/plans/todo/2026-04-14-shannon-proofs-roadmap.md`, `references/shannon1948-transcription.md`.

### File Inventory

**New (7):**

- `Book/IIDAndAEP.lean`
- `Shannon/Entropy/AEP.lean`
- `Shannon/Entropy/IID.lean`
- `ShannonTest/Entropy/AEP.lean`
- `ShannonTest/Entropy/IID.lean`
- `docs/plans/done/2026-04-21-implement-phase-d.md`

**Modified (9):**

- `AGENTS.md`
- `Book.lean`
- `Book/Introduction.lean`
- `Shannon/Entropy.lean`
- `Shannon/Entropy/Bits.lean`
- `ShannonTest/Entropy.lean`
- `ShannonTest/Entropy/Bits.lean`
- `cspell-words.txt`
- `docs/plans/todo/2026-04-14-shannon-proofs-roadmap.md`
- `references/shannon1948-transcription.md`

### Notable Changes

**Dependencies.** No new Lake dependencies. `Shannon/Entropy/AEP.lean` newly imports `Mathlib.Probability.ProbabilityMassFunction.Integrals`, `Mathlib.Probability.Moments.Variance`, and `Mathlib.MeasureTheory.Integral.Pi`, all of which were already transitively available via the pinned Mathlib v4.29.0. This is the first time the Shannon library reaches directly into Mathlib's measure-theoretic probability modules.

**Public API additions.** `iidDist`, `iidDist_apply`, `iidDist_succ_relabel`, `iidDist_entropyNat`, `iidDist_entropyBits`, `logProbBits`, `sum_mul_logProbBits`, `typicalSet`, `iidDist_le_of_mem_typicalSet`, `iidDist_ge_of_mem_typicalSet`, `entropyBits_relabelInvariant`, `chebyshev_finite`, `aep_iid`, `typicalSet_iidDist_card_le`, `typicalSet_iidDist_card_ge`, `minCover`, `tendsto_logb_minCover_iid`. No public API was removed or renamed.

**Upstream sync.** Phase D introduces two strictly new modules plus one feeder lemma in `Bits.lean`. The rest of the diff is additive (facade, docs, tests). No shared module was modified in a way that could conflict with upstream.

### Plan Compliance

**Verdict: strong compliance.** Every Phase D deliverable listed in the plan's `## Goal` section (items 1 through 6) has landed, with public API names that match the plan's target surface. All per-task verification tripwires pass (`lake build`, `lake test`, `lake lint`). The one substantive approach change (the Chebyshev helper uses a PMF / Measure bridge instead of the plan's direct `Finset.sum_le_sum`) is explicitly acknowledged in the plan's status line, so it is a recorded decision rather than an undisclosed deviation.

**Overall progress: 6/6 plan goals done (100%).**

**Done items:**

1. **Task 1 (I.i.d. product distribution and N-fold additivity, `Shannon/Entropy/IID.lean`).** `iidDist` is defined as `⟨fun x => ∏ i, p (x i), ...⟩` with the simplex proof routed through `Finset.prod_univ_sum` exactly as the plan proposed. `iidDist_apply`, `iidDist_succ_relabel` (using `Fin.consEquiv`), `iidDist_entropyNat` (induction on `N`, closing with `entropyNat_relabelInvariant`, `entropyNat_prodDist`, and the induction hypothesis), and `iidDist_entropyBits` (a two-rewrite consequence through the bits / nats bridge) all land. `logProbBits` and `sum_mul_logProbBits` are present. Implementation fidelity matches the plan.

2. **Task 1a (`entropyBits_relabelInvariant` feeder lemma in `Bits.lean`).** Landed as a one-line `simp only` + `rw [entropyNat_relabelInvariant]` proof, committed separately as `8123cb1 feat(entropy): add bits relabel invariance`. Plan-faithful.

3. **Task 2 (typical set and pointwise bounds, `Shannon/Entropy/IID.lean`).** `typicalSet` is defined as a `Finset.univ.filter` over the support-restricted epsilon-shell, matching the plan's statement. Both `iidDist_le_of_mem_typicalSet` and `iidDist_ge_of_mem_typicalSet` land with the exact signatures the plan specifies (though `hε : 0 < ε` was removed after the first-pass lint commit `2012b95`; see the Deviations section). The proofs route through `Real.logb_le_iff_le_rpow` and `Real.le_logb_iff_rpow_le` as planned.

4. **Task 3 (finite Chebyshev and `aep_iid`, `Shannon/Entropy/AEP.lean`).** `chebyshev_finite` lands with the plan's signature. The proof, however, differs in approach (see Deviations). `aep_iid` lands with the plan's signature, uses `chebyshev_finite` applied to the sample mean of `logProbBits`, and bounds the tail by `C / (N * eps^2)` with the explicit `N₀ := Nat.ceil (C / (delta * eps^2)) + 1`. The support condition is handled via `iidDist_eq_zero_of_off_support` plus `sum_typicalSet_eq_sum_goodShell` as the plan proposes.

5. **Task 4 (typical set cardinality bounds, `Shannon/Entropy/AEP.lean`).** Both `typicalSet_iidDist_card_le` (no large-`N` condition) and `typicalSet_iidDist_card_ge` (existential over `N ≥ N₀`) land with the plan's signatures. Proofs match the plan's description: upper bound via `sum mass ≤ 1` together with the pointwise lower bound; lower bound via `aep_iid` plus the pointwise upper bound.

6. **Task 5 (`minCover` and asymptotic rate, `Shannon/Entropy/AEP.lean`).** `minCover` is defined via `Nat.find` on `IsCoverCard`, with `minCover_exists`, `minCover_spec`, `minCover_le_card_of_mass_ge`, and `minCover_pos` as `private` helpers. `tendsto_logb_minCover_iid` lands with the exact `Tendsto` statement the plan specifies. The proof routes through `Metric.tendsto_atTop`, splits the epsilon ball into a typical-set tail (upper bound via `typicalSet_iidDist_card_le`) and a minimum-cover / typical-set intersection (lower bound via `iidDist_le_of_mem_typicalSet`), and absorbs the `Real.logb 2 (q - δ) / N` constant into the `η / 2` slack using `tendsto_const_div_atTop_nhds_zero_nat`.

7. **Task 6 (testing).** Both test files are present. `ShannonTest/Entropy/IID.lean` mirrors every exported IID symbol with `example`-based regressions, including the concrete `alternatingWord` / `uniformPNat 2` / `N = 4` / `ε = 1/10` typical-set membership check (the plan's preferred testing anchor) and two explicit `iidDist_entropyBits (uniformPNat 2) N = N` numerical tests. `ShannonTest/Entropy/AEP.lean` mirrors every exported AEP symbol, including a concrete `chebyshev_finite` on `uniformPNat 2` and concrete `aep_iid` / `typicalSet_iidDist_card_le` examples on `uniformPNat 2`. The aggregator `ShannonTest/Entropy.lean` imports both. `ShannonTest/Entropy/Bits.lean` gains the `entropyBits_relabelInvariant` example (Task 1a's mirror). Tests pass via `lake test`.

8. **Task 7 (book chapter, transcription, facade, documentation).** The book chapter is present and ordered between `FanoInequality` and `Bibliography`. The `Book.lean` include list and the `Book/Introduction.lean` reading-order list are updated. The transcription cross-references for Theorems 3 and 4 land with explicit "i.i.d. case" phrasing and a Phase E upgrade pointer. `Shannon/Entropy.lean` updates its public-API bullet list and adds a Phase D row to the module-chain diagram. `AGENTS.md` gains two module-layout bullets and extends the Phase C / D public API paragraph. `cspell-words.txt` covers the new vocabulary (checked by `make lint-spelling` implicitly through CI). The roadmap status line reflects Phase D shipped, and the open `Real.logb` / `Real.rpow` question is resolved in the "native Mathlib sufficed, no wrapper" direction.

**Deviations:**

1. **Approach deviation (Chebyshev helper).** The plan's Observation 3 argues for a self-contained Chebyshev proof ("direct `Finset.sum_le_sum` argument", "≈ 25 lines") to avoid the Mathlib measure-theoretic detour. The landed `chebyshev_finite` does the opposite: it wraps `ProbDist α` as a `PMF α`, pushes that forward to a `Measure α` via `PMF.toMeasure`, and invokes `ProbabilityTheory.meas_ge_le_variance_div_sq`. The plan's status line (written after-the-fact when the plan moved to `done/`) acknowledges this: "the landed AEP proof uses a small `ProbDist -> PMF/Measure` bridge to reuse Mathlib's variance and Chebyshev lemmas." Assessment: the deviation is reasonable. Reusing the measure-theoretic lemma also supplies `variance_sum_pi` for the i.i.d. variance scaling in `iidDist_variance_logProb_bound`, which would otherwise need a bespoke cross-term cancellation proof. The adapter overhead (`probDistToPMF`, `probDist_integral_eq_sum`, `probDist_variance_eq_sum`, `iidDist_toMeasure_eq_pi`) is concentrated in about 40 lines at the top of `AEP.lean` and is entirely `private`. Net cost: `AEP.lean` imports three extra Mathlib modules it otherwise would not; the public API is identical.

2. **Signature deviation (pointwise typical-set bounds drop `hε : 0 < ε`).** The plan's Task 2 signatures list `(hε : 0 < ε)` for both `iidDist_le_of_mem_typicalSet` and `iidDist_ge_of_mem_typicalSet`. The landed signatures omit it: `|sampleMean - entropyBits p| < ε` already forces `0 < ε` when the filter is non-empty, so the hypothesis was redundant. The redundant hypothesis was removed in commit `2012b95 chore(lint): remove unused phase d hypotheses`. Assessment: correct simplification. Downstream callers (e.g. `tendsto_logb_minCover_iid`) compensate by constructing `hε` locally where they need it.

3. **Approach deviation (`minCover` instance machinery).** The plan suggests `Nat.find` with a note that a `Classical.choose` fallback is acceptable if the decidability chain gets painful. The landed code uses `Nat.find` but bundles the decidability resolution inside a `by classical; ...; letI : DecidablePred P := Classical.decPred P; exact Nat.find ...` block. Assessment: matches the intent; keeping the `Nat.find` form preserves the stronger "minimum" statement while routing the decidability through `Classical.decPred`. The resulting `minCover` is `noncomputable` (the whole module is), as the plan's fallback permitted.

4. **Scope addition (`sum_not_typicalSet_le` helper).** An extra `private` lemma in `AEP.lean` bounds the `Finset.filter (fun x => x ∉ typicalSet ...)` tail by `δ`. Not listed in the plan, but it is a natural factoring of the tail estimate needed inside `tendsto_logb_minCover_iid` and would otherwise have been inlined. Assessment: reasonable refactor, not scope creep.

5. **Scope addition (`sampleMeanLogProbBits`, `goodShell`, `badShell` private aliases).** Not in the plan. They localize the names for the `(1/N) * ∑ logProbBits ...` expression and its epsilon / not-epsilon filter variants. Assessment: readability improvement; the typical set is the `support ∧ goodShell` intersection and the AEP bound is `mass(badShell) ≤ δ`.

**Fidelity concerns:**

1. **`Real.logb` / `Real.rpow` ergonomics open question.** The plan's Task 5 designates this proof as the stress test. The landed `tendsto_logb_minCover_iid` closes the proof using native Mathlib `Real.logb_mul`, `Real.logb_rpow`, `Real.rpow_add`, and `ring_nf` without a wrapper namespace. The roadmap's open-question entry is updated accordingly: "Resolved during execution: Mathlib's native `Real.logb` and `Real.rpow` lemmas were sufficient for Phase D. No wrapper namespace was needed." Intent matched.

2. **Variance-scaling proof (`iidDist_variance_logProb_bound`).** The plan permits either a direct cross-term argument or a `C / N` weakening. The landed proof routes `Var(Y̅_N) = Var(Y) / N` through `ProbabilityTheory.variance_sum_pi` applied to the i.i.d. `Measure.pi`, which is strictly stronger than the `≤ C / N` weakening: it gives the exact equality and therefore the exact Chebyshev rate. Intent is met (and exceeded).

3. **Support restriction ergonomics on full-support `p`.** The plan's Task 2 note asks that on a full-support `p` (e.g. `uniformPNat`), `typicalSet` equals the filter that drops the support conjunct. The landed `uniform_two_typicalSet_eq_univ` test lemma in `ShannonTest/Entropy/IID.lean` confirms this empirically on `uniformPNat 2`; no explicit `typicalSet_of_fullSupport` convenience lemma was added. Assessment: the test coverage is adequate for Phase D's purposes; adding a named lemma would be premature abstraction until Phase E or another consumer needs it.

### Code Quality Assessment

**Verdict: ready to merge.** The code is well-organized, the proofs are structured for readability, `private` is used defensively to keep adapter lemmas out of the public API, the docstrings follow the project's single-long-line convention, and the test surface mirrors the public API one example per symbol. The build, lint, and test targets all pass. The two areas below are refinements worth considering but not blockers.

**Strengths:**

1. **Thorough `private` scoping.** `probDistToPMF`, `probDist_integral_eq_sum`, `probDist_variance_eq_sum`, `iidDist_toMeasure_eq_pi`, `iidDist_pos_of_pos`, `logb_iidDist_apply_eq_sum`, `logb_iidDist_apply_eq_neg_sum_logProbBits`, `iidDist_eq_zero_of_off_support`, `exists_zero_of_not_fullSupport`, `sum_typicalSet_eq_sum_goodShell`, `sum_goodShell_add_sum_badShell`, `iidDist_sum_apply_sample`, `iidDist_sampleMean_eq_entropyBits`, `memLp_logProbBits`, `iidDist_variance_logProb_bound`, `IsCoverCard`, `minCover_exists`, `minCover_spec`, `minCover_le_card_of_mass_ge`, `minCover_pos`, and `sum_not_typicalSet_le` are all private. This keeps the public surface clean and focused on the plan's target API.

2. **Structured calc proofs.** `iidDist`'s simplex proof, `iidDist_sum_apply_sample`, `iidDist_sampleMean_eq_entropyBits`, and the cardinality bounds in `typicalSet_iidDist_card_le` / `typicalSet_iidDist_card_ge` use `calc` blocks that read top-to-bottom as informal proofs. The shape matches Shannon's paper closely.

3. **`Real.rpow` discipline.** Every `2 ^ x` where `x : ℝ` is `Real.rpow 2 x`; the positivity side condition `(by positivity : 0 < (2 : ℝ))` is supplied uniformly. The bookkeeping would be easy to get wrong; the landed code is consistent.

4. **Test regressions.** Both new test files include concrete numerical checks (on `uniformPNat 2` with explicit `N`, `ε`, and `δ`) in addition to the per-symbol `example` mirrors, matching the test discipline established in Phase C.

5. **Docstrings.** Module docstrings list main definitions, main results, and references (Shannon 1948 Section 7, Cover and Thomas Chapter 3) consistent with the Phase B / C template. Theorem docstrings are concise single-sentence descriptions.

**Issues to address:**

1. **(Minor) `@[nolint unusedArguments]` on `typicalSet` and the pointwise bounds.** `Shannon/Entropy/IID.lean:105`, `:137`, `:174` all carry `@[nolint unusedArguments]` attributes. For `typicalSet`, every argument (`α`, `Fintype α`, `p`, `N`, `ε`) is used in the body, so the attribute appears unnecessary. For `iidDist_le_of_mem_typicalSet` and `iidDist_ge_of_mem_typicalSet`, the hypothesis `hε : 0 < ε` was removed in commit `2012b95`, and the remaining signature looks fully used (`p`, `N`, `ε`, `x`, `hx` all feature in the proof). Both attributes read as leftovers from earlier drafts. Suggest removing them and running `lake lint` to confirm no linter complaint returns; if it does, a one-line comment would help a future reader understand why the attribute is retained.

2. **(Minor) `@[reducible] local instance instMeasurableSpace_shannon`.** `Shannon/Entropy/AEP.lean:42` names a local measurable-space instance `instMeasurableSpace_shannon`. The `_shannon` suffix is unusual: instance names in Lean typically follow `instClassForType` camel case (e.g. `instMeasurableSpaceFin`). Suggest `instDiscreteMeasurableSpace` or simply leaving it anonymous (`local instance : MeasurableSpace α := ⊤`). Not blocking.

3. **(Minor) `have _ := hq₀` inside `minCover`.** `Shannon/Entropy/AEP.lean:420` uses `have _ := hq₀` to silence an unused-variable complaint while keeping `hq₀ : 0 < q` in the public signature. A comment explaining that the hypothesis is part of the intended public contract (per the plan's Open Questions section) would help a future reader understand why a positivity hypothesis is carried through without being consumed.

**Suggestions:**

1. **Consider hoisting `probDistToPMF` to a shared helper.** The `ProbDist -> PMF -> Measure` bridge in `Shannon/Entropy/AEP.lean:44-56` is marked `private`. If Phase E or any later consumer (entropy-rate, channel coding, etc.) wants to reuse Mathlib's measure-theoretic probability lemmas, this bridge is the natural reusable piece. Leaving it `private` in `AEP.lean` is fine for now (YAGNI), but it is worth mentioning in the Phase D retrospective so Phase E knows where to find it.

2. **Consider a named `typicalSet_of_fullSupport` lemma.** The test `uniform_two_typicalSet_eq_univ` in `ShannonTest/Entropy/IID.lean:41` re-derives the fact that on `uniformPNat 2` the support restriction is vacuous. If this pattern shows up again (it probably will, in Phase E book examples and in any channel-coding chapter), hoisting a named `typicalSet_of_fullSupport` lemma into `Shannon/Entropy/IID.lean` would clean up the test. Not needed until the second consumer appears.

3. **Consider an absolute value import check.** `chebyshev_finite` and the typical-set definition both use `|·|` on `ℝ`, which is `abs`. Inside `aep_iid`, the rewriting through `abs_lt.mp` and `abs_of_nonneg` works as expected, but the module imports go through `Shannon.Entropy.IID -> Shannon.Entropy.Bits`, which transitively pulls `Mathlib.Algebra.Order.AbsoluteValue`. No current issue, but worth being aware of if the import chain ever gets restructured.
