# Branch Review: formalize/c-information-theoretic-primitives

Base: `main` (merge base: `d49fa96`)
Commits: 9
Files changed: 26 (12 added, 14 modified, 0 deleted, 0 renamed)
Reviewed through: `c88921f`

## Summary

The branch implements Phase C of the Shannon formalization roadmap: information-theoretic primitives. It adds five new library modules (`RelativeEntropy`, `MutualInfo`, `BinaryEntropy`, `FanoHelpers`, `Fano`), one new corollary in `Bits.lean` (`entropyBits_prodDist`), five `ShannonTest/Entropy/*` mirrors, three Verso book chapters, and synchronized roadmap, transcription, facade, and docs updates. Build, `lake test`, and `lake lint` all pass cleanly.

## Changes by Area

### Relative entropy (`Shannon/Entropy/RelativeEntropy.lean`, 245 insertions)

Defines `Supports q p`, `relEntropy`, `relEntropyBits`, proves `relEntropy_nonneg`, `relEntropyBits_nonneg`, `relEntropy_eq_zero_iff`, `relEntropy_self`, and the zero-total-friendly `log_sum_inequality`. The equality-characterization proof routes through Mathlib's `InformationTheory.klFun` (via `klFun_nonneg` / `klFun_eq_zero_iff`) rather than a bespoke `Real.log x = x - 1 ↔ x = 1` helper.

### Mutual information (`Shannon/Entropy/MutualInfo.lean`, 459 insertions)

Relocates `mutualInfo` from `Joint.lean`; adds `mutualInfoBits`, `condEntropyBits`, `swapJoint`, `diagonalDist`, `kernelPushforward`; proves the seven planned core identities (`nonneg`, `eq_relEntropy_prodMarginals`, `eq_zero_iff_independent`, `symm`, two chain-rule forms, `self`, `le_entropyFst/Snd`) plus their base-2 counterparts; proves the information-form DPI `mutualInfo_kernelPushforward_le` via the log-sum inequality (with `set_option maxHeartbeats 800000` locally scoped around the proof) and its bits counterpart.

### Binary entropy (`Shannon/Entropy/BinaryEntropy.lean`, 85 insertions)

Thin `binEntropyBits := Real.binEntropy / Real.log 2` wrapper with all planned lifted lemmas (`_zero`, `_one`, `_two_inv`, `_one_sub`, `_nonneg`, `_le_one`, `_eq_zero_iff`, `_continuous`) plus a private `_eq_negMulLog_pair` bridge.

### Fano's inequality (`Shannon/Entropy/Fano.lean`, 162 insertions; `FanoHelpers.lean`, 298 insertions)

`errorProb`, `rowErrorProb`, `condEntropy_swapJoint_le_qaryEntropy_errorProb`, and `fanoInequality`. Helpers: deterministic point distributions, `condDistFstGivenSnd`, row-wise decomposition of `condEntropy (swapJoint p)`, a point/complement split into `pointComplementFib`, and the one-row `q`-ary entropy bound `entropyNat_le_qaryEntropy_at_distinguished`. The final proof uses Mathlib's `Real.qaryEntropy` concavity via `strictConcaveOn_qaryEntropy.concaveOn.le_map_sum` (Jensen), together with `chain_rule` and `entropyNat_grouping` for the row decomposition.

### Base-2 corollary (`Shannon/Entropy/Bits.lean`, +13 / -1)

Adds `entropyBits_prodDist` exactly per the plan's suggested code pattern (`simp only [bridge]; rw [entropyNat_prodDist, add_div]`).

### Joint cleanup (`Shannon/Entropy/Joint.lean`, +0 / -8)

Removes the orphan `mutualInfo` definition now that it lives in `MutualInfo.lean`; module docstring's `mutualInfo` mention is gone.

### Tests

New `ShannonTest/Entropy/{RelativeEntropy, MutualInfo, BinaryEntropy, FanoHelpers, Fano}.lean`; `ShannonTest/Entropy.lean` aggregator updated; `ShannonTest/Entropy/Bits.lean` gains the `entropyBits_prodDist` example; `ShannonTest/Entropy/Joint.lean` drops the relocated `mutualInfo` example.

### Documentation and book

`Book.lean` and `Book/Introduction.lean` updated for reading order; three new Verso chapters (`MutualInformation`, `RelativeEntropy`, `FanoInequality`) written in the repo's long-single-line-paragraph style, with no `import Shannon` (book import discipline respected). Transcription cross-references added with the Theorem 7 forward-pointer as planned. Facade `Shannon/Entropy.lean` re-exports the four new public modules and updates the module-chain diagram. `AGENTS.md` module-layout gains five new bullets. `cspell-words.txt` picks up `binentropy`, `fiberwise`, `hcard`, `hchain`, `kernelpushforward`, `Kullback`, `Leibler`, `linarith`, `mutualinfo`, `pushforward`, `Pushforward`, `relabelings`, `relentropy`, `swapjoint`, `termwise`.

### Planning docs

`docs/plans/todo/2026-04-18-implement-phase-c.md` added (616 lines); parent roadmap updated to include `BinaryEntropy`, `Fano`, `FanoHelpers`.

## File Inventory

**New (12)**: `Shannon/Entropy/{RelativeEntropy, MutualInfo, BinaryEntropy, Fano, FanoHelpers}.lean`; `ShannonTest/Entropy/{RelativeEntropy, MutualInfo, BinaryEntropy, Fano, FanoHelpers}.lean`; `Book/{MutualInformation, RelativeEntropy, FanoInequality}.lean`; `docs/plans/todo/2026-04-18-implement-phase-c.md`.

**Modified (14)**: `AGENTS.md`, `Book.lean`, `Book/Introduction.lean`, `Shannon/Entropy.lean`, `Shannon/Entropy/Bits.lean`, `Shannon/Entropy/Joint.lean`, `ShannonTest/Entropy.lean`, `ShannonTest/Entropy/Bits.lean`, `ShannonTest/Entropy/Joint.lean`, `cspell-words.txt`, `docs/plans/todo/2026-04-14-shannon-proofs-roadmap.md`, `references/shannon1948-transcription.md`.

## Notable Changes

- New Mathlib dependency surface: `Mathlib.Analysis.SpecialFunctions.BinaryEntropy`, `Real.qaryEntropy`, `Real.strictConcaveOn_qaryEntropy`, `InformationTheory.klFun`. None require a Mathlib bump; all are already in the pinned v4.29.0 build.
- `set_option maxHeartbeats 800000` is locally scoped around `mutualInfo_kernelPushforward_le` and reset to `200000` immediately after.
- The DPI proof correctly keeps the zero-total case discharged by simplification rather than by demanding fiber positivity; this is the key robustness property called out in the plan.
- Fano correctly handles the `|α| = 1` edge case via a classical split on `Nonempty {x // x ≠ a0}` inside `entropyNat_le_qaryEntropy_at_distinguished`.

## Plan Compliance

**Compliance verdict: Good compliance, with one intentional proof-strategy deviation and one commit-strategy deviation.** Every planned deliverable lands; two tasks deviate from the plan's specific approach without changing the final statements.

**Overall progress: 8/8 tasks done (100%)**, with caveats noted below.

### Done items

- **Task 1** (`entropyBits_prodDist`): Implemented exactly as the plan's code sample; `Joint` import added; test example present.
- **Task 2** (RelativeEntropy + log-sum): All planned definitions and lemmas present. Log-sum stated in concave form with total-mass-zero case. Deviation: instead of a private `log_eq_sub_one_iff_of_pos` helper, the proof reuses Mathlib's `InformationTheory.klFun` machinery (`klFun_apply`, `klFun_nonneg`, `klFun_eq_zero_iff`). This is a strict reduction in local infrastructure and a reasonable deviation.
- **Task 3** (MutualInfo core): All seven core identities and their six planned base-2 counterparts exist; `swapJoint`, `diagonalDist`, their marginal and entropy identities all landed. One deviation: the marginal/entropy helpers on `swapJoint` and `diagonalDist` are exposed as public rather than private; this is consistent with the test mirror (they are exercised in `ShannonTest/Entropy/MutualInfo.lean`) and harmless.
- **Task 4** (DPI): `kernelPushforward`, both marginal identities (in the exact row-shape the plan locked in), `mutualInfo_kernelPushforward_le`, and `mutualInfoBits_kernelPushforward_le` all present; proof route follows the preferred log-sum path with the fiber-zero-friendly statement.
- **Task 5** (BinaryEntropy): Full planned lemma set plus the private `binEntropyBits_eq_negMulLog_pair` helper.
- **Task 6** (Fano): **Proof-strategy deviation.** The plan described an error-indicator-plus-chain-rule approach (`H(E, X | Y) = H(E | Y) + H(X | E, Y)` with `H(E | X, Y) = 0` because E is a function of X and Y). The landed proof instead decomposes `condEntropy (swapJoint p)` row-wise via `entropyNat_grouping` and `condDistFstGivenSnd`, bounds each row with `entropyNat_le_qaryEntropy_at_distinguished` (a point/complement split plus `entropyNat_le_log_card` on the complement), and averages via Jensen on `Real.qaryEntropy`. This leverages Mathlib's existing `Real.strictConcaveOn_qaryEntropy` and avoids building the three-variable-joint `(E, X, Y)` machinery the plan budgeted. The plan explicitly sanctions a fallback ("If the full error-indicator-plus-chain-rule proof of Fano proves awkward at the pinned Mathlib..."), so this is a reasonable, mathematically equivalent alternative. The final theorem statement matches the plan verbatim, including the `|α| = 1` edge case and the ℕ-cast shape.
- **Task 7** (Testing): All planned new test files exist; the aggregator is updated; the `mutualInfo` example has moved from `Joint.lean` to `MutualInfo.lean`. One minor scope addition: a new `ShannonTest/Entropy/FanoHelpers.lean` mirror file appears (not specified in the plan but consistent with the test-mirroring rule for a newly exposed public module).
- **Task 8** (Book, docs, facade): Three Verso chapters present with the right sectioning; `Book.lean` ordering matches plan; `Book/Introduction.lean` updated; transcription cross-refs added with the Theorem 7 forward-pointer; facade module-chain diagram updated (slightly simplified ASCII but equivalent); `AGENTS.md` layout updated; `cspell-words.txt` extended (with more words than just `relentropy` and `swapjoint`, all legitimate identifiers or prose words).

### Deviations

- **Fano proof strategy**: row-decomposition plus Jensen on `qaryEntropy` instead of error-indicator plus chain rule. **Reasonable**: allowed by the plan's fallback clause, avoids new entropy infrastructure, final statement is identical.
- **Commit strategy**: plan specified 8 commits with one per task (commit 5 "Split from commit 4 unconditionally: the log-sum reshape bookkeeping is the single largest proof in Phase C and deserves its own reviewable unit regardless of how cleanly it lands"). Actual history bundles `relEntropy` + `mutualInfo` + DPI + `binEntropyBits` into a single `feat(entropy): add KL, mutual information, and binary entropy` commit (`54ba9df`). Three follow-up commits (`8f61fe6` fix, `d6d75b7` lint, `c88921f` test strengthening) address polish. **Problematic**: this violates the plan's explicit "DPI gets its own commit unconditionally" directive, and the single landing commit is large enough to be hard to review. The branch is still coherent end-to-end, but the commit granularity is the clearest plan violation.
- **Public helpers on `swapJoint` / `diagonalDist`**: plan suggested keeping them private; landed version exposes them. **Reasonable**: test mirror exercises them; FanoHelpers uses `marginalFst_swapJoint` and `entropyNat_swapJoint`.
- **`ShannonTest/Entropy/FanoHelpers.lean`**: test-mirror for the helper module, not in the plan's test list. **Reasonable**: follows the test-mirroring rule for any publicly exposed module.

### Fidelity concerns

- The one item with lower fidelity to plan intent is the commit strategy. The plan's rationale ("the log-sum reshape bookkeeping is the single largest proof in Phase C and deserves its own reviewable unit") is not honored; DPI review would now require unpacking the large combined commit.
- `relEntropy_eq_zero_iff` test (`ShannonTest/Entropy/RelativeEntropy.lean:61`) is trivial (uses `uniformPNat 2` on both sides, so the biconditional reduces to `∀ a, x = x`). It technically mirrors the symbol but does not exercise the equality characterization on distinct distributions. Not a plan violation (plan did not spell out test content beyond "one example per exported symbol"), but a missed opportunity.

## Code Quality Assessment

**Overall quality: Ready to merge**, with small polish suggestions. The code is clean, the proofs are readable, Mathlib primitives are leveraged sensibly, and the entire pipeline (`make check`-equivalent: build + test + lint) is green.

### Strengths

- Heavy reliance on Mathlib's `InformationTheory.klFun`, `Real.binEntropy`, `Real.qaryEntropy`, and `strictConcaveOn_qaryEntropy` keeps local infrastructure small. The log-sum proof is a compact `calc` that reduces to `relEntropy_nonneg` on a normalized pair; the Fano row bound piggy-backs on existing entropy-is-bounded-by-log-card.
- `calc` blocks throughout the large proofs (`mutualInfo_eq_relEntropy_prodMarginals`, `mutualInfo_kernelPushforward_le`, `entropyNat_le_qaryEntropy_at_distinguished_of_nonempty_compl`) make the algebra legible rather than burying it in `simp` chains.
- The `set_option maxHeartbeats 800000` at `MutualInfo.lean:363` is bracketed and reset at line 455; no global heartbeat inflation.
- Public / private discipline is correct: proof bookkeeping (`pointDist`, `pointComplementFib`, `pointComplementEquiv`, `splitAtPointCond`, `splitAtPoint`, `sigmaProdEquiv`, `entropyNat_bool_eq_binEntropy`) is private; anything downstream code or tests consume is public.
- Correct edge-case handling: DPI's zero-fiber case, Fano's `|α| = 1` case, relative entropy's off-support terms, log-sum's `A = 0` case. Each is explicit rather than implicit.
- Tests include both structural symbol-mirror checks and concrete numeric anchors (`relEntropy (uniformPNat 2) quarterThreeQuarter = Real.log (4/3) / 2`, `binEntropyBits (1/2) = 1`, `errorProb (prodDist (uniformPNat 2) (uniformPNat 2)) id = 1/2`, `condEntropyBits (swapJoint ...) ≤ 1`).
- Verso chapters observe the book-import discipline (no `import Shannon`); paragraphs are single long lines per project convention.

### Issues to address (none blocking)

- `Shannon/Entropy/Fano.lean:143-145`: `hcast` is computed but never used inside `fanoInequality`; only `hcastInt` is consumed. Dead `have`. Minor; `lake lint` does not flag it, but removing it cleans the proof.
- `Shannon/Entropy/BinaryEntropy.lean:56`: `binEntropyBits_le_one (_hp₀ : 0 ≤ p) (_hp₁ : p ≤ 1)` uses underscore-prefixed parameters that are actually referenced in the proof body. The underscore prefix conventionally signals "parameter is unused"; here it is used. Rename to `hp₀`, `hp₁` for consistency with `binEntropyBits_nonneg` one line above.
- `Shannon/Entropy/MutualInfo.lean:65-69`: `marginalSnd_pos_of_prob_pos` is re-derived as a private helper here but is morally the twin of `marginalFst_pos_of_prob_pos` in `Joint.lean`. Consider lifting it to `Joint.lean` so the two marginal predicates live together.
- `ShannonTest/Entropy/RelativeEntropy.lean:61`: trivial biconditional test; would be more valuable to exercise on two distinct distributions (e.g., `uniformPNat 2` vs. `quarterThreeQuarter`).
- `Shannon/Entropy/MutualInfo.lean:392-393`: the DPI `simpa` hint list `[q, prodDist, marginalFst_kernelPushforward, marginalSnd_kernelPushforward, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]` is dense. This is load-bearing; consider a comment recording the reshape identity it resolves, so a future Mathlib bump that breaks the list has a reference.

### Suggestions (optional improvements)

- The `Shannon/Entropy.lean` facade docstring's module-chain diagram at lines 23-26 has slightly diverged from the plan's shape (the plan drew BinaryEntropy's mutual feed into Fano explicitly; the landed diagram notes it in prose). Both convey the dependency correctly; tightening the diagram is a cosmetic preference.
- The `_eq_negMulLog_pair` private helper in `BinaryEntropy.lean` appears unused at landing time (no caller in Phase C). Either delete it or mark the intended Phase D / E consumer in a comment.
- Next phase: consider auditing whether `mutualInfoBits_eq_relEntropyBits_prodMarginals` (base-2 form of `mutualInfo_eq_relEntropy_prodMarginals`) is worth adding to the public bits surface; Phase C does not need it, but Phase D channel-capacity work will.
