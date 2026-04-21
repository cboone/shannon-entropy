# 2026-04-18 Phase C: information-theoretic primitives

Date: 2026-04-18
Status: Draft. Targets Phase C of `docs/plans/todo/2026-04-14-shannon-proofs-roadmap.md`. Branch `formalize/c-information-theoretic-primitives` off `main` at `c98be16`.

## Context

Phase B shipped on 2026-04-18 (`chore/implement-phase-b`, merged as commit `c98be16`). The library now exposes a base-2 public API (`entropyBits`) alongside the natural-log internal workhorse (`entropyNat`), with bridge lemmas, base-2 uniqueness, and a Shannon-form restatement of conditional entropy (`condEntropy_eq_shannon_form`). The companion Verso book now has three walkthrough chapters (`AxiomaticEntropy`, `Properties`, `Logarithm`) covering Appendix 2 plus Section 6 Properties 1-6.

Phase C adds the information-theoretic primitives layer: mutual-information properties, relative entropy (KL divergence), the log-sum inequality, the information form of the data processing inequality, and Fano's inequality. All new statements are base-2 via `entropyBits`; natural-log variants surface only where a proof wants them internally. These primitives unblock Phase D (`iidDist`, AEP, typical sets in bits) and round out Shannon's Section 6 by completing the Gibbs-inequality toolkit into its standard textbook shape.

Three observations from the current code that shape Phase C:

- `mutualInfo` is already defined in `Shannon/Entropy/Joint.lean` (`entropyNat (marginalFst p) + entropyNat (marginalSnd p) - entropyNat p`), but no theorems about it exist yet. `ShannonTest/Entropy/Joint.lean` has a single example `mutualInfo (prodDist (uniformPNat 2) (uniformPNat 1)) = 0`. Phase C relocates the definition into the new `MutualInfo.lean` module and migrates the test to the matching `ShannonTest/Entropy/MutualInfo.lean`. The facade keeps the name reachable via `import Shannon.Entropy`, so library consumers continue to see `mutualInfo` with no breakage.
- `gibbs_inequality` in `Shannon/Entropy/Gibbs.lean` uses the support hypothesis `∀ a, 0 < p a → 0 < q a` inline. Phase C lifts this to a named predicate `Supports q p` in the new `RelativeEntropy.lean` module so the KL theorems have a stable, searchable hypothesis. The existing unnamed form of `gibbs_inequality` stays; a new `relEntropy_nonneg` restates the same content in "KL is nonnegative" shape.
- Mathlib already ships `Real.binEntropy` (`Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean`) in nats, with `binEntropy_zero`, `binEntropy_one`, `binEntropy_two_inv = log 2`, `binEntropy_nonneg`, `binEntropy_le_log_two`, `binEntropy_strictMonoOn`/`binEntropy_strictAntiOn`, and `strictConcave_binEntropy`. Phase C's `binEntropyBits` is a thin base-2 wrapper (`Real.binEntropy p / Real.log 2`); we lift the Mathlib lemmas into bits rather than re-proving them.

Single-phase design caveat recorded in the roadmap (`Chapters under Book/ must not import Shannon or any Shannon.* module`): every new Phase C book chapter continues to reference Lean identifiers by backticks only, with no direct `import Shannon`. Lake still links every transitive C object on the `generate-book` argv, and pulling Mathlib through `Shannon` would push the macOS command line past `ARG_MAX`.

## Goal

Deliver seven things in one branch:

1. `entropyBits_prodDist`: a one-line base-2 corollary of `entropyNat_prodDist`, closing the Phase B review's note about a natural follow-up lemma in `Shannon/Entropy/Bits.lean`.
2. A new `Shannon/Entropy/RelativeEntropy.lean` module: `Supports` predicate, `relEntropy` / `relEntropyBits` definitions, `relEntropy_nonneg`, `relEntropy_eq_zero_iff`, and the log-sum inequality.
3. A new `Shannon/Entropy/MutualInfo.lean` module: the `mutualInfo` definition (relocated from `Joint.lean`), the six identities the roadmap lists (`nonneg`, `eq_zero_iff_independent`, `symm`, `eq_entropy_sub_condEntropy` and its dual, `self`, `le_entropy`), their `mutualInfoBits` counterparts, the `swapJoint` helper used by `mutualInfo_symm`, and a `diagonalDist` helper used by `mutualInfo_self`.
4. The information form of the data processing inequality for a Markov chain `X → Y → Z` via a kernel `W : β → ProbDist γ`, in `MutualInfo.lean`. Proof via the zero-total-friendly log-sum inequality from Task 2, so the pointwise `(a, c)` application still works when a fiber mass vanishes.
5. A new `Shannon/Entropy/BinaryEntropy.lean` module: `binEntropyBits p := Real.binEntropy p / Real.log 2` plus bits-flavored versions of the Mathlib binary-entropy lemmas (`_zero`, `_one`, `_two_inv_eq_one`, `_nonneg`, `_le_one`, continuity, symmetry).
6. A new `Shannon/Entropy/Fano.lean` module: Fano's inequality in bits, stated as a bound on `condEntropyBits (swapJoint p)` in terms of `binEntropyBits Pe` and `Pe * Real.logb 2 (Fintype.card α - 1)` where `Pe` is the error probability of an estimator `f : β → α`. Budget the proof against nested-pair encodings of `(E, X, Y)` and explicitly spin out `Shannon/Entropy/FanoHelpers.lean` if the relabel / conditioning helper block stops being small and local.
7. Three new Verso chapters (`MutualInformation`, `RelativeEntropy`, `FanoInequality`) covering the new primitives in narrative form, plus the corresponding test additions, transcription cross-reference updates, roadmap-sync edits, and facade edits.

Non-goals (reserved for Phase D+):

- i.i.d. product distributions, typical sets, AEP (Phase D).
- Finite-state statistical sources, entropy-rate theorems, transducer-form DPI (Phase E).
- Continuous / differential entropy, channel capacity (Phase F, out of scope).

## Tasks

### 1. `entropyBits_prodDist` corollary in `Bits.lean`

Close the Phase B review's call-out (`docs/reviews/2026-04-18-chore-implement-phase-b.md`, final "Suggestions" bullet). Add to `Shannon/Entropy/Bits.lean`, after `entropyBits_le_logb_two_card`:

```lean
/-- Additivity for independent distributions in bits: `entropyBits (prodDist p q) = entropyBits p + entropyBits q`.

Base-2 counterpart of `entropyNat_prodDist`, obtained by dividing the natural-log identity by `Real.log 2`. -/
theorem entropyBits_prodDist
    {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist α) (q : ProbDist β) :
    entropyBits (prodDist p q) = entropyBits p + entropyBits q := by
  simp only [entropyBits_eq_entropyNat_div_log_two]
  rw [entropyNat_prodDist, add_div]
```

Using `simp only` for the bridge rewrite avoids fragility from occurrence ordering when later edits reshape the right-hand side.

This pulls `Joint.lean` into `Bits.lean`'s transitive import closure (currently `Bits` imports `Gibbs` which imports `Final → Approx → Rational → Uniform`; it does not pick up `Joint`). Update the `import` line to `import Shannon.Entropy.Joint` (which itself imports `Gibbs`, so the existing import chain stays intact).

Module docstring "Main results" list: add a bullet `- entropyBits_prodDist: base-2 counterpart of entropyNat_prodDist on product distributions`.

Tests: add a single `example` to `ShannonTest/Entropy/Bits.lean`, mirroring the existing `entropyNat_prodDist` example in `ShannonTest/Entropy/Joint.lean`:

```lean
example :
    entropyBits (prodDist (uniformPNat 2) (uniformPNat 3))
      = entropyBits (uniformPNat 2) + entropyBits (uniformPNat 3) :=
  entropyBits_prodDist (uniformPNat 2) (uniformPNat 3)
```

### 2. Relative entropy and the log-sum inequality (`RelativeEntropy.lean`)

Create `Shannon/Entropy/RelativeEntropy.lean`. Imports: `Shannon.Entropy.Bits` (for `entropyBits` bridge plus the transitively available `gibbs_inequality`).

Module structure:

```lean
import Shannon.Entropy.Bits

namespace Shannon

noncomputable section
open Finset Real
```

Definitions:

```lean
/-- `Supports q p` asserts that `q` covers the support of `p`: whenever `p a > 0`, also `q a > 0`. The standard finite-alphabet support predicate for KL divergence and Gibbs-style inequalities. -/
def Supports {α : Type} [Fintype α] (q p : ProbDist α) : Prop :=
  ∀ a, 0 < p a → 0 < q a

/-- Relative entropy (Kullback-Leibler divergence) in nats: `D(p ‖ q) = ∑ p_i log (p_i / q_i)`.

Defined as a total function. The value is mathematically meaningful only when `q` covers the support of `p` (`Supports q p`); Lean's conventions `Real.log 0 = 0` and `0 / 0 = 0` keep the expression finite even outside support, but theorems below require the support hypothesis. -/
def relEntropy {α : Type} [Fintype α] (p q : ProbDist α) : ℝ :=
  ∑ a, p a * Real.log (p a / q a)

/-- Base-2 relative entropy (KL divergence in bits). -/
def relEntropyBits {α : Type} [Fintype α] (p q : ProbDist α) : ℝ :=
  relEntropy p q / Real.log 2
```

Core lemmas:

- Private helper `relEntropy_eq_neg_gibbs_sum`:
  `relEntropy p q = -∑ a, p a * Real.log (q a / p a)` on support. Proof: termwise `p_a * log (p_a / q_a) = -p_a * log (q_a / p_a)` using `Real.log_div`; off-support terms vanish because `p_a = 0`.
- `relEntropy_nonneg (hsupp : Supports q p)`: `0 ≤ relEntropy p q`. Proof: rewrite via `relEntropy_eq_neg_gibbs_sum`, apply `gibbs_inequality p q hsupp`, negate.
- `relEntropyBits_nonneg`: same for bits. Proof: divide by `Real.log 2 > 0`.
- `relEntropy_eq_zero_iff (hsupp : Supports q p)`: `relEntropy p q = 0 ↔ ∀ a, p a = q a`. Proof: use the strict form of `Real.log x ≤ x - 1` (equality iff `x = 1`) applied termwise. Expansion:

  ```lean
  theorem relEntropy_eq_zero_iff
      {α : Type} [Fintype α] (p q : ProbDist α) (hsupp : Supports q p) :
      relEntropy p q = 0 ↔ ∀ a, p a = q a := by
    classical
    -- forward: each term ≥ 0 by Gibbs; equality forces p a = q a on support;
    -- off-support p a = 0, and Supports q p plus ∑ q = 1 = ∑ p gives q a = 0 too.
    ...
  ```

  Use `Real.log_eq_sub_iff_of_pos` (or equivalent: `Real.log x = x - 1 ↔ x = 1` for `x > 0`, easy from `Real.log_le_sub_one_of_pos` combined with the `Real.add_one_le_exp` direction) to pin each positive term. For the `Supports` bookkeeping, note that `∑ p a - ∑ q a = 0` combined with pointwise `p a ≤ q a` forces equality everywhere.

  Grep `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/` for the current canonical name before writing the proof. Budget a private helper lemma `private lemma log_eq_sub_one_iff_of_pos {x : ℝ} (hx : 0 < x) : Real.log x = x - 1 ↔ x = 1` as part of Task 2 unless the pinned Mathlib already ships an equivalent under another name. Do not treat this helper as an optional fallback discovered late in the proof.

- `relEntropy_self`: `relEntropy p p = 0`. Proof: each term is `p a * log 1 = 0`.

Log-sum inequality:

```lean
/-- **Log-sum inequality**: for nonneg sequences `a, b : α → ℝ` with `A = ∑ aᵢ`, `B = ∑ bᵢ`, and support condition `∀ i, 0 < aᵢ → 0 < bᵢ`:
    ∑ i, a i * log (a i / b i) ≥ A * log (A / B).

The statement is total: if `A = 0`, both sides are `0`; if `A > 0`, the support hypothesis forces `B > 0`, so the normalized probability-distribution proof applies. Equality holds iff the sequences are proportional (a i / b i is constant on support). -/
theorem log_sum_inequality
    {α : Type} [Fintype α]
    (a b : α → ℝ)
    (ha_nonneg : ∀ i, 0 ≤ a i) (hb_nonneg : ∀ i, 0 ≤ b i)
    (hsupp : ∀ i, 0 < a i → 0 < b i) :
    (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) ≤
      ∑ i, a i * Real.log (a i / b i) := by
  ...
```

Proof strategy: split on `A = ∑ i, a i`.

- If `A = 0`, use `Finset.sum_eq_zero_iff_of_nonneg` and `ha_nonneg` to show `a i = 0` for every `i`, so both sides are `0` by simplification.
- If `A > 0`, first show `B = ∑ i, b i > 0`: choose `i` with `0 < a i` from the positive total, then apply `hsupp`; now normalize to the probability-distribution case. Let `p := a / A`, `q := b / B` (as `ProbDist α`); then the log-sum inequality reduces to `relEntropy_nonneg` applied to `(p, q)` with support `Supports q p` inherited from `hsupp`.

Concretely:

```text
∑ a_i log(a_i / b_i)
  = ∑ A · p_i · log(A · p_i / (B · q_i))
  = A · ∑ p_i · (log(p_i / q_i) + log(A / B))
  = A · relEntropy p q + A · log(A / B).
```

Since `relEntropy p q ≥ 0`, we get `∑ a_i log(a_i / b_i) ≥ A · log(A / B)`.

Leave the equality case out of Phase C even though the statement above mentions it informally; DPI and Fano only need the inequality, and the zero-total generalization is the proof-critical part for this phase.

`RelativeEntropy.lean` module docstring structure (top of file) follows the Phase B `Bits.lean` style: `# Shannon.Entropy.RelativeEntropy`, one-paragraph overview, "Main definitions" list (`Supports`, `relEntropy`, `relEntropyBits`), "Main results" list (`relEntropy_nonneg`, `relEntropy_eq_zero_iff`, `log_sum_inequality`).

### 3. Mutual information (`MutualInfo.lean`)

Create `Shannon/Entropy/MutualInfo.lean`. Imports: `Shannon.Entropy.Properties` (brings `Joint`, `Gibbs`, and the subadditivity / conditioning lemmas) and `Shannon.Entropy.RelativeEntropy` (for `relEntropy` and `relEntropy_eq_zero_iff`, used by the independence characterization).

Remove the `mutualInfo` definition from `Shannon/Entropy/Joint.lean`. Move it verbatim to `MutualInfo.lean`. Joint's module docstring loses the `mutualInfo` bullet; `MutualInfo.lean`'s module docstring gains a new "Main definitions" list headed by `mutualInfo`. The `Shannon.Entropy` facade continues to re-export `mutualInfo` via the new `import Shannon.Entropy.MutualInfo`.

New helpers in `MutualInfo.lean`:

```lean
/-- Swap the coordinates of a joint distribution. Implemented via `relabelProb Equiv.prodComm`. -/
def swapJoint {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist (α × β)) : ProbDist (β × α) :=
  relabelProb (Equiv.prodComm α β) p

/-- Diagonal distribution: `(diagonalDist p)(a, a') = if a = a' then p a else 0`. Used to state `mutualInfo_self`. -/
def diagonalDist {α : Type} [Fintype α] [DecidableEq α]
    (p : ProbDist α) : ProbDist (α × α) := by
  refine ⟨fun ab => if ab.1 = ab.2 then p ab.1 else 0, ?_⟩
  constructor
  · intro ab; split_ifs
    · exact prob_nonneg p _
    · exact le_refl _
  · -- ∑ (a, b), (if a = b then p a else 0) = ∑ a, p a = 1
    rw [Fintype.sum_prod_type]
    simp_rw [Finset.sum_ite_eq Finset.univ _ fun a => p a]
    simp [prob_sum_eq_one p]
```

The inner sum `∑ b, if a = b then p a else 0` has bound variable `b` on the right of the equality (`a = b`), which matches `Finset.sum_ite_eq` (not the primed variant `Finset.sum_ite_eq'`, which requires the bound variable on the left of the equality). Verify the invocation against the pinned Mathlib during implementation — both variants exist with subtly different orientations and the choice depends on how `Fintype.sum_prod_type` normalizes the outer / inner bound-variable names.

Private supporting identities on the helpers (keep these local unless downstream code needs them on the public API):

- `marginalFst_swapJoint : marginalFst (swapJoint p) = marginalSnd p`. Proof: unfold `swapJoint`, `relabelProb`, `Equiv.prodComm`; sum over β rearranges to marginalSnd.
- `marginalSnd_swapJoint : marginalSnd (swapJoint p) = marginalFst p`. Dual.
- `entropyNat_swapJoint : entropyNat (swapJoint p) = entropyNat p`. Follows from `entropyNat_relabelInvariant` (already in `Converse.lean`).
- `marginalFst_diagonalDist : marginalFst (diagonalDist p) = p`. Proof: `∑ b, if a = b then p a else 0 = p a` via `Finset.sum_ite_eq` (see orientation note above).
- `marginalSnd_diagonalDist : marginalSnd (diagonalDist p) = p`. Dual.
- `entropyNat_diagonalDist : entropyNat (diagonalDist p) = entropyNat p`. Proof: the joint sum restricts to the diagonal; `Finset.sum_ite_eq` inside `Fintype.sum_prod_type`.

Core theorems (`H` is `entropyNat`):

```lean
/-- **Mutual information is nonnegative**: `0 ≤ I(X; Y)`. Immediate from subadditivity `entropyNat_joint_le_add`. -/
theorem mutualInfo_nonneg
    {α β : Type} [Fintype α] [Fintype β] (p : ProbDist (α × β)) :
    0 ≤ mutualInfo p := by
  unfold mutualInfo
  linarith [entropyNat_joint_le_add p]

/-- **Mutual information equals KL to the product of marginals**:
    I(X;Y) = D(p ‖ marginalFst p × marginalSnd p). -/
theorem mutualInfo_eq_relEntropy_prodMarginals
    {α β : Type} [Fintype α] [Fintype β] (p : ProbDist (α × β)) :
    mutualInfo p = relEntropy p (prodDist (marginalFst p) (marginalSnd p)) := by
  ...  -- pointwise: log (p(a,b) / (mFst a * mSnd b)) = log p - log mFst - log mSnd

/-- **Mutual information is zero iff X and Y are independent**: combines `mutualInfo_eq_relEntropy_prodMarginals` with `relEntropy_eq_zero_iff`. -/
theorem mutualInfo_eq_zero_iff_independent
    {α β : Type} [Fintype α] [Fintype β] (p : ProbDist (α × β)) :
    mutualInfo p = 0 ↔ IsIndependent p := by
  rw [mutualInfo_eq_relEntropy_prodMarginals]
  constructor
  · intro h
    -- relEntropy_eq_zero_iff needs Supports (prodDist marginals) p, which holds
    -- by marginalFst/Snd_pos_of_prob_pos.
    have hsupp : Supports (prodDist (marginalFst p) (marginalSnd p)) p := ...
    exact (relEntropy_eq_zero_iff p _ hsupp).mp h
  · intro hind
    -- p = prodDist (marginalFst p) (marginalSnd p) pointwise, so relEntropy_self gives zero.
    ...

/-- **Symmetry**: `I(X;Y) = I(Y;X)`. -/
theorem mutualInfo_symm
    {α β : Type} [Fintype α] [Fintype β] (p : ProbDist (α × β)) :
    mutualInfo p = mutualInfo (swapJoint p) := by
  unfold mutualInfo
  rw [marginalFst_swapJoint, marginalSnd_swapJoint, entropyNat_swapJoint]; ring

/-- **Chain-rule identity**: `I(X;Y) = H(X) - H(X|Y)`. Here `H(X|Y) = condEntropy (swapJoint p)`. -/
theorem mutualInfo_eq_entropyFst_sub_condEntropy_swap
    {α β : Type} [Fintype α] [Fintype β] (p : ProbDist (α × β)) :
    mutualInfo p =
      entropyNat (marginalFst p) - condEntropy (swapJoint p) := by
  have hchain := chain_rule (swapJoint p)
  rw [marginalFst_swapJoint, entropyNat_swapJoint] at hchain
  unfold mutualInfo; linarith

/-- **Chain-rule identity, dual**: `I(X;Y) = H(Y) - H(Y|X)`. -/
theorem mutualInfo_eq_entropySnd_sub_condEntropy
    {α β : Type} [Fintype α] [Fintype β] (p : ProbDist (α × β)) :
    mutualInfo p = entropyNat (marginalSnd p) - condEntropy p := by
  have hchain := chain_rule p
  unfold mutualInfo; linarith

/-- **Self mutual information**: `I(X;X) = H(X)`. -/
theorem mutualInfo_self
    {α : Type} [Fintype α] [DecidableEq α] (p : ProbDist α) :
    mutualInfo (diagonalDist p) = entropyNat p := by
  unfold mutualInfo
  rw [marginalFst_diagonalDist, marginalSnd_diagonalDist, entropyNat_diagonalDist]; ring

/-- **MI bounded by marginal entropy (first)**: `I(X;Y) ≤ H(X)`. -/
theorem mutualInfo_le_entropyFst
    {α β : Type} [Fintype α] [Fintype β] (p : ProbDist (α × β)) :
    mutualInfo p ≤ entropyNat (marginalFst p) := by
  rw [mutualInfo_eq_entropyFst_sub_condEntropy_swap]
  linarith [condEntropy_nonneg (swapJoint p)]

/-- **MI bounded by marginal entropy (second)**: `I(X;Y) ≤ H(Y)`. -/
theorem mutualInfo_le_entropySnd
    {α β : Type} [Fintype α] [Fintype β] (p : ProbDist (α × β)) :
    mutualInfo p ≤ entropyNat (marginalSnd p) := by
  rw [mutualInfo_eq_entropySnd_sub_condEntropy]
  linarith [condEntropy_nonneg p]
```

Base-2 counterparts:

```lean
/-- Base-2 mutual information (bits). -/
def mutualInfoBits {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist (α × β)) : ℝ :=
  mutualInfo p / Real.log 2

/-- Base-2 conditional entropy (bits). -/
def condEntropyBits {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist (α × β)) : ℝ :=
  condEntropy p / Real.log 2
```

For each of the mutual-info theorems above, add a `*_bits` corollary obtained by dividing by `Real.log 2`. For example:

```lean
theorem mutualInfoBits_nonneg ... : 0 ≤ mutualInfoBits p := by
  unfold mutualInfoBits
  exact div_nonneg (mutualInfo_nonneg p) (Real.log_nonneg (by norm_num))

theorem mutualInfoBits_le_entropyBitsFst ... :
    mutualInfoBits p ≤ entropyBits (marginalFst p) := by
  unfold mutualInfoBits entropyBits
  rw [entropyBits_eq_entropyNat_div_log_two]
  exact div_le_div_of_nonneg_right
    (mutualInfo_le_entropyFst p) (Real.log_nonneg (by norm_num))
```

Keep the base-2 corollaries minimal: `nonneg`, `symm`, `le_entropyBitsFst`, `le_entropyBitsSnd`, `self`, plus a `mutualInfoBits_eq_entropyBitsFst_sub_condEntropyBits_swap` (and dual) identity needed by the Fano chapter.

### 4. Data processing inequality (information form) in `MutualInfo.lean`

Add to `MutualInfo.lean`, after the mutual-information identities:

```lean
/-- **Push-forward of a joint via a kernel**: given a joint `p : ProbDist (α × β)` modeling (X, Y) and a kernel `W : β → ProbDist γ` modeling the conditional distribution of Z given Y, form the induced joint `(X, Z) : ProbDist (α × γ)` with
    kernelPushforward p W (a, c) = ∑ b, p (a, b) * W b c. -/
def kernelPushforward
    {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (p : ProbDist (α × β)) (W : β → ProbDist γ) :
    ProbDist (α × γ) := by
  refine ⟨fun ac => ∑ b, p (ac.1, b) * W b ac.2, ?_⟩
  ...  -- simplex proof: doubled Finset.sum reshape, then prob_sum_eq_one
```

Marginal and entropy identities:

- `marginalFst_kernelPushforward : marginalFst (kernelPushforward p W) = marginalFst p`. Proof: `∑ c, ∑ b, p(a, b) · W b c = ∑ b, p(a, b) · ∑ c, W b c = ∑ b, p(a, b) = marginalFst p a` using `Finset.sum_comm`, `prob_sum_eq_one (W b)`, and the definition of `marginalFst`.
- `marginalSnd_kernelPushforward : marginalSnd (kernelPushforward p W) c = ∑ b, marginalSnd p b * W b c`. The second marginal of the push-forward is the push-forward of the second marginal under the same kernel. This exact shape is what the DPI log-sum reshape consumes: the reshape computes `∑_b marginalFst p a · marginalSnd p b · W b c = marginalFst p a · marginalSnd (kernelPushforward p W) c`, matching the "b-side total" term needed by `log_sum_inequality`. Proof: `∑ a, ∑ b, p(a, b) · W b c = ∑ b, (∑ a, p(a, b)) · W b c = ∑ b, marginalSnd p b · W b c` via `Finset.sum_comm` and `Finset.sum_mul`.

Lock the exact statement of `marginalSnd_kernelPushforward` before writing the DPI proof body so the reshape step is a pure rewrite rather than a side computation.

DPI statement:

```lean
/-- **Data processing inequality (information form)**: for a Markov chain X → Y → Z, `I(X; Z) ≤ I(X; Y)`.

The Markov chain is encoded by a joint `p : ProbDist (α × β)` modeling (X, Y) and a kernel `W : β → ProbDist γ` modeling the transition Y → Z. The joint (X, Z) is `kernelPushforward p W`. -/
theorem mutualInfo_kernelPushforward_le
    {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (p : ProbDist (α × β)) (W : β → ProbDist γ) :
    mutualInfo (kernelPushforward p W) ≤ mutualInfo p := by
  ...
```

Proof approach (via log-sum inequality):

Write `q := kernelPushforward p W`. We need `D(q ‖ prodMarginals q) ≤ D(p ‖ prodMarginals p)`.

For each `(a, c)`, apply the log-sum inequality with `a_b := p(a, b) · W b c` and `b_b := marginalFst p a · marginalSnd p b · W b c`:

- `∑_b a_b = q(a, c)` (by definition of `kernelPushforward`)
- `∑_b b_b = marginalFst p a · (∑_b marginalSnd p b · W b c) = marginalFst q a · marginalSnd q c`
- `a_b · log(a_b / b_b) = p(a,b) · W b c · log(p(a,b) / (marginalFst p a · marginalSnd p b))` for `W b c > 0`, matching one term of `D(p ‖ prodMarginals p)`.

The zero-total-friendly statement from Task 2 is essential here: some fixed `(a, c)` fibers may have total mass `0`, and the proof should discharge those fibers by simplification rather than by manufacturing positivity assumptions. Summing over `(a, c)` and reshaping then gives `D(q ‖ prodMarginals q) ≤ D(p ‖ prodMarginals p)`; use `mutualInfo_eq_relEntropy_prodMarginals` to translate back.

Add the base-2 corollary `mutualInfoBits_kernelPushforward_le` by dividing by `Real.log 2`.

If the log-sum-based proof becomes unwieldy during implementation, an alternative route is via subadditivity plus the three-variable joint (build `p₃ : ProbDist (α × β × γ)` from `p` and `W`, show `H(X, Y, Z) = H(X, Y) + H(Z | Y)` and `H(X, Z) ≤ H(X, Y, Z) − H(Y | X, Z) = H(X) + H(Z | X)`, giving `I(X; Z) = H(Z) − H(Z|X) ≤ H(Z) − H(Z|X,Y)`, etc.). Prefer the log-sum route; fall back to the three-variable-joint route only if log-sum bookkeeping explodes.

### 5. Binary entropy helper (`BinaryEntropy.lean`)

Create `Shannon/Entropy/BinaryEntropy.lean`. Imports: `Mathlib.Analysis.SpecialFunctions.BinaryEntropy` only (no Shannon-side dependencies).

```lean
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

namespace Shannon

noncomputable section
open Real

/-- Base-2 binary entropy: `h₂(p) = -p log₂ p - (1 - p) log₂ (1 - p)`.

Thin wrapper over Mathlib's `Real.binEntropy` (defined in nats), dividing by `Real.log 2` to land in bits. Used in Fano's inequality. -/
def binEntropyBits (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2
```

Lifted lemmas (each one-line, dividing the Mathlib nats lemma by `Real.log 2`):

- `binEntropyBits_zero : binEntropyBits 0 = 0`
- `binEntropyBits_one : binEntropyBits 1 = 0`
- `binEntropyBits_two_inv : binEntropyBits 2⁻¹ = 1` (uses `Real.binEntropy_two_inv = Real.log 2`, dividing gives `1`).
- `binEntropyBits_one_sub (p : ℝ) : binEntropyBits (1 - p) = binEntropyBits p` (from `Real.binEntropy_one_sub`).
- `binEntropyBits_nonneg (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : 0 ≤ binEntropyBits p`.
- `binEntropyBits_le_one (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : binEntropyBits p ≤ 1` (from `Real.binEntropy_le_log_two`).
- `binEntropyBits_eq_zero_iff : binEntropyBits p = 0 ↔ p = 0 ∨ p = 1` (from `Real.binEntropy_eq_zero`).
- `binEntropyBits_continuous : Continuous binEntropyBits` (from `Real.binEntropy_continuous`, since `fun p => Real.binEntropy p / Real.log 2` is continuous).
- Private helper `binEntropyBits_eq_negMulLog_pair : binEntropyBits p = (Real.negMulLog p + Real.negMulLog (1 - p)) / Real.log 2` (from `Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub`) if the Fano proof wants a direct bridge to `negMulLog`.

Module docstring follows the Phase B template: one-paragraph overview, "Main definitions" (`binEntropyBits`), "Main results" list.

### 6. Fano's inequality (`Fano.lean` plus `FanoHelpers.lean`)

Create `Shannon/Entropy/Fano.lean` alongside `Shannon/Entropy/FanoHelpers.lean`. Imports: `Fano.lean` imports `Shannon.Entropy.FanoHelpers` (which in turn imports `Shannon.Entropy.MutualInfo` for `condEntropy`, `swapJoint`, `condEntropyBits`) and `Shannon.Entropy.BinaryEntropy`.

Phase C does not assume a new general three-variable entropy API. The proof splits `H(E, X | Y) = H(E | Y) + H(X | E, Y)` via two applications of the existing pairwise `chain_rule`, bridged by relabelings of the nested-pair encodings `(β × (Bool × α))` and `((β × Bool) × α)`. The pairwise chain rule conditions on the first coordinate of a pair, so every step either introduces a `swapJoint` (to put the conditioning variable on the left) or a `relabelProb` (to regroup nested pairs); each rearrangement is justified by `entropyNat_relabelInvariant`.

Create `FanoHelpers.lean` preemptively rather than conditionally: the nested-pair bookkeeping is the proof's dominant cost, and splitting it out from day one keeps `Fano.lean` focused on the final inequality assembly. Plan the helper module around:

- An `errorIndicatorJoint` constructor that augments `(X, Y)` with the Boolean error event `E = [f(Y) ≠ X]` as a joint on `(α × β) × Bool` (or equivalently on `α × β × Bool` via a `relabelProb`).
- Relabel lemmas that bridge between `(α × β) × Bool`, `α × (β × Bool)`, `(α × Bool) × β`, and `β × (α × Bool)`, each proved via `entropyNat_relabelInvariant`.
- The two chain-rule applications packaged as named lemmas (`condEntropy_joint_error_split` and similar) so the main Fano proof reads as four algebraic steps rather than four fresh relabel calculations.
- A deterministic-function entropy lemma `H(E | X, Y) = 0` (since `E` is determined by `X` and `Y`), stated via `condEntropy` on the appropriate nested joint.

Statement (base-2):

```lean
/-- **Fano's inequality** (base 2): for a joint distribution `p : ProbDist (α × β)`, an estimator `f : β → α` of the first coordinate from the second, and error probability
    Pe := ∑ (a, b) ∈ {(a, b) | f b ≠ a}, p (a, b),
the conditional entropy of X given Y is bounded by
    H(X | Y) ≤ h₂(Pe) + Pe · log₂(|α| − 1).

Here `H(X | Y) = condEntropyBits (swapJoint p)`. The bound is stated with the convention `log₂(0) = 0` so that `|α| = 1` still gives a valid bound (the right-hand side equals `h₂(Pe)` in that case; `Pe = 0` is forced anyway). -/
theorem fanoInequality
    {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [DecidableEq α]
    (p : ProbDist (α × β)) (f : β → α) :
    let Pe := ∑ ab ∈ Finset.univ.filter (fun ab => f ab.2 ≠ ab.1), p ab
    condEntropyBits (swapJoint p) ≤
      binEntropyBits Pe + Pe * Real.logb 2 ((Fintype.card α - 1 : ℕ) : ℝ) := by
  ...
```

Proof sketch (classic Fano, via chain rule and conditioning):

1. Define the error indicator `E : ProbDist (α × β) → ProbDist (α × β × Bool)` augmenting `(X, Y)` with the error event `E = [f(Y) ≠ X]`.
2. Chain rule on `(E, X, Y)`: `H(E, X | Y) = H(E | Y) + H(X | E, Y)`.
3. Since `E` is a function of `X` and `Y`, `H(E | X, Y) = 0`, so `H(E, X | Y) = H(X | Y)`.
4. `H(E | Y) ≤ H(E) = h₂(Pe)` by conditioning reduces entropy.
5. `H(X | E, Y) ≤ Pe · log(|α| − 1) + (1 − Pe) · 0`: when `E = 0` the estimator is correct and `X = f(Y)` deterministically; when `E = 1` the conditional entropy of `X` given `Y` and the error event is at most `log(|α| − 1)` (since `X` takes at most `|α| − 1` values in that case).

All four steps in nats first, then divide by `Real.log 2`. The `|α| − 1` cast needs `hcard_sub : (Fintype.card α − 1 : ℕ) = (Fintype.card α : ℝ) − 1` guarded by `Fintype.card α ≥ 1` (automatic from `Nonempty α`).

The `log₂(0)` edge case at `|α| = 1`: when `Fintype.card α = 1`, `(Fintype.card α − 1 : ℕ) = 0`, and `Real.logb 2 0 = 0` by Mathlib's `log 0 = 0` convention, so the right-hand side collapses to `binEntropyBits Pe`. In this case `Pe = 0` is automatic (any estimator is correct since α has one element), so both sides are zero and the bound is trivial.

Auxiliary definition / lemmas:

- `errorProb p f : ℝ := ∑ ab ∈ univ.filter (f ab.2 ≠ ab.1), p ab` lives in `Fano.lean` with standalone lemmas `errorProb_nonneg`, `errorProb_le_one`.
- The nested-pair error-tagged joint constructor, its relabel lemmas, and the two-step conditional-entropy split live in `FanoHelpers.lean` (see the list above).

If the full error-indicator-plus-chain-rule proof of Fano proves awkward at the pinned Mathlib (especially the `H(X | E, Y)` split), fall back to a direct summation argument: expand `condEntropy (swapJoint p)` as a double sum, split into correct and incorrect terms, and bound each. This is more elementary but longer; prefer the chain-rule proof first.

### 7. Testing

New test files:

- `ShannonTest/Entropy/RelativeEntropy.lean`: one `example` per exported symbol (`Supports`, `relEntropy`, `relEntropyBits`, `relEntropy_nonneg`, `relEntropy_eq_zero_iff`, `log_sum_inequality`), plus one composition: `relEntropy` of `(1/2, 1/2)` vs. `(1/4, 3/4)` equals `Real.log (1/2 / (1/4)) / 2 + Real.log (1/2 / (3/4)) / 2 = (log 2 − log (3/2)) / 2`; or a simpler exact-value check closed by `native_decide` / `norm_num` depending on how Mathlib's log simplifies.
- `ShannonTest/Entropy/MutualInfo.lean`: one `example` per exported symbol (all the `mutualInfo_*` theorems, `mutualInfoBits_*`, `swapJoint`, `diagonalDist`, `kernelPushforward`, `mutualInfo_kernelPushforward_le`, `mutualInfoBits_kernelPushforward_le`). Move the existing `mutualInfo (prodDist (uniformPNat 2) (uniformPNat 1)) = 0` example from `ShannonTest/Entropy/Joint.lean` into this file. Add:
  - `mutualInfoBits (prodDist (uniformPNat 2) (uniformPNat 3)) = 0` (independence).
  - `mutualInfo (diagonalDist (uniformPNat 2)) = entropyNat (uniformPNat 2)` (self MI equals entropy).
  - A two-step DPI example on a concrete small joint with a concrete kernel.
- `ShannonTest/Entropy/BinaryEntropy.lean`: one `example` per exported symbol (`binEntropyBits_zero`, `_one`, `_two_inv`, `_one_sub`, `_nonneg`, `_le_one`, `_eq_zero_iff`). Include the numeric anchor `binEntropyBits (1/2) = 1`.
- `ShannonTest/Entropy/Fano.lean`: one `example` calling `fanoInequality` on a concrete small joint. Suggested case: `α := Fin 2`, `β := Fin 2`, `p := prodDist (uniformPNat 2) (uniformPNat 2)` (independent X and Y), `f := id`; `Pe = 1/2`, `|α| − 1 = 1`, `log₂ 1 = 0`, so the inequality reduces to `1 ≤ h₂(1/2) = 1`, equality. This is a good degenerate case: the bound is tight.

Existing test files to extend:

- `ShannonTest/Entropy/Bits.lean`: add the `entropyBits_prodDist` example from Task 1.
- `ShannonTest/Entropy/Joint.lean`: remove the `mutualInfo (prodDist (uniformPNat 2) (uniformPNat 1)) = 0` example (it has moved to `MutualInfo.lean`). Keep everything else.
- `ShannonTest/Entropy.lean` aggregator: add `import ShannonTest.Entropy.{RelativeEntropy, MutualInfo, BinaryEntropy, Fano}`.

Each test file follows the `write-lean-tests` skill discipline: one `example` per exported symbol, closed by `by exact <lemma>` or `by simpa using <lemma>` or (for composition tests) a short tactic block using only the public API. No `import Shannon.Entropy.<M>.Internal` patterns and no `sorry` escape hatches.

For exported `def`s (`swapJoint`, `diagonalDist`, `kernelPushforward`, `Supports`, `relEntropy`, `relEntropyBits`, `mutualInfoBits`, `condEntropyBits`, `binEntropyBits`, `errorProb`), the mirroring rule is that each `def` needs a regression example, but "regression" can be indirect: a test case that unfolds the definition inside a larger expression and closes with a supporting lemma counts. Prefer exercising each `def` through a downstream lemma (e.g. exercise `swapJoint` via `marginalFst_swapJoint`) over standalone `example : swapJoint p = relabelProb _ p := rfl`-style checks, which mostly restate the definition and add little regression value.

Private helpers do not need one-example-per-lemma coverage; exported helpers do. When in doubt, keep proof-only bookkeeping private rather than widening the mirrored public surface unnecessarily.

### 8. Verso book chapters, transcription, facade, documentation

New chapters (`import VersoManual`, `#doc (Manual) "<Title>" => %%% tag := "<slug>" %%%`, single-long-line paragraphs, Lean identifiers in backticks, no `import Shannon`):

- `Book/MutualInformation.lean`: sections "Definition", "Nonnegativity and Independence", "Chain Rule and Conditioning", "Self-information and Bounds". Reference `mutualInfo`, `mutualInfoBits`, the six identities, and `mutualInfo_le_entropyFst`/`Snd`. Cross-link to `Shannon/Entropy/MutualInfo.lean` throughout.
- `Book/RelativeEntropy.lean`: sections "Relative Entropy (KL Divergence)", "Gibbs' Inequality Restated", "Log-Sum Inequality", "Data Processing Inequality (Information Form)". Reference `relEntropy`, `relEntropy_nonneg`, `relEntropy_eq_zero_iff`, `log_sum_inequality`, and `mutualInfo_kernelPushforward_le`.
- `Book/FanoInequality.lean`: sections "The Estimator Setting", "Binary Entropy in Bits", "Fano's Inequality", "Forward Pointer to Phase E". Reference `binEntropyBits`, `fanoInequality`, `errorProb`, and mention that Phase E's finite-state-source material will build on this template.

Chapter ordering update in `Book.lean` (insert between `Logarithm` and `Bibliography`):

```
{include 0 Book.Introduction}
{include 0 Book.AxiomaticEntropy}
{include 0 Book.Properties}
{include 0 Book.Logarithm}
{include 0 Book.MutualInformation}
{include 0 Book.RelativeEntropy}
{include 0 Book.FanoInequality}
{include 0 Book.Bibliography}
```

Update the "Reading Order" list in `Book/Introduction.lean` to mention the three new chapters and add pointers to `Shannon/Entropy/{RelativeEntropy, MutualInfo, BinaryEntropy, Fano}.lean` alongside the existing module list.

Transcription cross-references update in `references/shannon1948-transcription.md`:

Add four bullets under `## Formalization Cross-References`, grouped alongside the existing Section-6 entries:

- `**Relative entropy (Kullback-Leibler divergence)**: relEntropy, relEntropy_nonneg, relEntropy_eq_zero_iff in Shannon/Entropy/RelativeEntropy.lean`
- `**Mutual information**: mutualInfo, mutualInfo_nonneg, mutualInfo_eq_zero_iff_independent, mutualInfo_symm, mutualInfo_self, mutualInfo_le_entropyFst/Snd in Shannon/Entropy/MutualInfo.lean`
- `**Data processing inequality (information form)**: mutualInfo_kernelPushforward_le in Shannon/Entropy/MutualInfo.lean. Forward pointer: Shannon's transducer form (Theorem 7 in the paper) is deferred to Phase E and is a distinct statement, not a restatement of the information-form DPI.`
- `**Fano's inequality**: fanoInequality in Shannon/Entropy/Fano.lean`

The Theorem 7 forward pointer is emphasized so readers do not mistake the information-form DPI proved here for the paper's transducer-form statement.

Per the Phase A/B pattern, do not introduce new transcription prose sections for these (they are not separate Shannon theorems); just the cross-reference bullets.

Facade update in `Shannon/Entropy.lean`:

Add `import Shannon.Entropy.RelativeEntropy`, `import Shannon.Entropy.MutualInfo`, `import Shannon.Entropy.BinaryEntropy`, `import Shannon.Entropy.Fano`. Extend the "Import this file to access..." bullet list so it mentions the full Phase C base-2 surface: `entropyBits`, `mutualInfoBits`, `condEntropyBits`, `binEntropyBits`, `relEntropyBits`, `fanoInequality`. Update the module-chain diagram:

```
Core → Uniform → Rational → Approx → Final → Gibbs → Joint → Properties → MutualInfo → Fano
                                                    ↘ Converse                         ↗
                                                    ↘ Bits → RelativeEntropy ↗
                                                      (Mathlib only) → BinaryEntropy ↗
```

The three feeders into `Fano` are `MutualInfo` (for `condEntropyBits` and the conditional-entropy chain-rule helpers), `RelativeEntropy` (transitively, through `MutualInfo`), and `BinaryEntropy` (standalone from Mathlib). `BinaryEntropy` depends only on Mathlib and does not participate in the `Core → ... → Joint` chain at all.

Update `AGENTS.md` / `CLAUDE.md` Module Layout section: add one-line entries for `Shannon/Entropy/{RelativeEntropy, MutualInfo, BinaryEntropy, Fano}.lean`. Note in the `entropyBits`/`entropyNat` paragraph that base-2 mutual information (`mutualInfoBits`), conditional entropy (`condEntropyBits`), and binary entropy (`binEntropyBits`) join the public surface with Phase C.

`cspell-words.txt` already contains `binentropy`, `Fano`, `kernelpushforward`, `Kullback`, `Leibler`, and `mutualinfo` from Phase B / earlier work. Phase C adds the two new identifiers that surface in Book prose and module docstrings:

- relentropy
- swapjoint

Insert both in the existing alphabetical order. Re-run `make lint-spelling` after the prose edits land to catch any additional words (e.g. identifier casings, author names in Book chapters) this list missed.

Roadmap sync in `docs/plans/todo/2026-04-14-shannon-proofs-roadmap.md`: update the Phase C goal, task summary, and file inventory so the parent roadmap explicitly mentions `BinaryEntropy`, `Fano`, and the expanded test mirror. This spun-out plan is temporary coordination detail; the roadmap remains the canonical long-lived inventory.

## Critical files

Existing, to modify (rough task order):

- `Shannon/Entropy/Bits.lean`: add `entropyBits_prodDist` (Task 1); update imports to include `Joint`.
- `Shannon/Entropy/Joint.lean`: remove `mutualInfo` definition (Task 3); move the line into `MutualInfo.lean` verbatim. Update module docstring to drop the `mutualInfo` bullet.
- `Shannon/Entropy.lean`: add imports and update module-chain diagram (Task 8).
- `docs/plans/todo/2026-04-14-shannon-proofs-roadmap.md`: sync the parent roadmap's Phase C inventory with this plan's settled scope (Task 8).
- `ShannonTest/Entropy.lean`: register the four new test modules (Task 7).
- `ShannonTest/Entropy/Bits.lean`: add `entropyBits_prodDist` example (Task 1).
- `ShannonTest/Entropy/Joint.lean`: remove the `mutualInfo` example (moved to `MutualInfo.lean` test file) (Task 7).
- `Book.lean`: include the three new chapters in reading order (Task 8).
- `Book/Introduction.lean`: extend reading-order list (Task 8).
- `references/shannon1948-transcription.md`: add four cross-reference bullets (Task 8).
- `AGENTS.md` / `CLAUDE.md` (symlink): module-layout entries (Task 8).
- `cspell-words.txt`: add any words surfaced by prose (Task 8).

New, to create:

- `Shannon/Entropy/RelativeEntropy.lean` (Task 2).
- `Shannon/Entropy/MutualInfo.lean` (Tasks 3 and 4).
- `Shannon/Entropy/BinaryEntropy.lean` (Task 5).
- `Shannon/Entropy/Fano.lean` (Task 6).
- `Shannon/Entropy/FanoHelpers.lean` (Task 6, created preemptively alongside `Fano.lean`).
- `ShannonTest/Entropy/RelativeEntropy.lean` (Task 7).
- `ShannonTest/Entropy/MutualInfo.lean` (Task 7).
- `ShannonTest/Entropy/BinaryEntropy.lean` (Task 7).
- `ShannonTest/Entropy/Fano.lean` (Task 7).
- `Book/MutualInformation.lean` (Task 8).
- `Book/RelativeEntropy.lean` (Task 8).
- `Book/FanoInequality.lean` (Task 8).

## Commit strategy

Eight commits keep the branch reviewable. Each commit is self-contained (library + its test mirror + any docstring and facade edits). Book chapters and documentation ride a single trailing commit so the code-reviewable commits do not interleave with prose-dense ones.

1. `feat(entropy): add entropyBits_prodDist base-2 corollary` (Task 1, `Bits.lean` + `ShannonTest/Entropy/Bits.lean`).
2. `feat(entropy): introduce RelativeEntropy with Supports and KL divergence` (Task 2 definitions + `relEntropy_nonneg`, `relEntropy_eq_zero_iff`, `relEntropy_self`; test file seed).
3. `feat(entropy): log-sum inequality` (Task 2 final lemma; test extension).
4. `feat(entropy): relocate mutualInfo and prove core properties` (Task 3: `MutualInfo.lean` creation, `mutualInfo` relocation from `Joint.lean`, all seven mutual-info theorems, `swapJoint`, `diagonalDist`, `kernelPushforward`, their helper lemmas, the matching test module entries; `ShannonTest/Entropy/Joint.lean` loses its `mutualInfo` example).
5. `feat(entropy): data processing inequality (information form)` (Task 4: DPI statement, proof via the log-sum inequality, `marginalFst_kernelPushforward` / `marginalSnd_kernelPushforward` shape, `mutualInfoBits_kernelPushforward_le`, and DPI test example). Split from commit 4 unconditionally: the log-sum reshape bookkeeping is the single largest proof in Phase C and deserves its own reviewable unit regardless of how cleanly it lands.
6. `feat(entropy): binary entropy helper in bits` (Task 5, `BinaryEntropy.lean` + test module).
7. `feat(entropy): Fano's inequality` (Task 6, `Fano.lean` + `FanoHelpers.lean` + test module).
8. `docs(book): MutualInformation, RelativeEntropy, FanoInequality chapters` (Task 8 book additions, transcription cross-refs, facade edits, Introduction reading-order update, AGENTS.md module-layout entries, cspell-words updates).

If Task 6's Fano proof grows, split commit 7 into two (`binEntropyBits` corollaries needed by Fano into 7a; `fanoInequality` itself into 7b). The `FanoHelpers.lean` material stays with 7a since it is infrastructure, not the top-level statement.

If the branch exceeds ~15 commits during implementation, consider splitting into two PRs:

- PR 1: Tasks 1, 2, 3, 4 (primitives and MI + DPI) plus partial book coverage (`MutualInformation`, `RelativeEntropy` chapters).
- PR 2: Tasks 5, 6 (binary entropy and Fano) plus `FanoInequality` chapter.

The roadmap's Phase C unit stays coherent across both PRs; splitting is an implementation convenience, not a scope change.

## Verification

Per-task tripwires (run locally before committing each task):

- Task 1: `lake build Shannon.Entropy.Bits` compiles; `lake test` runs the new `entropyBits_prodDist` example.
- Task 2: `lake build Shannon.Entropy.RelativeEntropy` compiles cold; `lake test` runs the new `RelativeEntropy` test file. `relEntropy_eq_zero_iff` closes without `sorry`; if the pinned Mathlib does not already expose the needed strict log-equality characterization, the planned private `log_eq_sub_one_iff_of_pos` helper lands as part of this task.
- Task 3: `lake build Shannon.Entropy.MutualInfo` compiles; all seven mutual-info theorems plus `swapJoint`, `diagonalDist`, their marginal / entropy identities land; the relocated `mutualInfo` definition is in `MutualInfo.lean` only (grep confirms no duplicate in `Joint.lean`).
- Task 4: the DPI theorem `mutualInfo_kernelPushforward_le` closes; concrete test example on a small joint passes.
- Task 5: `lake build Shannon.Entropy.BinaryEntropy` compiles; `binEntropyBits (1/2) = 1` example passes.
- Task 6: `lake build Shannon.Entropy.Fano` compiles; concrete Fano example on `α := Fin 2`, `β := Fin 2` passes. `lake build Shannon.Entropy.FanoHelpers` also compiles (the helper module lands preemptively, not conditionally).
- Task 7: `lake test` green end-to-end; every new public definition or theorem has a matching `example` in the appropriate `ShannonTest/Entropy/*.lean` file.
- Task 8: `lake build Book` compiles cold; `make book` produces `_site/html-multi/index.html` listing all eight chapters (Introduction, AxiomaticEntropy, Properties, Logarithm, MutualInformation, RelativeEntropy, FanoInequality, Bibliography) in the TOC.

End-of-phase checks (`make check` is the blanket command):

- `make check` passes end-to-end: markdownlint, cspell, `lake lint`, `lake build`, `lake test`.
- `make book` produces non-empty rendered output under `_site/html-multi/` with the expected eight-chapter TOC.
- `bin/bootstrap-worktree` still works from a clean worktree (spot-check by deleting `.lake/` and re-running).
- Spot-check the rendered book via `make serve`: confirm the three new chapters render, internal cross-references resolve, and the depth-2 TOC view still looks right after the additions.

Roadmap-level sanity checks (Phase C row of the roadmap's `## Verification` section):

- For a specific independent `prodDist p q`, `mutualInfo = 0` and `mutualInfoBits = 0`. Concrete case in `ShannonTest/Entropy/MutualInfo.lean`: `mutualInfoBits (prodDist (uniformPNat 2) (uniformPNat 3)) = 0`.
- `relEntropy` of a support-covering hand-picked pair matches the analytic value. Concrete case in `ShannonTest/Entropy/RelativeEntropy.lean`: `(1/2, 1/2)` vs. `(1/4, 3/4)`, closed by direct computation.

Upstream-sync note: Phase C introduces strictly new modules (`RelativeEntropy`, `MutualInfo`, `BinaryEntropy`, `Fano`) that do not exist in `upstream/main`, so the upstream-diff calculus is simpler than Phase B's: these modules add cleanly without conflict. The only modifications to existing files touch `Bits.lean` (Phase B only; not in upstream yet), `Joint.lean` (removing the stub `mutualInfo` def; upstream keeps the stub), the `Shannon/Entropy.lean` facade, tests, docs, and book. Defer upstream-PR consideration until after merge; note in commit messages that the `Joint.lean` removal will need a matching upstream patch that also introduces `MutualInfo.lean`.

## Open questions (to resolve during execution)

- **`relEntropy_eq_zero_iff` proof route**: the cleanest route uses `Real.log x = x - 1 ↔ x = 1` for positive `x`. Expect to budget a short private helper proved from `Real.strictConcaveOn_negMulLog` or a stricter log inequality already present under another name. Prefer reusing Mathlib over inventing more local machinery than this one helper.
- **`log_sum_inequality` statement shape**: the plan above states it in the `∑ a_i log(a_i / b_i) ≥ A log(A/B)` direction (concave form), but generalized so `A = 0` is allowed and simplifies to the trivial `0 ≤ 0` case. Some presentations state the convex form with `a · log(b/a)`. The concave form is more convenient for DPI; state and prove just that direction, and add a convex-form restatement only if Phase D or Fano needs it.
- **DPI proof route**: log-sum is the first choice; the three-variable-joint route is the fallback. Lock in whichever lands cleaner within one commit's worth of work, and record the choice in the commit message.
- **Fano helper modularization**: if the error-indicator three-variable-joint machinery needed by Fano grows beyond ~100 lines, extract it into a helper module (suggested name: `Shannon/Entropy/FanoHelpers.lean`) rather than bloating `Fano.lean`. Otherwise keep the helpers inline.
- **`mutualInfoBits` / `condEntropyBits` surface depth**: the plan adds bits-flavored counterparts only for the theorems Phase C's own Book chapters and test cases touch. If a lemma is used only from a nats proof, leave its bits-flavored variant for a later phase.
