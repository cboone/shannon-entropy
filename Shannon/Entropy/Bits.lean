/-
SPDX-FileCopyrightText: 2026 Christopher Boone
SPDX-License-Identifier: Apache-2.0
-/

import Shannon.Entropy.Joint

/-!
# Shannon.Entropy.Bits

Base-2 public API for Shannon entropy.

`entropyBits` is the base-2 specialization of `entropyBase`, intended as the
primary public entropy API for later phases of this formalization. The
natural-log form `entropyNat` stays as the internal workhorse used throughout
the Appendix 2 characterization proof.

This module provides the bridge lemmas connecting the two forms and restates
the uniqueness theorems in base-2 units.

## Main results

- `entropyBits_def`: definitional expansion into `Real.logb 2`
- `entropyBits_eq_entropyNat_div_log_two`: bridge to the natural-log form
- `entropyBits_nonneg`, `entropyBits_uniformPNat`, `entropyBits_le_logb_two_card`:
  base-2 counterparts of the single-variable bounds from `Gibbs`
- `entropyBits_prodDist`: base-2 counterpart of `entropyNat_prodDist` on product distributions
- `entropyBits_unique`: the base-2 restatement of `entropyBase_unique`
- `entropyBits_unique_eq`: same, with the constant named as `K H * Real.log 2`

## References

- [Shannon1948]: Claude E. Shannon, *A Mathematical Theory of Communication*, *Bell System Technical Journal* 27 (1948), Section 1 and Appendix 2.
- [CoverThomas2006]: Thomas M. Cover and Joy A. Thomas, *Elements of Information Theory*, 2nd ed., Wiley, 2006, Chapter 2.
- [MacKay2003]: David J. C. MacKay, *Information Theory, Inference, and Learning Algorithms*, Cambridge University Press, 2003, Chapter 4.
-/
namespace Shannon

noncomputable section
open Real

/-- Base-2 Shannon entropy (bits). Defined via `entropyBase 2`.

This is the primary public entropy API for Phase C and later. -/
def entropyBits {α : Type} [Fintype α] (p : ProbDist α) : ℝ :=
  entropyBase 2 p

/-- Definitional expansion of `entropyBits` in terms of `Real.logb 2`. Holds by `rfl` because `entropyBits p` unfolds through `entropyBase 2 p` directly to `-∑ a, p a * Real.logb 2 (p a)`. -/
lemma entropyBits_def {α : Type} [Fintype α] (p : ProbDist α) :
    entropyBits p = -∑ a, p a * Real.logb 2 (p a) := rfl

/-- Bridge between base-2 and natural-log entropy: dividing the natural-log
form by `log 2` gives the base-2 form. -/
lemma entropyBits_eq_entropyNat_div_log_two {α : Type} [Fintype α] (p : ProbDist α) :
    entropyBits p = entropyNat p / Real.log 2 := by
  unfold entropyBits entropyBase entropyNat
  rw [neg_div, Finset.sum_div]
  refine congrArg Neg.neg ?_
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [Real.logb, mul_div_assoc]

/-- Reverse bridge: the natural-log entropy is the base-2 entropy scaled by
`log 2`. -/
lemma entropyNat_eq_entropyBits_mul_log_two {α : Type} [Fintype α] (p : ProbDist α) :
    entropyNat p = entropyBits p * Real.log 2 := by
  have hlog2_ne : Real.log 2 ≠ 0 := by
    apply Real.log_ne_zero.mpr; norm_num
  rw [entropyBits_eq_entropyNat_div_log_two, div_mul_cancel₀ _ hlog2_ne]

/-- Base-2 entropy is nonnegative. -/
theorem entropyBits_nonneg {α : Type} [Fintype α] (p : ProbDist α) :
    0 ≤ entropyBits p := by
  rw [entropyBits_eq_entropyNat_div_log_two]
  exact div_nonneg (entropyNat_nonneg p) (Real.log_nonneg (by norm_num))

/-- Base-2 entropy of the uniform distribution on `n` outcomes equals `logb 2 n`. -/
theorem entropyBits_uniformPNat (n : ℕ+) :
    entropyBits (uniformPNat n) = Real.logb 2 (n : ℝ) := by
  rw [entropyBits_eq_entropyNat_div_log_two, entropyNat_uniformPNat, Real.log_div_log]

/-- Base-2 entropy is at most `logb 2 |α|`, with equality at the uniform distribution. -/
theorem entropyBits_le_logb_two_card {α : Type} [Fintype α] [Nonempty α]
    (p : ProbDist α) :
    entropyBits p ≤ Real.logb 2 (Fintype.card α : ℝ) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [entropyBits_eq_entropyNat_div_log_two, ← Real.log_div_log]
  exact (div_le_div_iff_of_pos_right hlog2_pos).2 (entropyNat_le_log_card p)

/-- Additivity for independent distributions in bits: `entropyBits (prodDist p q) = entropyBits p + entropyBits q`.

Base-2 counterpart of `entropyNat_prodDist`, obtained by dividing the natural-log identity by `Real.log 2`. -/
theorem entropyBits_prodDist
    {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist α) (q : ProbDist β) :
    entropyBits (prodDist p q) = entropyBits p + entropyBits q := by
  simp only [entropyBits_eq_entropyNat_div_log_two]
  rw [entropyNat_prodDist, add_div]

/-- Base-2 uniqueness (tighter statement that names the constant):
any `H` satisfying the Shannon axioms agrees with base-2 Shannon entropy
scaled by `K H * Real.log 2`. -/
theorem entropyBits_unique_eq
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H)
    {α : Type} [Fintype α] (p : ProbDist α) :
    H p = -(K H * Real.log 2) * ∑ a, p a * Real.logb 2 (p a) := by
  have hlog2_ne : Real.log 2 ≠ 0 := by
    apply Real.log_ne_zero.mpr; norm_num
  have hsum :
      (∑ a, p a * Real.log (p a))
        = Real.log 2 * (∑ a, p a * Real.logb 2 (p a)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro a _
    have hterm : Real.log (p a) = Real.log 2 * Real.logb 2 (p a) := by
      unfold Real.logb; field_simp [hlog2_ne]
    rw [hterm]; ring
  calc
    H p = -K H * ∑ a, p a * Real.log (p a) := entropyNat_unique H hH p
    _ = -(K H * Real.log 2) * ∑ a, p a * Real.logb 2 (p a) := by
      rw [hsum]; ring

/-- Base-2 uniqueness (existential form):
there is a positive constant `Kb` with `H p = -Kb * ∑ p_i logb 2 p_i`.
Obtained by specializing `entropyBase_unique` to `b := 2`. -/
theorem entropyBits_unique
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H) :
    ∃ Kb : ℝ, 0 < Kb ∧
      ∀ {α : Type} [Fintype α] (p : ProbDist α),
        H p = -Kb * ∑ a, p a * Real.logb 2 (p a) :=
  entropyBase_unique H hH 2 (by norm_num)


end

end Shannon
