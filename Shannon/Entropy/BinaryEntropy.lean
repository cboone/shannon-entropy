import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Shannon.Entropy.BinaryEntropy

Base-2 binary entropy.

Mathlib defines `Real.binEntropy` in nats. This module wraps that definition in
bits by dividing by `Real.log 2`, providing the small API needed by the Phase C
mutual-information and Fano developments.

## Main definitions

- `binEntropyBits`: binary entropy measured in bits

## Main results

- `binEntropyBits_zero`, `binEntropyBits_one`, `binEntropyBits_two_inv`: basic evaluations
- `binEntropyBits_one_sub`: symmetry under `p ↦ 1 - p`
- `binEntropyBits_nonneg`, `binEntropyBits_le_one`, `binEntropyBits_eq_zero_iff`: basic bounds
- `binEntropyBits_continuous`: continuity of the base-2 wrapper
-/
namespace Shannon

noncomputable section
open Real

/-- Base-2 binary entropy: `h₂(p) = -p log₂ p - (1 - p) log₂ (1 - p)`.

Thin wrapper over Mathlib's `Real.binEntropy` (defined in nats), dividing by
`Real.log 2` to land in bits. Used in Fano's inequality. -/
def binEntropyBits (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

@[simp] theorem binEntropyBits_zero : binEntropyBits 0 = 0 := by
  unfold binEntropyBits
  simp

@[simp] theorem binEntropyBits_one : binEntropyBits 1 = 0 := by
  unfold binEntropyBits
  simp

@[simp] theorem binEntropyBits_two_inv : binEntropyBits 2⁻¹ = 1 := by
  unfold binEntropyBits
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [Real.binEntropy_two_inv]
  field_simp [hlog2_ne]

@[simp] theorem binEntropyBits_one_sub (p : ℝ) : binEntropyBits (1 - p) = binEntropyBits p := by
  unfold binEntropyBits
  rw [Real.binEntropy_one_sub]

theorem binEntropyBits_nonneg (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : 0 ≤ binEntropyBits p := by
  unfold binEntropyBits
  exact div_nonneg (Real.binEntropy_nonneg hp₀ hp₁) (Real.log_nonneg (by norm_num))

theorem binEntropyBits_le_one (_hp₀ : 0 ≤ p) (_hp₁ : p ≤ 1) : binEntropyBits p ≤ 1 := by
  unfold binEntropyBits
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_iff₀ hlog2_pos]
  simpa using Real.binEntropy_le_log_two (p := p)

theorem binEntropyBits_eq_zero_iff : binEntropyBits p = 0 ↔ p = 0 ∨ p = 1 := by
  constructor
  · intro h
    have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    have hnat : Real.binEntropy p = 0 := by
      rcases div_eq_zero_iff.mp h with hzero | hzero
      · exact hzero
      · exact False.elim (hlog2_ne hzero)
    exact Real.binEntropy_eq_zero.mp hnat
  · rintro (rfl | rfl) <;> simp

theorem binEntropyBits_continuous : Continuous binEntropyBits := by
  unfold binEntropyBits
  fun_prop

private theorem binEntropyBits_eq_negMulLog_pair (p : ℝ) :
    binEntropyBits p = (Real.negMulLog p + Real.negMulLog (1 - p)) / Real.log 2 := by
  unfold binEntropyBits
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

end

end Shannon
