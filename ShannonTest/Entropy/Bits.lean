import Shannon.Entropy.Bits
import Shannon.Entropy.Converse

/-!
# Shannon Entropy: Bits Tests

Exercises for the base-2 public API (`entropyBits`), including the
uniform-distribution value, bridge to the natural-log form, nonnegativity,
and the base-2 uniqueness theorem.
-/

open Shannon

example : entropyBits (uniformPNat 2) = 1 := by
  rw [entropyBits_uniformPNat]
  exact_mod_cast Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)

example : entropyBits (uniformPNat 4) = 2 := by
  rw [entropyBits_uniformPNat]
  have h4 : ((4 : ℕ+) : ℝ) = (2 : ℝ) ^ 2 := by norm_num
  rw [h4, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  norm_num

example (p : ProbDist (Fin 3)) : entropyBits p = entropyNat p / Real.log 2 :=
  entropyBits_eq_entropyNat_div_log_two p

example (p : ProbDist (Fin 3)) : 0 ≤ entropyBits p :=
  entropyBits_nonneg p

example (p : ProbDist (Fin 3)) : entropyBits p ≤ Real.logb 2 (Fintype.card (Fin 3) : ℝ) :=
  entropyBits_le_logb_two_card p

example (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H) {α : Type} [Fintype α] (p : ProbDist α) :
    H p = -(K H * Real.log 2) * ∑ a, p a * Real.logb 2 (p a) :=
  entropyBits_unique_eq H hH p
