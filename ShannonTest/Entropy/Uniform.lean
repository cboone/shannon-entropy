import Shannon.Entropy.Uniform
import Shannon.Entropy.Converse

/-!
# Shannon Entropy: Uniform Tests

Exercises for the equiprobable phase, including multiplicativity, logarithmic
characterization, positivity, and monotonicity.
-/

open Shannon

example :
    Apos entropyNat (2 * 3) = Apos entropyNat 2 + Apos entropyNat 3 :=
  Apos_mul entropyNat entropyNat_shannonAxioms 2 3

example : Apos entropyNat 1 = 0 :=
  Apos_one_zero entropyNat entropyNat_shannonAxioms

example : 0 < Apos entropyNat 3 :=
  Apos_pos_of_one_lt entropyNat entropyNat_shannonAxioms (by decide)

example : 0 < K entropyNat :=
  K_pos entropyNat entropyNat_shannonAxioms

example :
    Apos entropyNat (2 ^ 3) = (3 : ℝ) * Apos entropyNat 2 :=
  Apos_pow entropyNat entropyNat_shannonAxioms 2 3

example : Apos entropyNat 3 = K entropyNat * Real.log 3 :=
  Apos_eq_K_mul_log entropyNat entropyNat_shannonAxioms 3

example : Apos entropyNat 2 ≤ Apos entropyNat 4 :=
  (Apos_monotone entropyNat entropyNat_shannonAxioms) (by decide)

example :
    Apos entropyNat 3 = (K entropyNat * Real.log 10) * Real.logb 10 3 :=
  Apos_eq_K_mul_logb entropyNat entropyNat_shannonAxioms 10 (by norm_num) 3

example : Apos entropyNat 4 = 2 * Apos entropyNat 2 := by
  have h : (4 : ℕ+) = 2 ^ 2 := rfl
  have := Apos_pow entropyNat entropyNat_shannonAxioms 2 2
  rw [h]; exact_mod_cast this
