import Shannon.Entropy.BinaryEntropy

/-!
# Shannon Entropy: Binary Entropy Tests

Exercises for the public base-2 binary-entropy wrapper.
-/

open Shannon

example : binEntropyBits 0 = 0 :=
  binEntropyBits_zero

example : binEntropyBits 1 = 0 :=
  binEntropyBits_one

example : binEntropyBits 2⁻¹ = 1 :=
  binEntropyBits_two_inv

example (p : ℝ) : binEntropyBits (1 - p) = binEntropyBits p :=
  binEntropyBits_one_sub p

example (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : 0 ≤ binEntropyBits p :=
  binEntropyBits_nonneg hp₀ hp₁

example (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : binEntropyBits p ≤ 1 :=
  binEntropyBits_le_one hp₀ hp₁

example (p : ℝ) : binEntropyBits p = 0 ↔ p = 0 ∨ p = 1 :=
  binEntropyBits_eq_zero_iff
