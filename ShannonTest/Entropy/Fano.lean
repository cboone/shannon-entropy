/-
SPDX-FileCopyrightText: 2026 Christopher Boone
SPDX-License-Identifier: Apache-2.0
-/

import Shannon.Entropy.Fano

/-!
# Shannon Entropy: Fano Tests

Exercises for the public Fano-inequality API.
-/

open Shannon

noncomputable section

example (p : ProbDist (Fin 2 × Fin 3)) (f : Fin 3 → Fin 2) :
    0 ≤ errorProb p f :=
  errorProb_nonneg p f

example (p : ProbDist (Fin 2 × Fin 3)) (f : Fin 3 → Fin 2) :
    errorProb p f = 1 - ∑ y, p (f y, y) :=
  errorProb_eq_one_sub_sum_correct p f

example (p : ProbDist (Fin 2 × Fin 3)) (f : Fin 3 → Fin 2) :
    errorProb p f ≤ 1 :=
  errorProb_le_one p f

example (p : ProbDist (Fin 2 × Fin 3)) (f : Fin 3 → Fin 2) (y : Fin 3) :
    0 ≤ rowErrorProb p f y :=
  rowErrorProb_nonneg p f y

example (p : ProbDist (Fin 2 × Fin 3)) (f : Fin 3 → Fin 2) (y : Fin 3) :
    rowErrorProb p f y ≤ 1 :=
  rowErrorProb_le_one p f y

example (p : ProbDist (Fin 2 × Fin 3)) (f : Fin 3 → Fin 2) :
    condEntropy (swapJoint p) ≤ Real.qaryEntropy (Fintype.card (Fin 2)) (errorProb p f) :=
  condEntropy_swapJoint_le_qaryEntropy_errorProb p f

example :
    let p := prodDist (uniformPNat 2) (uniformPNat 2)
    errorProb p id = (1 : ℝ) / 2 := by
  intro p
  rw [errorProb_eq_one_sub_sum_correct]
  simp [p, prodDist]
  change 1 - (∑ x : Fin 2, (uniformPNat 2) x * (uniformPNat 2) x) = ((2 : ℝ)⁻¹)
  rw [Fin.sum_univ_two]
  norm_num [uniformPNat]

example :
    let p := prodDist (uniformPNat 2) (uniformPNat 2)
    condEntropyBits (swapJoint p) ≤ 1 := by
  intro p
  have hPe : errorProb p id = (1 : ℝ) / 2 := by
    rw [errorProb_eq_one_sub_sum_correct]
    simp [p, prodDist]
    change 1 - (∑ x : Fin 2, (uniformPNat 2) x * (uniformPNat 2) x) = ((2 : ℝ)⁻¹)
    rw [Fin.sum_univ_two]
    norm_num [uniformPNat]
  have hbin : binEntropyBits (1 / 2 : ℝ) = 1 := by
    have hhalf : (1 / 2 : ℝ) = 2⁻¹ := by norm_num
    rw [hhalf]
    exact binEntropyBits_two_inv
  have h : condEntropyBits (swapJoint p) ≤
      binEntropyBits (errorProb p id) +
        errorProb p id * Real.logb 2 ((Fintype.card (Fin 2) - 1 : ℕ) : ℝ) :=
    fanoInequality p id
  rw [hPe, hbin] at h
  have hzero : (1 / 2 : ℝ) * Real.logb 2 ((Fintype.card (Fin 2) - 1 : ℕ) : ℝ) = 0 := by
    simp
  calc
    condEntropyBits (swapJoint p) ≤ 1 + (1 / 2 : ℝ) * Real.logb 2 ((Fintype.card (Fin 2) - 1 : ℕ) : ℝ) := h
    _ = 1 := by rw [hzero, add_zero]
