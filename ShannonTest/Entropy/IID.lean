/-
SPDX-FileCopyrightText: 2026 Christopher Boone
SPDX-License-Identifier: Apache-2.0
-/

import Shannon.Entropy.IID

/-!
# Shannon Entropy: IID Tests

Regression tests for the i.i.d. product distribution, base-2 self-information,
typical sets, and the pointwise typical-set mass bounds.
-/

open Shannon

example (p : ProbDist (Fin 3)) (N : ℕ) (x : Fin N → Fin 3) :
    (iidDist p N) x = ∏ i, p (x i) :=
  iidDist_apply p N x

example (p : ProbDist (Fin 3)) (N : ℕ) :
    entropyNat (iidDist p N) = N * entropyNat p :=
  iidDist_entropyNat p N

example (p : ProbDist (Fin 3)) (N : ℕ) :
    entropyBits (iidDist p N) = N * entropyBits p :=
  iidDist_entropyBits p N

example : entropyBits (iidDist (uniformPNat 2) 4) = 4 := by
  rw [iidDist_entropyBits, entropyBits_uniformPNat]
  norm_num [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]

example : entropyBits (iidDist (uniformPNat 2) 0) = 0 := by
  rw [iidDist_entropyBits]
  norm_num

example (p : ProbDist (Fin 3)) (a : Fin 3) :
    logProbBits p a = -Real.logb 2 (p a) :=
  rfl

example (p : ProbDist (Fin 3)) :
    ∑ a, p a * logProbBits p a = entropyBits p :=
  sum_mul_logProbBits p

example (p : ProbDist (Fin 3)) (N : ℕ) (ε : ℝ) :
    typicalSet p N ε =
      Finset.univ.filter fun x =>
        (∀ i, 0 < p (x i)) ∧
          |(1 / (N : ℝ)) * (∑ i, logProbBits p (x i)) - entropyBits p| < ε :=
  rfl

example {p : ProbDist (Fin 2)} {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    {x : Fin N → Fin 2} (hx : x ∈ typicalSet p N ε) :
    (iidDist p N) x ≤ (2 : ℝ) ^ (-(N : ℝ) * (entropyBits p - ε)) :=
  iidDist_le_of_mem_typicalSet (p := p) (N := N) (ε := ε) hx

example {p : ProbDist (Fin 2)} {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    {x : Fin N → Fin 2} (hx : x ∈ typicalSet p N ε) :
    (2 : ℝ) ^ (-(N : ℝ) * (entropyBits p + ε)) ≤ (iidDist p N) x :=
  iidDist_ge_of_mem_typicalSet (p := p) (N := N) (ε := ε) hx
