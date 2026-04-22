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

noncomputable section

private lemma entropyBits_uniform_two : entropyBits (uniformPNat 2) = 1 := by
  rw [entropyBits_uniformPNat]
  exact_mod_cast Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)

private lemma logProbBits_uniform_two (a : Fin 2) : logProbBits (uniformPNat 2) a = 1 := by
  unfold logProbBits
  have hmass : (uniformPNat 2) a = ((2 : ℝ)⁻¹) := by
    simp [uniformPNat]
  rw [hmass]
  rw [Real.logb_inv, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  norm_num

private def alternatingWord : Fin 4 → Fin 2 := ![0, 1, 0, 1]

private lemma uniform_two_shell (x : Fin 4 → Fin 2) :
    |(1 / (4 : ℝ)) * (∑ i, logProbBits (uniformPNat 2) (x i)) - entropyBits (uniformPNat 2)| <
      (1 / 10 : ℝ) := by
  rw [Fin.sum_univ_four, entropyBits_uniform_two]
  rw [logProbBits_uniform_two (x 0), logProbBits_uniform_two (x 1), logProbBits_uniform_two (x 2),
    logProbBits_uniform_two (x 3)]
  norm_num

private lemma uniform_two_typicalSet_eq_univ : typicalSet (uniformPNat 2) 4 (1 / 10 : ℝ) = Finset.univ := by
  ext x
  simp only [typicalSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro _
    trivial
  · intro _
    constructor
    · intro i
      have hhalf : (uniformPNat 2) (x i) = ((2 : ℝ)⁻¹) := by
        simp [uniformPNat]
      rw [hhalf]
      norm_num
    · exact uniform_two_shell x

example (p : ProbDist (Fin 3)) (N : ℕ) (x : Fin N → Fin 3) :
    (iidDist p N) x = ∏ i, p (x i) :=
  iidDist_apply p N x

example (p : ProbDist (Fin 2)) (N : ℕ) :
    iidDist p (N + 1)
      = relabelProb (Fin.consEquiv fun _ : Fin (N + 1) => Fin 2) (prodDist p (iidDist p N)) :=
  iidDist_succ_relabel p N

example (p : ProbDist (Fin 3)) (N : ℕ) :
    entropyNat (iidDist p N) = N * entropyNat p :=
  iidDist_entropyNat p N

example (p : ProbDist (Fin 3)) (N : ℕ) :
    entropyBits (iidDist p N) = N * entropyBits p :=
  iidDist_entropyBits p N

example : entropyBits (iidDist (uniformPNat 2) 4) = 4 := by
  rw [iidDist_entropyBits, entropyBits_uniform_two]
  norm_num

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

example : typicalSet (uniformPNat 2) 4 (1 / 10 : ℝ) = Finset.univ := by
  exact uniform_two_typicalSet_eq_univ

example : alternatingWord ∈ typicalSet (uniformPNat 2) 4 (1 / 10 : ℝ) := by
  rw [uniform_two_typicalSet_eq_univ]
  exact Finset.mem_univ _

example {p : ProbDist (Fin 2)} {N : ℕ} {ε : ℝ}
    {x : Fin N → Fin 2} (hx : x ∈ typicalSet p N ε) :
    (iidDist p N) x ≤ (2 : ℝ) ^ (-(N : ℝ) * (entropyBits p - ε)) :=
  iidDist_le_of_mem_typicalSet (p := p) (N := N) (ε := ε) hx

example {p : ProbDist (Fin 2)} {N : ℕ} {ε : ℝ}
    {x : Fin N → Fin 2} (hx : x ∈ typicalSet p N ε) :
    (2 : ℝ) ^ (-(N : ℝ) * (entropyBits p + ε)) ≤ (iidDist p N) x :=
  iidDist_ge_of_mem_typicalSet (p := p) (N := N) (ε := ε) hx
