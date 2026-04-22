/-
SPDX-FileCopyrightText: 2026 Christopher Boone
SPDX-License-Identifier: Apache-2.0
-/

import Shannon.Entropy.AEP

/-!
# Shannon Entropy: AEP Tests

Regression tests for finite Chebyshev, the i.i.d. AEP, and the typical-set
cardinality bounds.
-/

open Shannon
open scoped Topology

noncomputable section

private def bitValue : Fin 2 → ℝ := ![0, 1]

example (p : ProbDist (Fin 3)) (f : Fin 3 → ℝ) (ε : ℝ) (hε : 0 < ε) :
    (∑ a ∈ Finset.univ.filter (fun a => ε ≤ |f a - (∑ b, p b * f b)|), p a)
      ≤ (∑ a, p a * (f a - (∑ b, p b * f b)) ^ 2) / ε ^ 2 :=
  chebyshev_finite p f ε hε

example :
    (∑ a ∈ Finset.univ.filter
        (fun a : Fin 2 => (1 / 2 : ℝ) ≤ |bitValue a - (∑ b, (uniformPNat 2) b * bitValue b)|),
      (uniformPNat 2) a)
      ≤ (∑ a, (uniformPNat 2) a * (bitValue a - (∑ b, (uniformPNat 2) b * bitValue b)) ^ 2) /
        (1 / 2 : ℝ) ^ 2 := by
  simpa [bitValue, uniformPNat, Fin.sum_univ_two] using
    chebyshev_finite (uniformPNat 2) bitValue (1 / 2 : ℝ) (by norm_num)

example (p : ProbDist (Fin 3)) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (1 - δ : ℝ) ≤ ∑ x ∈ typicalSet p N ε, (iidDist p N) x :=
  aep_iid p hε hδ

example (p : ProbDist (Fin 3)) (N : ℕ) (ε : ℝ) :
    (typicalSet p N ε).card ≤ (2 : ℝ) ^ ((N : ℝ) * (entropyBits p + ε)) :=
  typicalSet_iidDist_card_le p N ε

example (p : ProbDist (Fin 3)) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (1 - δ) * (2 : ℝ) ^ ((N : ℝ) * (entropyBits p - ε)) ≤ (typicalSet p N ε).card :=
  typicalSet_iidDist_card_ge p hε hδ

example (p : ProbDist (Fin 3)) (N : ℕ) {q : ℝ} (hq₀ : 0 < q) (hq₁ : q < 1) :
    minCover p N q hq₀ hq₁ = minCover p N q hq₀ hq₁ :=
  rfl

example (p : ProbDist (Fin 3)) {q : ℝ} (hq₀ : 0 < q) (hq₁ : q < 1) :
    Filter.Tendsto
      (fun N : ℕ => Real.logb 2 ((minCover p N q hq₀ hq₁ : ℝ)) / (N : ℝ))
      Filter.atTop (𝓝 (entropyBits p)) :=
  tendsto_logb_minCover_iid p hq₀ hq₁

example :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (1 - (0.1 : ℝ)) ≤ ∑ x ∈ typicalSet (uniformPNat 2) N 0.1, (iidDist (uniformPNat 2) N) x := by
  exact aep_iid (uniformPNat 2) (by norm_num) (by norm_num)

example :
    (typicalSet (uniformPNat 2) 4 0.1).card ≤ (2 : ℝ) ^ ((4 : ℝ) * (entropyBits (uniformPNat 2) + 0.1)) := by
  exact typicalSet_iidDist_card_le (uniformPNat 2) 4 0.1
