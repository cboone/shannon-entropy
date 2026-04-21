/-
SPDX-FileCopyrightText: 2026 Christopher Boone
SPDX-License-Identifier: Apache-2.0
-/

import Shannon.Entropy.Rational
import Shannon.Entropy.Converse

/-!
# Shannon Entropy: Rational Tests

Exercises for rational-count refinements and the worked `(1/2, 1/3, 1/6)`
decomposition.
-/

open Shannon

example :
    relabelProb (Fintype.equivFinOfCardEq (by decide))
      (composeProb (uniformPNat 2) (fun _ : Fin 2 => uniformPNat 1))
      = uniformPNat 2 := by
  simpa using
    relabel_compose_rational_eq_uniform
      (p := uniformPNat 2)
      (n := fun _ : Fin 2 => 1)
      (hpos := fun _ : Fin 2 => show 0 < (1 : ℕ) from by decide)
      (N := 2)
      (hN := by decide)
      (hp := by intro a; norm_num [uniformPNat])
      (e := Fintype.equivFinOfCardEq (by decide))

example (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H) {α : Type} [Fintype α]
    (p : ProbDist α) (n : α → ℕ) (hpos : ∀ a, 0 < n a)
    (N : ℕ) (hN : 0 < N) (hsum : (∑ a, n a) = N)
    (hp : ∀ a, p a = (n a : ℝ) / (N : ℝ)) :
    Apos H ⟨N, hN⟩ = H p + ∑ a, p a * Apos H ⟨n a, hpos a⟩ :=
  grouping_on_rational_counts H hH p n hpos N hN hsum hp

example :
    entropyNat (uniformPNat 3)
      = -K entropyNat * ∑ a, (uniformPNat 3) a * Real.log ((uniformPNat 3) a) := by
  simpa using
    entropyNat_of_rational_counts
      entropyNat
      entropyNat_shannonAxioms
      (uniformPNat 3)
      (fun _ : Fin 3 => 1)
      (fun _ : Fin 3 => show 0 < (1 : ℕ) from by decide)
      3
      (by decide)
      (by decide)
      (by intro a; norm_num [uniformPNat])

example :
    workedCompose ⟨true, (0 : Fin 1)⟩ = (1 : ℝ) / 2 ∧
      workedCompose ⟨false, (0 : Fin 2)⟩ = (1 : ℝ) / 3 ∧
      workedCompose ⟨false, (1 : Fin 2)⟩ = (1 : ℝ) / 6 :=
  workedCompose_masses

example :
    entropyNat workedCompose = entropyNat workedP + (1 / 2 : ℝ) * entropyNat (workedQ false) :=
  worked_grouping_identity entropyNat entropyNat_shannonAxioms

/-- Exact entropy value for Shannon's `(1/2, 1/3, 1/6)` example. -/
example :
    let p : ProbDist (Fin 3) :=
      ⟨![1/2, 1/3, 1/6], by
        refine ⟨fun i => ?_, ?_⟩
        · fin_cases i <;> norm_num
        · simp [Fin.sum_univ_three]; norm_num⟩
    entropyNat p = (2 / 3 : ℝ) * Real.log 2 + (1 / 2 : ℝ) * Real.log 3 := by
  intro p
  unfold entropyNat
  rw [Fin.sum_univ_three]
  change -((1 / 2 : ℝ) * Real.log (1 / 2 : ℝ) + (1 / 3 : ℝ) * Real.log (1 / 3 : ℝ) + (1 / 6 : ℝ) * Real.log (1 / 6 : ℝ)) =
      (2 / 3 : ℝ) * Real.log 2 + (1 / 2 : ℝ) * Real.log 3
  rw [show (1 / 2 : ℝ) = ((2 : ℝ)⁻¹) by norm_num,
    show (1 / 3 : ℝ) = ((3 : ℝ)⁻¹) by norm_num,
    show (1 / 6 : ℝ) = ((6 : ℝ)⁻¹) by norm_num,
    Real.log_inv, Real.log_inv, Real.log_inv]
  have hlog6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [hlog6]
  ring

/-- Numeric complement to the `workedCompose` tree: `entropyNat_of_rational_counts`
instantiated on the flat `(1/2, 1/3, 1/6)` distribution with counts `(3, 2, 1)`
summing to `N = 6`. -/
example :
    let p : ProbDist (Fin 3) :=
      ⟨![1/2, 1/3, 1/6], by
        refine ⟨fun i => ?_, ?_⟩
        · fin_cases i <;> norm_num
        · simp [Fin.sum_univ_three]; norm_num⟩
    entropyNat p = -K entropyNat * ∑ a, p a * Real.log (p a) := by
  intro p
  refine entropyNat_of_rational_counts
      entropyNat entropyNat_shannonAxioms
      p (fun i : Fin 3 => ![3, 2, 1] i)
      (fun i => by fin_cases i <;> decide)
      6 (by decide) (by decide) ?_
  intro a
  fin_cases a <;> simp [p] <;> norm_num
