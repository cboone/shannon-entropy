import Shannon.Entropy.RelativeEntropy

/-!
# Shannon Entropy: Relative Entropy Tests

Exercises for the public KL-divergence API.
-/

open Shannon

noncomputable section

private def quarterThreeQuarter : ProbDist (Fin 2) :=
  ⟨![1 / 4, 3 / 4], by
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> norm_num
    · simp [Fin.sum_univ_two]
      norm_num⟩

example : Supports (uniformPNat 2) (uniformPNat 2) := by
  intro a _
  positivity

example : relEntropy (uniformPNat 2) (uniformPNat 2) = 0 :=
  relEntropy_self _

example : 0 ≤ relEntropy (uniformPNat 2) (uniformPNat 2) :=
  relEntropy_nonneg _ _ (by intro a h; exact h)

example : 0 ≤ relEntropyBits (uniformPNat 2) (uniformPNat 2) :=
  relEntropyBits_nonneg _ _ (by intro a h; exact h)

example : Supports quarterThreeQuarter (uniformPNat 2) := by
  intro a _
  fin_cases a <;> simp [quarterThreeQuarter]

example : relEntropy (uniformPNat 2) quarterThreeQuarter = Real.log (4 / 3 : ℝ) / 2 := by
  have hrewrite :
      relEntropy (uniformPNat 2) quarterThreeQuarter =
        (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) / (1 / 4 : ℝ)) +
          (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) / (3 / 4 : ℝ)) := by
    unfold relEntropy
    change ∑ a : Fin 2, (uniformPNat 2) a * Real.log ((uniformPNat 2) a / quarterThreeQuarter a) =
      (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) / (1 / 4 : ℝ)) +
        (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) / (3 / 4 : ℝ))
    rw [Fin.sum_univ_two]
    change (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) / (1 / 4 : ℝ)) +
        (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) / (3 / 4 : ℝ)) =
      (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) / (1 / 4 : ℝ)) +
        (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) / (3 / 4 : ℝ))
    rfl
  rw [hrewrite]
  rw [show ((1 / 2 : ℝ) / (1 / 4 : ℝ) = (2 : ℝ)) by norm_num,
    show ((1 / 2 : ℝ) / (3 / 4 : ℝ) = (2 / 3 : ℝ)) by norm_num,
    show (1 / 2 : ℝ) = ((2 : ℝ)⁻¹) by norm_num]
  have hlog23 : Real.log (2 / 3 : ℝ) = Real.log (4 / 3 : ℝ) - Real.log 2 := by
    rw [show (2 / 3 : ℝ) = (4 / 3 : ℝ) / 2 by norm_num, Real.log_div (by positivity) (by norm_num)]
  rw [hlog23]
  ring

example :
    relEntropy (uniformPNat 2) quarterThreeQuarter = 0
      ↔ ∀ a, (uniformPNat 2) a = quarterThreeQuarter a :=
  relEntropy_eq_zero_iff _ _ (by intro a _; fin_cases a <;> simp [quarterThreeQuarter])

example :
    (∑ i, (uniformPNat 2) i) * Real.log ((∑ i, (uniformPNat 2) i) / (∑ i, (uniformPNat 2) i))
      ≤ ∑ i, (uniformPNat 2) i * Real.log ((uniformPNat 2) i / (uniformPNat 2) i) := by
  exact log_sum_inequality
    (fun i : Fin 2 => (uniformPNat 2) i)
    (fun i : Fin 2 => (uniformPNat 2) i)
    (fun i => prob_nonneg (uniformPNat 2) i)
    (fun i => prob_nonneg (uniformPNat 2) i)
    (fun i h => h)
