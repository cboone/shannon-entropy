import Shannon.Entropy.Gibbs

/-!
# Shannon Entropy: Gibbs Tests

Exercises for the `negMulLog` bridge, Gibbs inequality, and the basic entropy
bounds derived from it.
-/

open Shannon

example (p : ProbDist (Fin 2)) :
    entropyNat p = ∑ a, Real.negMulLog (p a) :=
  entropyNat_eq_sum_negMulLog p

example (p q : ProbDist (Fin 2)) (hsupp : ∀ a, 0 < p a → 0 < q a) :
    ∑ a, p a * Real.log (q a / p a) ≤ 0 :=
  gibbs_inequality p q hsupp

example : 0 ≤ entropyNat (uniformPNat 3) :=
  entropyNat_nonneg (uniformPNat 3)

example : entropyNat (uniformPNat 2) = Real.log 2 :=
  entropyNat_uniformPNat 2

example (p : ProbDist (Fin 3)) : entropyNat p ≤ Real.log 3 := by
  simpa [Fintype.card_fin] using entropyNat_le_log_card p

/-- Concrete non-equal pair: `gibbs_inequality` on `uniformPNat 2` against
the biased `(1/4, 3/4)` distribution on `Fin 2`. -/
example :
    let q : ProbDist (Fin 2) :=
      ⟨![1/4, 3/4], by
        refine ⟨fun i => ?_, ?_⟩
        · fin_cases i <;> norm_num
        · simp [Fin.sum_univ_two]; norm_num⟩
    ∑ a, (uniformPNat 2) a * Real.log (q a / (uniformPNat 2) a) ≤ 0 := by
  intro q
  refine gibbs_inequality (uniformPNat 2) q ?_
  intro a _
  fin_cases a <;> simp [q]
