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
