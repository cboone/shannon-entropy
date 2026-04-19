import Shannon.Entropy.RelativeEntropy

/-!
# Shannon Entropy: Relative Entropy Tests

Exercises for the public KL-divergence API.
-/

open Shannon

example : Supports (uniformPNat 2) (uniformPNat 2) := by
  intro a _
  positivity

example : relEntropy (uniformPNat 2) (uniformPNat 2) = 0 :=
  relEntropy_self _

example : 0 ≤ relEntropy (uniformPNat 2) (uniformPNat 2) :=
  relEntropy_nonneg _ _ (by intro a h; exact h)

example : 0 ≤ relEntropyBits (uniformPNat 2) (uniformPNat 2) :=
  relEntropyBits_nonneg _ _ (by intro a h; exact h)

example : relEntropy (uniformPNat 2) (uniformPNat 2) = 0 ↔ ∀ a, (uniformPNat 2) a = (uniformPNat 2) a :=
  relEntropy_eq_zero_iff _ _ (by intro a h; exact h)

example :
    (∑ i, (uniformPNat 2) i) * Real.log ((∑ i, (uniformPNat 2) i) / (∑ i, (uniformPNat 2) i))
      ≤ ∑ i, (uniformPNat 2) i * Real.log ((uniformPNat 2) i / (uniformPNat 2) i) := by
  exact log_sum_inequality
    (fun i : Fin 2 => (uniformPNat 2) i)
    (fun i : Fin 2 => (uniformPNat 2) i)
    (fun i => prob_nonneg (uniformPNat 2) i)
    (fun i => prob_nonneg (uniformPNat 2) i)
    (fun i h => h)
