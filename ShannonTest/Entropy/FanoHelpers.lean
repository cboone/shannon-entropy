import Shannon.Entropy.FanoHelpers

/-!
# Shannon Entropy: Fano Helpers Tests

Exercises for the public helper API that underpins `fanoInequality`.
-/

open Shannon

noncomputable section

example (p : ProbDist (Fin 2 × Fin 3)) (y : Fin 3) : ProbDist (Fin 2) :=
  condDistFstGivenSnd p y

example (p : ProbDist (Fin 2 × Fin 3)) (y : Fin 3) (x : Fin 2) :
    marginalSnd p y * condDistFstGivenSnd p y x = p (x, y) :=
  marginalSnd_mul_condDistFstGivenSnd p y x

example (p : ProbDist (Fin 2 × Fin 3)) :
    condEntropy (swapJoint p) = ∑ y, marginalSnd p y * entropyNat (condDistFstGivenSnd p y) :=
  condEntropy_swapJoint_eq_sum_marginalSnd_entropyNat_condDistFstGivenSnd p

example (r : ProbDist (Fin 2)) (a0 : Fin 2) :
    entropyNat r ≤ Real.qaryEntropy (Fintype.card (Fin 2)) (1 - r a0) :=
  entropyNat_le_qaryEntropy_at_distinguished r a0
