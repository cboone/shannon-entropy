import Shannon.Entropy.MutualInfo

/-!
# Shannon Entropy: Mutual Information Tests

Exercises for the public mutual-information API and the information-form DPI.
-/

open Shannon

noncomputable section

private def constKernel : Fin 3 → ProbDist (Fin 2) := fun _ => uniformPNat 2

example :
    mutualInfo (prodDist (uniformPNat 2) (uniformPNat 1)) = 0 := by
  rw [mutualInfo_eq_zero_iff_independent]
  intro a b
  rw [marginalFst_prodDist, marginalSnd_prodDist]
  rfl

example :
    mutualInfoBits (prodDist (uniformPNat 2) (uniformPNat 3)) = 0 := by
  have hnat : mutualInfo (prodDist (uniformPNat 2) (uniformPNat 3)) = 0 := by
    rw [mutualInfo_eq_zero_iff_independent]
    intro a b
    rw [marginalFst_prodDist, marginalSnd_prodDist]
    rfl
  unfold mutualInfoBits
  rw [hnat]
  simp

example :
    mutualInfo (prodDist (uniformPNat 2) (uniformPNat 3))
      = relEntropy (prodDist (uniformPNat 2) (uniformPNat 3))
          (prodDist (marginalFst (prodDist (uniformPNat 2) (uniformPNat 3)))
            (marginalSnd (prodDist (uniformPNat 2) (uniformPNat 3)))) :=
  mutualInfo_eq_relEntropy_prodMarginals _

example (p : ProbDist (Fin 2 × Fin 3)) : 0 ≤ mutualInfo p :=
  mutualInfo_nonneg p

example (p : ProbDist (Fin 2 × Fin 3)) :
    mutualInfo p = mutualInfo (swapJoint p) :=
  mutualInfo_symm p

example (p : ProbDist (Fin 2 × Fin 3)) :
    mutualInfo p = entropyNat (marginalFst p) - condEntropy (swapJoint p) :=
  mutualInfo_eq_entropyFst_sub_condEntropy_swap p

example (p : ProbDist (Fin 2 × Fin 3)) :
    mutualInfo p = entropyNat (marginalSnd p) - condEntropy p :=
  mutualInfo_eq_entropySnd_sub_condEntropy p

example :
    mutualInfo (diagonalDist (uniformPNat 2)) = entropyNat (uniformPNat 2) :=
  mutualInfo_self _

example (p : ProbDist (Fin 2 × Fin 3)) : mutualInfo p ≤ entropyNat (marginalFst p) :=
  mutualInfo_le_entropyFst p

example (p : ProbDist (Fin 2 × Fin 3)) : mutualInfo p ≤ entropyNat (marginalSnd p) :=
  mutualInfo_le_entropySnd p

example (p : ProbDist (Fin 2 × Fin 3)) : 0 ≤ mutualInfoBits p :=
  mutualInfoBits_nonneg p

example (p : ProbDist (Fin 2 × Fin 3)) : mutualInfoBits p = mutualInfoBits (swapJoint p) :=
  mutualInfoBits_symm p

example (p : ProbDist (Fin 2 × Fin 3)) :
    mutualInfoBits p = entropyBits (marginalFst p) - condEntropyBits (swapJoint p) :=
  mutualInfoBits_eq_entropyBitsFst_sub_condEntropyBits_swap p

example (p : ProbDist (Fin 2 × Fin 3)) :
    mutualInfoBits p = entropyBits (marginalSnd p) - condEntropyBits p :=
  mutualInfoBits_eq_entropyBitsSnd_sub_condEntropyBits p

example :
    mutualInfoBits (diagonalDist (uniformPNat 2)) = entropyBits (uniformPNat 2) :=
  mutualInfoBits_self _

example (p : ProbDist (Fin 2 × Fin 3)) : mutualInfoBits p ≤ entropyBits (marginalFst p) :=
  mutualInfoBits_le_entropyBitsFst p

example (p : ProbDist (Fin 2 × Fin 3)) : mutualInfoBits p ≤ entropyBits (marginalSnd p) :=
  mutualInfoBits_le_entropyBitsSnd p

example (p : ProbDist (Fin 2 × Fin 3)) :
    marginalFst (swapJoint p) = marginalSnd p :=
  marginalFst_swapJoint p

example (p : ProbDist (Fin 2 × Fin 3)) :
    marginalSnd (swapJoint p) = marginalFst p :=
  marginalSnd_swapJoint p

example (p : ProbDist (Fin 2 × Fin 3)) :
    entropyNat (swapJoint p) = entropyNat p :=
  entropyNat_swapJoint p

example :
    marginalFst (diagonalDist (uniformPNat 2)) = uniformPNat 2 :=
  marginalFst_diagonalDist _

example :
    marginalSnd (diagonalDist (uniformPNat 2)) = uniformPNat 2 :=
  marginalSnd_diagonalDist _

example :
    entropyNat (diagonalDist (uniformPNat 2)) = entropyNat (uniformPNat 2) :=
  entropyNat_diagonalDist _

example :
    marginalFst (kernelPushforward (prodDist (uniformPNat 2) (uniformPNat 3)) constKernel)
      = marginalFst (prodDist (uniformPNat 2) (uniformPNat 3)) :=
  marginalFst_kernelPushforward _ _

example (c : Fin 2) :
    marginalSnd (kernelPushforward (prodDist (uniformPNat 2) (uniformPNat 3)) constKernel) c
      = ∑ b, marginalSnd (prodDist (uniformPNat 2) (uniformPNat 3)) b * constKernel b c :=
  marginalSnd_kernelPushforward _ _ c

example :
    mutualInfo (kernelPushforward (prodDist (uniformPNat 2) (uniformPNat 3)) constKernel)
      ≤ mutualInfo (prodDist (uniformPNat 2) (uniformPNat 3)) :=
  mutualInfo_kernelPushforward_le _ _

example :
    mutualInfoBits (kernelPushforward (prodDist (uniformPNat 2) (uniformPNat 3)) constKernel)
      ≤ mutualInfoBits (prodDist (uniformPNat 2) (uniformPNat 3)) :=
  mutualInfoBits_kernelPushforward_le _ _
