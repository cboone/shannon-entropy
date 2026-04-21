/-
SPDX-FileCopyrightText: 2026 Christopher Boone
SPDX-License-Identifier: Apache-2.0
-/

import Shannon.Entropy.Joint

/-!
# Shannon Entropy: Joint Tests

Exercises for marginals, product distributions, conditional entropy, mutual
information, and the chain rule.
-/

open Shannon

example :
    marginalFst (prodDist (uniformPNat 2) (uniformPNat 3)) = uniformPNat 2 :=
  marginalFst_prodDist (uniformPNat 2) (uniformPNat 3)

example :
    marginalSnd (prodDist (uniformPNat 2) (uniformPNat 3)) = uniformPNat 3 :=
  marginalSnd_prodDist (uniformPNat 2) (uniformPNat 3)

example :
    entropyNat (prodDist (uniformPNat 2) (uniformPNat 3))
      = entropyNat (uniformPNat 2) + entropyNat (uniformPNat 3) :=
  entropyNat_prodDist (uniformPNat 2) (uniformPNat 3)

example :
    entropyNat (prodDist (uniformPNat 2) (uniformPNat 1))
      = entropyNat (marginalFst (prodDist (uniformPNat 2) (uniformPNat 1)))
          + condEntropy (prodDist (uniformPNat 2) (uniformPNat 1)) :=
  chain_rule (prodDist (uniformPNat 2) (uniformPNat 1))

example : IsIndependent (prodDist (uniformPNat 2) (uniformPNat 3)) := by
  intro a b
  rw [marginalFst_prodDist, marginalSnd_prodDist]
  rfl

example : condEntropy (prodDist (uniformPNat 2) (uniformPNat 1)) = 0 := by
  have hchain := chain_rule (prodDist (uniformPNat 2) (uniformPNat 1))
  rw [marginalFst_prodDist] at hchain
  have hprod := entropyNat_prodDist (uniformPNat 2) (uniformPNat 1)
  have h1 : entropyNat (uniformPNat 1) = 0 := by
    simpa using entropyNat_uniformPNat 1
  linarith

example :
    let p := prodDist (uniformPNat 2) (uniformPNat 3)
    condEntropy p = -∑ a, ∑ b, p (a, b) * Real.log (p (a, b) / marginalFst p a) :=
  condEntropy_eq_shannon_form _
