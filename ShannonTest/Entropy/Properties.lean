/-
SPDX-FileCopyrightText: 2026 Christopher Boone
SPDX-License-Identifier: Apache-2.0
-/

import Shannon.Entropy.Properties
import Shannon.Entropy.Joint

/-!
# Shannon Entropy: Properties Tests

Exercises for Section 6 entropy properties: non-negativity, deterministic iff,
uniform maximum, subadditivity, Schur-concavity, conditioning, and chain rule.
-/

open Shannon

/-- Entropy of any distribution is non-negative. -/
example : 0 ≤ entropyNat (uniformPNat 4) :=
  entropyNat_nonneg (uniformPNat 4)

/-- Entropy of the uniform distribution on n outcomes equals log n. -/
example : entropyNat (uniformPNat 2) = Real.log 2 :=
  entropyNat_uniformPNat 2

/-- Entropy of the uniform distribution on 1 outcome equals log 1 (= 0). -/
example : entropyNat (uniformPNat 1) = 0 := by
  have h := entropyNat_uniformPNat 1
  simp at h
  exact h

/-- Entropy is bounded above by log of the alphabet size. -/
example (p : ProbDist (Fin 4)) : entropyNat p ≤ Real.log 4 := by
  have h := entropyNat_le_log_card p
  simp [Fintype.card_fin] at h
  exact h

/-- Conditional entropy is non-negative. -/
example (pxy : ProbDist (Fin 2 × Fin 2)) : 0 ≤ condEntropy pxy :=
  condEntropy_nonneg pxy

/-- Conditioning reduces entropy. -/
example (pxy : ProbDist (Fin 2 × Fin 2)) :
    condEntropy pxy ≤ entropyNat (marginalSnd pxy) :=
  condEntropy_le_entropyNat pxy

/-- Product distribution entropy decomposes additively. -/
example (p : ProbDist (Fin 2)) (q : ProbDist (Fin 3)) :
    entropyNat (prodDist p q) = entropyNat p + entropyNat q :=
  entropyNat_prodDist p q
