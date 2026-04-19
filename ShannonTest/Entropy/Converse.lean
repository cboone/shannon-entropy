/-
SPDX-FileCopyrightText: 2026 Christopher Boone
SPDX-License-Identifier: Apache-2.0
-/

import Shannon.Entropy.Converse

/-!
# Shannon Entropy: Converse Tests

Exercises for relabel invariance, uniform monotonicity, grouping, and the
axiom bundle for `entropyNat`.
-/

open Shannon

example : ShannonEntropyAxioms (fun {α} [Fintype α] => entropyNat) :=
  entropyNat_shannonAxioms

example :
    entropyNat (relabelProb (Equiv.swap (0 : Fin 2) (1 : Fin 2)) (uniformPNat 2))
      = entropyNat (uniformPNat 2) :=
  entropyNat_relabelInvariant (Equiv.swap (0 : Fin 2) (1 : Fin 2)) (uniformPNat 2)

example : entropyNat (uniformPNat 2) < entropyNat (uniformPNat 3) :=
  entropyNat_uniformMonotone (by decide)

example (p : ProbDist (Fin 2)) (q : (a : Fin 2) → ProbDist (Fin 1)) :
    entropyNat (composeProb p q) = entropyNat p + ∑ a, p a * entropyNat (q a) :=
  entropyNat_grouping p q
