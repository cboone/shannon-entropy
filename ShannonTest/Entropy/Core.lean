/-
SPDX-FileCopyrightText: 2026 Christopher Boone
SPDX-License-Identifier: Apache-2.0
-/

import Shannon.Entropy.Core

/-!
# Shannon Entropy: Core Smoke Tests

Exercises for `ProbDist`, `uniformPNat`, and basic simplex lemmas.
-/

open Shannon

example : (uniformPNat 1 : ProbDist (Fin 1)) (0 : Fin 1) = 1 := by
  norm_num [uniformPNat]

example : (uniformPNat 2 : ProbDist (Fin 2)) (0 : Fin 2) = 1 / 2 := by
  norm_num [uniformPNat]

example : (∑ a, (uniformPNat 3 : ProbDist (Fin 3)) a) = 1 :=
  prob_sum_eq_one (uniformPNat 3)

example (a : Fin 4) : 0 ≤ (uniformPNat 4 : ProbDist (Fin 4)) a :=
  prob_nonneg (uniformPNat 4) a

example (a : Fin 2) : (uniformPNat 2 : ProbDist (Fin 2)) a ≤ 1 :=
  prob_le_one (uniformPNat 2) a
