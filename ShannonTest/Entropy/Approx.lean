/-
SPDX-FileCopyrightText: 2026 Christopher Boone
SPDX-License-Identifier: Apache-2.0
-/

import Shannon.Entropy.Approx
import Shannon.Entropy.Converse

/-!
# Shannon Entropy: Approximation Tests

Exercises for floor-count approximants, their entropy formula, and convergence
to the target distribution.
-/

open Shannon Filter
open scoped Topology

example : 0 < approxCount (uniformPNat 2) 0 (0 : Fin 2) :=
  approxCount_pos (uniformPNat 2) 0 (0 : Fin 2)

example : 0 < approxTotal (uniformPNat 2) 0 :=
  approxTotal_pos (uniformPNat 2) 0

example :
    approxProb (uniformPNat 2) 0 (0 : Fin 2)
      = (approxCount (uniformPNat 2) 0 (0 : Fin 2) : ℝ) / (approxTotal (uniformPNat 2) 0 : ℝ) :=
  approxProb_apply (uniformPNat 2) 0 (0 : Fin 2)

example :
    entropyNat (approxProb (uniformPNat 2) 3)
      = -K entropyNat * ∑ a, approxProb (uniformPNat 2) 3 a * Real.log (approxProb (uniformPNat 2) 3 a) :=
  entropyNat_approxProb entropyNat entropyNat_shannonAxioms (uniformPNat 2) 3

example :
    |approxProb (uniformPNat 2) 3 (0 : Fin 2) - (uniformPNat 2 : ProbDist (Fin 2)) 0|
      ≤ ((Fintype.card (Fin 2) : ℝ) + 1) / (((3 + 1 : ℕ) : ℝ)) := by
  simpa using approxProb_error_bound (uniformPNat 2) 3 (0 : Fin 2)

example :
    Tendsto (fun N : ℕ => approxProb (uniformPNat 2) N) atTop (𝓝 (uniformPNat 2)) :=
  tendsto_approxProb (uniformPNat 2)
