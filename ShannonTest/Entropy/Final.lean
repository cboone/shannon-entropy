import Shannon.Entropy.Final

/-!
# Shannon Entropy: Uniqueness Tests

Exercises for the main characterization theorems.
-/

open Shannon

/-- Uniqueness (nat log form): any H satisfying the axioms equals
-K * ∑ p_i log p_i. -/
example (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H) {α : Type} [Fintype α] (p : ProbDist α) :
    H p = -K H * ∑ a, p a * Real.log (p a) :=
  entropyNat_unique H hH p

/-- Uniqueness (arbitrary base form): for each base b > 1, there exists a
positive constant Kb such that H p = -Kb * ∑ p_i log_b p_i. -/
example (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H) (b : ℝ) (hb : 1 < b) :
    ∃ Kb : ℝ, 0 < Kb ∧
      ∀ {α : Type} [Fintype α] (p : ProbDist α),
        H p = -Kb * ∑ a, p a * Real.logb b (p a) :=
  entropyBase_unique H hH b hb
