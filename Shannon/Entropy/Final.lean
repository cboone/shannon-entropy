/-
SPDX-FileCopyrightText: 2026 Samuel Schlesinger
SPDX-FileCopyrightText: 2026 Christopher Boone
SPDX-License-Identifier: MIT
-/

import Shannon.Entropy.Approx

/-!
# Shannon.Entropy.Final

Final theorem layer.

Combines the rational characterization and continuity extension to prove:
- natural-log uniqueness (`entropyNat_unique`);
- base-parametric uniqueness (`entropyBase_unique`).

## Shannon narrative (Appendix 2, closing paragraph, p. 49)

This module states Shannon's **Theorem 2** (the uniqueness statement advertised at the top of Section 6 and proved across Appendix 2, pp. 48-49): any functional `H` satisfying the three axioms of continuity, monotonicity on uniforms, and grouping must be of the form `H p = -K ∑ p_i log p_i` for some positive constant `K`. The base-parametric restatement `entropyBase_unique` shows the constant rescales with the logarithm base, anchoring the "base choice = unit choice" reading that Shannon stresses in Section 1. The base-2 specialization lives in `Shannon/Entropy/Bits.lean`. The corresponding transcription entries are in `references/shannon1948-transcription.md` under the `## Formalization Cross-References` section.

## References

- [Shannon1948]: Claude E. Shannon, *A Mathematical Theory of Communication*, *Bell System Technical Journal* 27 (1948), Section 6 and Appendix 2, pp. 11-12, 48-49.
-/
namespace Shannon

noncomputable section
open Filter
open scoped Topology

/-! ## Final Characterization Theorems -/

/-! ### Theorem Index

- `entropyNat_unique`
- `entropyBase_unique`
-/

/--
Uniqueness in natural-log units:
every `H` satisfying the axiom bundle agrees with Shannon entropy up to the
positive multiplicative constant `K H`.
-/
theorem entropyNat_unique
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H)
    {α : Type} [Fintype α]
    (p : ProbDist α) :
    H p = -K H * ∑ a, p a * Real.log (p a) := by
  have hseq :
      ∀ N : ℕ, H (approxProb p N) = K H * entropyNat (approxProb p N) := by
    intro N
    have hN := entropyNat_approxProb H hH p N
    simpa [entropyNat, mul_assoc, mul_left_comm, mul_comm] using hN
  have hleft :
      Tendsto (fun N : ℕ => H (approxProb p N)) atTop (𝓝 (H p)) := by
    exact (hH.continuous (α := α)).continuousAt.tendsto.comp (tendsto_approxProb p)
  have hright :
      Tendsto (fun N : ℕ => K H * entropyNat (approxProb p N)) atTop (𝓝 (K H * entropyNat p)) := by
    have hcont : Continuous (fun q : ProbDist α => K H * entropyNat q) :=
      continuous_const.mul continuous_entropyNat
    exact hcont.continuousAt.tendsto.comp (tendsto_approxProb p)
  have hright' :
      Tendsto (fun N : ℕ => H (approxProb p N)) atTop (𝓝 (K H * entropyNat p)) := by
    convert hright using 1
    funext N
    exact hseq N
  have hlim : H p = K H * entropyNat p := tendsto_nhds_unique hleft hright'
  simpa [entropyNat, mul_assoc, mul_left_comm, mul_comm] using hlim

/--
Base-parametric uniqueness:
for each base `b > 1`, there is a positive constant `Kb` with
`H p = -Kb * ∑ p_i log_b p_i`.
-/
theorem entropyBase_unique
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H)
    (b : ℝ)
    (hb : 1 < b) :
    ∃ Kb : ℝ, 0 < Kb ∧
      ∀ {α : Type} [Fintype α] (p : ProbDist α),
        H p = -Kb * ∑ a, p a * Real.logb b (p a) := by
  refine ⟨K H * Real.log b, ?_, ?_⟩
  · exact mul_pos (K_pos H hH) (Real.log_pos hb)
  · intro α _ p
    have hb0 : b ≠ 0 := ne_of_gt (lt_trans (show (0 : ℝ) < 1 by norm_num) hb)
    have hb1 : b ≠ 1 := ne_of_gt hb
    have hb_pos : 0 < b := lt_trans (show (0 : ℝ) < 1 by norm_num) hb
    have hlogb_ne : Real.log b ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hb_pos hb1
    calc
      H p = -K H * ∑ a, p a * Real.log (p a) := entropyNat_unique H hH p
      _ = -(K H * Real.log b) * ∑ a, p a * Real.logb b (p a) := by
            have hsum :
                (∑ a, p a * Real.log (p a))
                  = Real.log b * (∑ a, p a * Real.logb b (p a)) := by
              calc
                (∑ a, p a * Real.log (p a))
                    = ∑ a, p a * (Real.log b * Real.logb b (p a)) := by
                        refine Finset.sum_congr rfl ?_
                        intro a _
                        have hterm :
                            Real.log (p a) = Real.log b * Real.logb b (p a) := by
                          unfold Real.logb
                          field_simp [hlogb_ne]
                        rw [hterm]
                _ = Real.log b * (∑ a, p a * Real.logb b (p a)) := by
                      rw [Finset.mul_sum]
                      refine Finset.sum_congr rfl ?_
                      intro a _
                      ring
            rw [hsum]
            ring


end

end Shannon
