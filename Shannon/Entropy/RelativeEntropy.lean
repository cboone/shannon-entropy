/-
SPDX-FileCopyrightText: 2026 Christopher Boone
SPDX-License-Identifier: Apache-2.0
-/

import Shannon.Entropy.Bits

/-!
# Shannon.Entropy.RelativeEntropy

Finite-alphabet relative entropy (Kullback-Leibler divergence) and the log-sum
inequality.

This module packages the support condition already used implicitly by
`gibbs_inequality`, defines relative entropy in nats and in bits, restates
Gibbs' inequality as KL nonnegativity, characterizes the zero case, and proves
the log-sum inequality in the finite setting.

## Main definitions

- `Supports`: support-covering predicate for finite distributions
- `relEntropy`: relative entropy in nats
- `relEntropyBits`: relative entropy in bits

## Main results

- `relEntropy_nonneg`: Gibbs' inequality restated as KL nonnegativity
- `relEntropy_eq_zero_iff`: KL vanishes exactly on equal distributions
- `log_sum_inequality`: the finite log-sum inequality
-/
namespace Shannon

noncomputable section
open Finset Real InformationTheory

/-- `Supports q p` asserts that `q` covers the support of `p`: whenever `p a > 0`, also `q a > 0`. The standard finite-alphabet support predicate for KL divergence and Gibbs-style inequalities. -/
def Supports {α : Type} [Fintype α] (q p : ProbDist α) : Prop :=
  ∀ a, 0 < p a → 0 < q a

/-- Relative entropy (Kullback-Leibler divergence) in nats: `D(p ‖ q) = ∑ p_i log (p_i / q_i)`.

Defined as a total function. The value is mathematically meaningful only when `q` covers the support of `p` (`Supports q p`); Lean's conventions `Real.log 0 = 0` and `0 / 0 = 0` keep the expression finite even outside support, but theorems below require the support hypothesis. -/
def relEntropy {α : Type} [Fintype α] (p q : ProbDist α) : ℝ :=
  ∑ a, p a * Real.log (p a / q a)

/-- Base-2 relative entropy (KL divergence in bits). -/
def relEntropyBits {α : Type} [Fintype α] (p q : ProbDist α) : ℝ :=
  relEntropy p q / Real.log 2

private theorem relEntropy_eq_neg_gibbs_sum {α : Type} [Fintype α]
    (p q : ProbDist α) (hsupp : Supports q p) :
    relEntropy p q = -∑ a, p a * Real.log (q a / p a) := by
  unfold relEntropy
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro a _
  by_cases hp : p a = 0
  · simp [hp]
  · have hpa : 0 < p a := lt_of_le_of_ne (prob_nonneg p a) (Ne.symm hp)
    have hqa : 0 < q a := hsupp a hpa
    rw [Real.log_div (ne_of_gt hpa) (ne_of_gt hqa), Real.log_div (ne_of_gt hqa) (ne_of_gt hpa)]
    ring

private theorem relEntropy_eq_klFun_sum {α : Type} [Fintype α]
    (p q : ProbDist α) (hsupp : Supports q p) :
    relEntropy p q = ∑ a, q a * InformationTheory.klFun (p a / q a) := by
  unfold relEntropy
  have hterm : ∀ a, p a * Real.log (p a / q a) = q a * InformationTheory.klFun (p a / q a) + (p a - q a) := by
    intro a
    by_cases hq : q a = 0
    · have hp : p a = 0 := by
        by_cases hp : p a = 0
        · exact hp
        · have hpa : 0 < p a := lt_of_le_of_ne (prob_nonneg p a) (Ne.symm hp)
          exact False.elim ((hsupp a hpa).ne' hq)
      simp [hq, hp, InformationTheory.klFun_zero]
    · rw [InformationTheory.klFun_apply]
      field_simp [hq]
      ring
  calc
    ∑ a, p a * Real.log (p a / q a) = ∑ a, (q a * InformationTheory.klFun (p a / q a) + (p a - q a)) := by
      refine Finset.sum_congr rfl ?_
      intro a _
      exact hterm a
    _ = (∑ a, q a * InformationTheory.klFun (p a / q a)) + ∑ a, (p a - q a) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ a, q a * InformationTheory.klFun (p a / q a) := by
      rw [Finset.sum_sub_distrib, prob_sum_eq_one, prob_sum_eq_one, sub_self, add_zero]

/-- Relative entropy is nonnegative. -/
theorem relEntropy_nonneg {α : Type} [Fintype α]
    (p q : ProbDist α) (hsupp : Supports q p) :
    0 ≤ relEntropy p q := by
  have hgibbs := gibbs_inequality p q hsupp
  rw [relEntropy_eq_neg_gibbs_sum p q hsupp]
  linarith

/-- Base-2 relative entropy is nonnegative. -/
theorem relEntropyBits_nonneg {α : Type} [Fintype α]
    (p q : ProbDist α) (hsupp : Supports q p) :
    0 ≤ relEntropyBits p q := by
  unfold relEntropyBits
  exact div_nonneg (relEntropy_nonneg p q hsupp) (Real.log_nonneg (by norm_num))

/-- Relative entropy vanishes exactly when the two distributions agree pointwise. -/
theorem relEntropy_eq_zero_iff
    {α : Type} [Fintype α] (p q : ProbDist α) (hsupp : Supports q p) :
    relEntropy p q = 0 ↔ ∀ a, p a = q a := by
  constructor
  · intro h
    have hsum : ∑ a, q a * InformationTheory.klFun (p a / q a) = 0 := by
      simpa [relEntropy_eq_klFun_sum p q hsupp] using h
    have hnonneg : ∀ a ∈ Finset.univ, 0 ≤ q a * InformationTheory.klFun (p a / q a) := by
      intro a _
      by_cases hq : q a = 0
      · simp [hq]
      · have hq_pos : 0 < q a := lt_of_le_of_ne (prob_nonneg q a) (Ne.symm hq)
        exact mul_nonneg (prob_nonneg q a) (InformationTheory.klFun_nonneg (div_nonneg (prob_nonneg p a) hq_pos.le))
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
    intro a
    by_cases hq : q a = 0
    · have hp : p a = 0 := by
        by_cases hp : p a = 0
        · exact hp
        · have hpa : 0 < p a := lt_of_le_of_ne (prob_nonneg p a) (Ne.symm hp)
          exact False.elim ((hsupp a hpa).ne' hq)
      simp [hp, hq]
    · have hq_pos : 0 < q a := lt_of_le_of_ne (prob_nonneg q a) (Ne.symm hq)
      have hkl : InformationTheory.klFun (p a / q a) = 0 := by
        exact (mul_eq_zero.mp (hterms a (Finset.mem_univ a))).resolve_left hq
      have hratio : p a / q a = 1 :=
        (InformationTheory.klFun_eq_zero_iff (div_nonneg (prob_nonneg p a) hq_pos.le)).mp hkl
      simpa using (div_eq_iff hq).mp hratio
  · intro hpq
    unfold relEntropy
    apply Finset.sum_eq_zero
    intro a _
    rw [hpq a]
    by_cases hp : p a = 0
    · have hq : q a = 0 := by simpa [hpq a] using hp
      simp [hq]
    · have hpa : 0 < p a := lt_of_le_of_ne (prob_nonneg p a) (Ne.symm hp)
      have hqa : 0 < q a := by simpa [hpq a] using hpa
      rw [div_self (ne_of_gt hqa), Real.log_one]
      ring

/-- Relative entropy of a distribution with itself is zero. -/
theorem relEntropy_self {α : Type} [Fintype α] (p : ProbDist α) :
    relEntropy p p = 0 :=
  (relEntropy_eq_zero_iff p p (fun _ h => h)).2 fun _ => rfl

/-- **Log-sum inequality**: for nonnegative sequences `a, b : α → ℝ` with `A = ∑ aᵢ`, `B = ∑ bᵢ`, and support condition `∀ i, 0 < a i → 0 < b i`:
    `∑ i, a i * log (a i / b i) ≥ A * log (A / B)`.

The statement is total: if `A = 0`, both sides are `0`; if `A > 0`, the support hypothesis forces `B > 0`, so the normalized probability-distribution proof applies. -/
theorem log_sum_inequality
    {α : Type} [Fintype α]
    (a b : α → ℝ)
    (ha_nonneg : ∀ i, 0 ≤ a i) (hb_nonneg : ∀ i, 0 ≤ b i)
    (hsupp : ∀ i, 0 < a i → 0 < b i) :
    (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) ≤
      ∑ i, a i * Real.log (a i / b i) := by
  classical
  let A : ℝ := ∑ i, a i
  let B : ℝ := ∑ i, b i
  by_cases hA : A = 0
  · have ha_zero : ∀ i, a i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => ha_nonneg j)).mp (by simpa [A] using hA) i (Finset.mem_univ i)
    have hrhs : ∑ i, a i * Real.log (a i / b i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp [ha_zero i]
    simp [A, hA, hrhs]
  · have hA_pos : 0 < A := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => ha_nonneg i) (Ne.symm hA)
    have hex : ∃ i, 0 < a i := by
      by_contra hnone
      push Not at hnone
      have hA_zero : A = 0 := by
        apply le_antisymm
        · simpa [A] using Finset.sum_nonpos fun i _ => hnone i
        · exact Finset.sum_nonneg fun i _ => ha_nonneg i
      exact hA hA_zero
    obtain ⟨i0, hi0⟩ := hex
    have hB_pos : 0 < B := by
      exact lt_of_lt_of_le (hsupp i0 hi0)
        (by simpa [B] using (Finset.single_le_sum (fun i _ => hb_nonneg i) (Finset.mem_univ i0)))
    let p : ProbDist α := by
      refine ⟨fun i => a i / A, ?_⟩
      constructor
      · intro i
        exact div_nonneg (ha_nonneg i) hA_pos.le
      · calc
          ∑ i, a i / A = (∑ i, a i) / A := by rw [Finset.sum_div]
          _ = 1 := by simp [A, hA_pos.ne']
    let q : ProbDist α := by
      refine ⟨fun i => b i / B, ?_⟩
      constructor
      · intro i
        exact div_nonneg (hb_nonneg i) hB_pos.le
      · calc
          ∑ i, b i / B = (∑ i, b i) / B := by rw [Finset.sum_div]
          _ = 1 := by simp [B, hB_pos.ne']
    have hpq_supp : Supports q p := by
      intro i hpi
      show 0 < b i / B
      have hai : 0 < a i := by
        dsimp [p] at hpi
        exact (div_pos_iff_of_pos_right hA_pos).mp hpi
      exact (div_pos_iff_of_pos_right hB_pos).2 (hsupp i hai)
    have hrewrite :
        ∑ i, a i * Real.log (a i / b i) = A * Real.log (A / B) + A * relEntropy p q := by
      calc
        ∑ i, a i * Real.log (a i / b i)
            = ∑ i, (a i * Real.log (A / B) + A * (p i * Real.log (p i / q i))) := by
                refine Finset.sum_congr rfl ?_
                intro i _
                by_cases hai0 : a i = 0
                · have hpi0 : p i = 0 := by
                    dsimp [p]
                    simp [hai0]
                  simp [hai0, hpi0]
                · have hai : 0 < a i := lt_of_le_of_ne (ha_nonneg i) (Ne.symm hai0)
                  have hbi : 0 < b i := hsupp i hai
                  have hpi : 0 < p i := by
                    dsimp [p]
                    exact (div_pos_iff_of_pos_right hA_pos).2 hai
                  have hqi : 0 < q i := by
                    dsimp [q]
                    exact (div_pos_iff_of_pos_right hB_pos).2 hbi
                  have hratio : a i / b i = (A / B) * (p i / q i) := by
                    dsimp [p, q]
                    field_simp [hA_pos.ne', hB_pos.ne', hbi.ne']
                  have ha_eq : a i = A * p i := by
                    dsimp [p]
                    field_simp [hA_pos.ne']
                  rw [hratio, Real.log_mul (ne_of_gt (div_pos hA_pos hB_pos)) (ne_of_gt (div_pos hpi hqi)), mul_add, ha_eq]
                  ring
        _ = (∑ i, a i * Real.log (A / B)) + ∑ i, A * (p i * Real.log (p i / q i)) := by
              rw [Finset.sum_add_distrib]
        _ = A * Real.log (A / B) + A * relEntropy p q := by
              rw [Finset.sum_mul, ← Finset.mul_sum, relEntropy]
    have hkl_nonneg : 0 ≤ relEntropy p q := relEntropy_nonneg p q hpq_supp
    have hineq : A * Real.log (A / B) ≤ A * Real.log (A / B) + A * relEntropy p q := by
      nlinarith [hkl_nonneg, hA_pos]
    simpa [A, B] using hineq.trans_eq hrewrite.symm

end

end Shannon
