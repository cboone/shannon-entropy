/-
SPDX-FileCopyrightText: 2026 Christopher Boone
SPDX-License-Identifier: Apache-2.0
-/

import Shannon.Entropy.IID
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Shannon.Entropy.AEP

Finite concentration and the i.i.d. asymptotic equipartition property.

This module proves the i.i.d. case of Shannon's Theorem 3 and the cardinality
bounds that feed the i.i.d. form of Theorem 4.

## Main results

- `chebyshev_finite`: Chebyshev's inequality on a finite probability
  distribution
- `aep_iid`: i.i.d. AEP in base 2
- `typicalSet_iidDist_card_le`, `typicalSet_iidDist_card_ge`: typical-set
  cardinality bounds
- `minCover`, `tendsto_logb_minCover_iid`: Shannon's Theorem 4 in minimum-cover
  form for the i.i.d. case
-/

namespace Shannon

noncomputable section
open Filter
open Finset Real MeasureTheory
open scoped ProbabilityTheory Topology

section Discrete

variable {α : Type} [Fintype α]

/-- Finite alphabets use the discrete measurable structure in this module's local PMF bridge. -/
@[reducible] local instance instMeasurableSpace_shannon : MeasurableSpace α := ⊤

private def probDistToPMF (p : ProbDist α) : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (p a)) <| by
    simpa [prob_sum_eq_one p] using
      (ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (f := fun a => p a)
        (fun a _ => prob_nonneg p a)).symm

private lemma probDistToPMF_apply_toReal (p : ProbDist α) (a : α) :
    ((probDistToPMF p) a).toReal = p a := by
  simp [probDistToPMF, prob_nonneg]

private lemma probDist_integral_eq_sum (p : ProbDist α) (f : α → ℝ) :
    ∫ a, f a ∂(probDistToPMF p).toMeasure = ∑ a, p a * f a := by
  simp [PMF.integral_eq_sum, probDistToPMF_apply_toReal, smul_eq_mul]

private lemma probDist_variance_eq_sum (p : ProbDist α) (f : α → ℝ) :
    Var[f; (probDistToPMF p).toMeasure]
      = ∑ a, p a * (f a - ∑ b, p b * f b) ^ 2 := by
  have hmean : ∫ a, f a ∂(probDistToPMF p).toMeasure = ∑ b, p b * f b :=
    probDist_integral_eq_sum p f
  rw [ProbabilityTheory.variance_eq_integral]
  · simpa [hmean] using
      (probDist_integral_eq_sum p (fun a => (f a - ∫ b, f b ∂(probDistToPMF p).toMeasure) ^ 2))
  · exact Measurable.aemeasurable (by fun_prop)

private lemma iidDist_toPMF_eq_pi (p : ProbDist α) (N : ℕ) :
    probDistToPMF (iidDist p N)
      = (Measure.pi fun _ : Fin N => (probDistToPMF p).toMeasure).toPMF := by
  ext x
  rw [Measure.toPMF_apply, Measure.pi_singleton]
  change ENNReal.ofReal ((iidDist p N) x) = ∏ i, (probDistToPMF p).toMeasure {x i}
  rw [iidDist_apply, ENNReal.ofReal_prod_of_nonneg (fun i _ => prob_nonneg p (x i))]
  refine Finset.prod_congr rfl ?_
  intro i _
  simpa [probDistToPMF] using
    (PMF.toMeasure_apply_singleton (p := probDistToPMF p) (a := x i) (MeasurableSet.singleton _)).symm

private lemma iidDist_toMeasure_eq_pi (p : ProbDist α) (N : ℕ) :
    (probDistToPMF (iidDist p N)).toMeasure
      = Measure.pi fun _ : Fin N => (probDistToPMF p).toMeasure := by
  rw [iidDist_toPMF_eq_pi, Measure.toPMF_toMeasure]

/-- Finite Chebyshev inequality on a finite probability distribution. -/
theorem chebyshev_finite
    (p : ProbDist α) (f : α → ℝ) (ε : ℝ) (hε : 0 < ε) :
    (∑ a ∈ Finset.univ.filter (fun a => ε ≤ |f a - (∑ b, p b * f b)|), p a) ≤
      (∑ a, p a * (f a - (∑ b, p b * f b)) ^ 2) / ε ^ 2 := by
  let μ := (probDistToPMF p).toMeasure
  let s : Finset α := Finset.univ.filter fun a => ε ≤ |f a - (∑ b, p b * f b)|
  have hLp : MemLp f 2 μ := by
    exact MemLp.of_bound (Measurable.aestronglyMeasurable (by fun_prop))
      (∑ a, |f a|) <| Filter.Eventually.of_forall fun a => by
        simp only [Real.norm_eq_abs]
        exact Finset.single_le_sum (fun b _ => abs_nonneg (f b)) (Finset.mem_univ a)
  have hmean : μ[f] = ∑ b, p b * f b := probDist_integral_eq_sum p f
  have hraw := ProbabilityTheory.meas_ge_le_variance_div_sq (μ := μ) (X := f) hLp hε
  have hs : μ {a | ε ≤ |f a - ∑ b, p b * f b|} = ENNReal.ofReal (∑ a ∈ s, p a) := by
    calc
      μ {a | ε ≤ |f a - ∑ b, p b * f b|}
          = ∑ a, {a | ε ≤ |f a - ∑ b, p b * f b|}.indicator (probDistToPMF p) a := by
              rw [PMF.toMeasure_apply_fintype]
      _ = ∑ a, ENNReal.ofReal (if ε ≤ |f a - ∑ b, p b * f b| then p a else 0) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases ha : ε ≤ |f a - ∑ b, p b * f b|
            · simp [ha, probDistToPMF]
            · simp [ha, probDistToPMF]
      _ = ENNReal.ofReal (∑ a, if ε ≤ |f a - ∑ b, p b * f b| then p a else 0) := by
            symm
            exact ENNReal.ofReal_sum_of_nonneg fun a _ => by
              split_ifs <;> simp [prob_nonneg p a]
      _ = ENNReal.ofReal (∑ a ∈ s, p a) := by
            simp [s, Finset.sum_filter]
  have hvar : Var[f; μ] = ∑ a, p a * (f a - ∑ b, p b * f b) ^ 2 :=
    probDist_variance_eq_sum p f
  have hbound : ENNReal.ofReal (∑ a ∈ s, p a)
      ≤ ENNReal.ofReal ((∑ a, p a * (f a - ∑ b, p b * f b) ^ 2) / ε ^ 2) := by
    have hraw' : μ {a | ε ≤ |f a - ∑ b, p b * f b|} ≤ ENNReal.ofReal (Var[f; μ] / ε ^ 2) := by
      simpa [hmean] using hraw
    rw [hs, hvar] at hraw'
    exact hraw'
  have hsum_nonneg : 0 ≤ ∑ a, p a * (f a - ∑ b, p b * f b) ^ 2 := by
    exact Finset.sum_nonneg fun a _ => mul_nonneg (prob_nonneg p a) (sq_nonneg _)
  have hright_nonneg : 0 ≤ ((∑ a, p a * (f a - ∑ b, p b * f b) ^ 2) / ε ^ 2) := by
    exact div_nonneg hsum_nonneg (sq_nonneg ε)
  exact (ENNReal.ofReal_le_ofReal_iff hright_nonneg).mp hbound

private def sampleMeanLogProbBits (p : ProbDist α) (N : ℕ) (x : Fin N → α) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, logProbBits p (x i)

private def goodShell [DecidableEq α] (p : ProbDist α) (N : ℕ) (ε : ℝ) : Finset (Fin N → α) :=
  Finset.univ.filter fun x => |sampleMeanLogProbBits p N x - entropyBits p| < ε

private def badShell [DecidableEq α] (p : ProbDist α) (N : ℕ) (ε : ℝ) : Finset (Fin N → α) :=
  Finset.univ.filter fun x => ε ≤ |sampleMeanLogProbBits p N x - entropyBits p|

private lemma iidDist_eq_zero_of_off_support {N : ℕ} (p : ProbDist α) (x : Fin N → α)
    (hx : ∃ i, p (x i) = 0) : (iidDist p N) x = 0 := by
  rw [iidDist_apply]
  obtain ⟨i, hi⟩ := hx
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

private lemma exists_zero_of_not_fullSupport {N : ℕ} (p : ProbDist α) (x : Fin N → α)
    (hx : ¬ ∀ i, 0 < p (x i)) : ∃ i, p (x i) = 0 := by
  obtain ⟨i, hi⟩ := not_forall.mp hx
  exact ⟨i, le_antisymm (not_lt.mp hi) (prob_nonneg p (x i))⟩

private lemma sum_typicalSet_eq_sum_goodShell [DecidableEq α]
    (p : ProbDist α) (N : ℕ) (ε : ℝ) :
    ∑ x ∈ typicalSet p N ε, (iidDist p N) x = ∑ x ∈ goodShell p N ε, (iidDist p N) x := by
  classical
  let s := goodShell p N ε
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := s)
    (p := fun x : Fin N → α => ∀ i, 0 < p (x i)) (f := fun x => (iidDist p N) x)
  have hzero : ∑ x ∈ s.filter (fun x => ¬ ∀ i, 0 < p (x i)), (iidDist p N) x = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    exact iidDist_eq_zero_of_off_support p x <| exists_zero_of_not_fullSupport p x
      (Finset.mem_filter.mp hx).2
  calc
    ∑ x ∈ typicalSet p N ε, (iidDist p N) x
        = ∑ x ∈ s.filter (fun x => ∀ i, 0 < p (x i)), (iidDist p N) x := by
            simp [s, goodShell, typicalSet, sampleMeanLogProbBits, Finset.filter_filter,
              and_comm]
    _ = ∑ x ∈ s, (iidDist p N) x := by
          linarith [hsplit, hzero]
    _ = ∑ x ∈ goodShell p N ε, (iidDist p N) x := by rfl

private lemma sum_goodShell_add_sum_badShell [DecidableEq α]
    (p : ProbDist α) (N : ℕ) (ε : ℝ) :
    (∑ x ∈ goodShell p N ε, (iidDist p N) x) + (∑ x ∈ badShell p N ε, (iidDist p N) x) = 1 := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun x : Fin N → α => |sampleMeanLogProbBits p N x - entropyBits p| < ε)
    (f := fun x => (iidDist p N) x)
  calc
    (∑ x ∈ goodShell p N ε, (iidDist p N) x) + (∑ x ∈ badShell p N ε, (iidDist p N) x)
        = ∑ x : Fin N → α, (iidDist p N) x := by
            simpa [goodShell, badShell, sampleMeanLogProbBits] using hsplit
    _ = 1 := prob_sum_eq_one (iidDist p N)

private lemma iidDist_sum_apply_sample (p : ProbDist α) (N : ℕ) (g : α → ℝ) :
    ∑ x : Fin N → α, (iidDist p N) x * (∑ i, g (x i)) = (N : ℝ) * (∑ a, p a * g a) := by
  let μ : Fin N → Measure α := fun _ => (probDistToPMF p).toMeasure
  calc
    ∑ x : Fin N → α, (iidDist p N) x * (∑ i, g (x i))
        = ∫ x, ∑ i, g (x i) ∂(probDistToPMF (iidDist p N)).toMeasure := by
            symm
            simp [PMF.integral_eq_sum, probDistToPMF_apply_toReal, smul_eq_mul]
    _ = ∫ x, ∑ i, g (x i) ∂Measure.pi μ := by rw [iidDist_toMeasure_eq_pi]
    _ = ∑ i, ∫ x : Fin N → α, g (x i) ∂Measure.pi μ := by
          simpa using (MeasureTheory.integral_finset_sum (μ := Measure.pi μ) (s := Finset.univ)
            (f := fun i x => g (x i)) (fun i _ => Integrable.of_finite))
    _ = ∑ i, ∫ a, g a ∂μ i := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simpa [μ] using MeasureTheory.integral_comp_eval (μ := μ) (i := i) (f := g)
            (Measurable.aestronglyMeasurable (by fun_prop))
    _ = ∑ i : Fin N, ∑ a, p a * g a := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simpa [μ] using probDist_integral_eq_sum p g
    _ = (N : ℝ) * (∑ a, p a * g a) := by simp

private lemma iidDist_sampleMean_eq_entropyBits (p : ProbDist α) (N : ℕ) :
    ∑ x : Fin (N + 1) → α, (iidDist p (N + 1)) x * sampleMeanLogProbBits p (N + 1) x
      = entropyBits p := by
  unfold sampleMeanLogProbBits
  calc
    ∑ x : Fin (N + 1) → α, (iidDist p (N + 1)) x * ((1 / ((N + 1 : ℕ) : ℝ)) * ∑ i, logProbBits p (x i))
        = ∑ x : Fin (N + 1) → α, (1 / ((N + 1 : ℕ) : ℝ)) * ((iidDist p (N + 1)) x * ∑ i, logProbBits p (x i)) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            ring
    _ = (1 / ((N + 1 : ℕ) : ℝ)) * ∑ x : Fin (N + 1) → α, (iidDist p (N + 1)) x * ∑ i, logProbBits p (x i) := by
          rw [Finset.mul_sum]
    _ = (1 / ((N + 1 : ℕ) : ℝ)) * (((N + 1 : ℕ) : ℝ) * entropyBits p) := by
          rw [iidDist_sum_apply_sample p (N + 1) (logProbBits p), sum_mul_logProbBits]
    _ = entropyBits p := by
          have hn_ne : (((N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
          field_simp [hn_ne]

private lemma memLp_logProbBits (p : ProbDist α) :
    MemLp (logProbBits p) 2 ((probDistToPMF p).toMeasure) := by
  refine MemLp.of_bound (Measurable.aestronglyMeasurable (by fun_prop)) (∑ a, |logProbBits p a|) ?_
  exact Filter.Eventually.of_forall fun a => by
    simp only [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun b _ => abs_nonneg (logProbBits p b)) (Finset.mem_univ a)

private lemma iidDist_variance_logProb_bound (p : ProbDist α) (N : ℕ) :
    ∑ x : Fin (N + 1) → α,
      (iidDist p (N + 1)) x * (sampleMeanLogProbBits p (N + 1) x - entropyBits p) ^ 2
        ≤ (∑ a, p a * (logProbBits p a - entropyBits p) ^ 2) / ((N + 1 : ℕ) : ℝ) := by
  let μ : Fin (N + 1) → Measure α := fun _ => (probDistToPMF p).toMeasure
  have hvar_sum :
      Var[∑ i, fun x : Fin (N + 1) → α => logProbBits p (x i); Measure.pi μ]
        = ∑ i : Fin (N + 1), Var[logProbBits p; (probDistToPMF p).toMeasure] := by
    simpa [μ] using ProbabilityTheory.variance_sum_pi (μ := μ) (X := fun _ => logProbBits p)
      (fun _ => memLp_logProbBits p)
  have hsamp_var :
      Var[sampleMeanLogProbBits p (N + 1); (probDistToPMF (iidDist p (N + 1))).toMeasure]
        = Var[logProbBits p; (probDistToPMF p).toMeasure] / ((N + 1 : ℕ) : ℝ) := by
    rw [iidDist_toMeasure_eq_pi]
    unfold sampleMeanLogProbBits
    rw [ProbabilityTheory.variance_const_mul]
    have hn_ne : (((N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hvar_sum' :
        Var[fun x : Fin (N + 1) → α => ∑ i, logProbBits p (x i); Measure.pi μ]
          = ((N + 1 : ℕ) : ℝ) * Var[logProbBits p; (probDistToPMF p).toMeasure] := by
      have hfun : (fun x : Fin (N + 1) → α => ∑ i, logProbBits p (x i))
          = ∑ i, fun x : Fin (N + 1) → α => logProbBits p (x i) := by
            funext x
            simp
      rw [hfun]
      simpa using hvar_sum
    rw [hvar_sum']
    field_simp [hn_ne]
  have hsamp_sq :
      ∑ x : Fin (N + 1) → α,
        (iidDist p (N + 1)) x * (sampleMeanLogProbBits p (N + 1) x - entropyBits p) ^ 2
          = Var[sampleMeanLogProbBits p (N + 1); (probDistToPMF (iidDist p (N + 1))).toMeasure] := by
    rw [ProbabilityTheory.variance_eq_integral]
    · symm
      have hmean :
          ∫ x, sampleMeanLogProbBits p (N + 1) x ∂(probDistToPMF (iidDist p (N + 1))).toMeasure
            = entropyBits p := by
              simpa [PMF.integral_eq_sum, probDistToPMF_apply_toReal, smul_eq_mul] using
                iidDist_sampleMean_eq_entropyBits p N
      rw [hmean]
      simp [PMF.integral_eq_sum, probDistToPMF_apply_toReal, smul_eq_mul]
    · exact Measurable.aemeasurable (by fun_prop)
  have hsingle_var :
      Var[logProbBits p; (probDistToPMF p).toMeasure]
        = ∑ a, p a * (logProbBits p a - entropyBits p) ^ 2 := by
    rw [probDist_variance_eq_sum p (logProbBits p), sum_mul_logProbBits]
  rw [hsamp_sq, hsamp_var, hsingle_var]

/-- Shannon's Theorem 3 in the i.i.d. case: for large block lengths, the
typical set carries arbitrarily close to full mass. -/
theorem aep_iid [DecidableEq α] (p : ProbDist α) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (1 - δ : ℝ) ≤ ∑ x ∈ typicalSet p N ε, (iidDist p N) x := by
  let C : ℝ := ∑ a, p a * (logProbBits p a - entropyBits p) ^ 2
  let N₀ : ℕ := Nat.ceil (C / (δ * ε ^ 2)) + 1
  refine ⟨N₀, ?_⟩
  intro N hN
  have hN_pos : 0 < N := by
    have hN₀_pos : 0 < N₀ := by simp [N₀]
    exact lt_of_lt_of_le hN₀_pos hN
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN_pos)
  have hcheb := chebyshev_finite (p := iidDist p (n + 1)) (f := sampleMeanLogProbBits p (n + 1)) ε hε
  have hcheb' := hcheb
  rw [iidDist_sampleMean_eq_entropyBits p n] at hcheb'
  have hbad :
      ∑ x ∈ badShell p (n + 1) ε, (iidDist p (n + 1)) x
        ≤ (∑ x : Fin (n + 1) → α,
            (iidDist p (n + 1)) x * (sampleMeanLogProbBits p (n + 1) x - entropyBits p) ^ 2) / ε ^ 2 := by
    simpa [badShell, sampleMeanLogProbBits] using hcheb'
  have hbad' :
      ∑ x ∈ badShell p (n + 1) ε, (iidDist p (n + 1)) x
        ≤ C / (((n + 1 : ℕ) : ℝ) * ε ^ 2) := by
    calc
      ∑ x ∈ badShell p (n + 1) ε, (iidDist p (n + 1)) x
          ≤ ((∑ x : Fin (n + 1) → α,
                (iidDist p (n + 1)) x * (sampleMeanLogProbBits p (n + 1) x - entropyBits p) ^ 2) / ε ^ 2) := hbad
      _ ≤ (C / (((n + 1 : ℕ) : ℝ))) / ε ^ 2 := by
            exact div_le_div_of_nonneg_right (iidDist_variance_logProb_bound p n) (sq_nonneg ε)
      _ = C / (((n + 1 : ℕ) : ℝ) * ε ^ 2) := by
            have hn_ne : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
            have hεsq_ne : ε ^ 2 ≠ 0 := by positivity
            field_simp [div_eq_mul_inv, hn_ne, hεsq_ne]
  have hN_real : (N₀ : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast hN
  have hC_nonneg : 0 ≤ C := by
    exact Finset.sum_nonneg fun a _ => mul_nonneg (prob_nonneg p a) (sq_nonneg _)
  have ht_lt : C / (δ * ε ^ 2) < ((n + 1 : ℕ) : ℝ) := by
    calc
      C / (δ * ε ^ 2) ≤ Nat.ceil (C / (δ * ε ^ 2)) := Nat.le_ceil _
      _ < Nat.ceil (C / (δ * ε ^ 2)) + 1 := by exact_mod_cast Nat.lt_succ_self _
      _ = N₀ := by simp [N₀]
      _ ≤ ((n + 1 : ℕ) : ℝ) := hN_real
  have hsmall : C / (((n + 1 : ℕ) : ℝ) * ε ^ 2) ≤ δ := by
    have hden_pos : 0 < δ * ε ^ 2 := by positivity
    have hnum_lt : C < ((n + 1 : ℕ) : ℝ) * (δ * ε ^ 2) := by
      exact (div_lt_iff₀ hden_pos).mp ht_lt
    have hblock_pos : 0 < (((n + 1 : ℕ) : ℝ) * ε ^ 2) := by positivity
    apply (div_le_iff₀ hblock_pos).mpr
    exact le_of_lt <| by
      calc
        C < ((n + 1 : ℕ) : ℝ) * (δ * ε ^ 2) := hnum_lt
        _ = δ * ((((n + 1 : ℕ) : ℝ) * ε ^ 2) : ℝ) := by ring
  have hgood :
      (1 - δ : ℝ) ≤ ∑ x ∈ goodShell p (n + 1) ε, (iidDist p (n + 1)) x := by
    have hbad_leδ : ∑ x ∈ badShell p (n + 1) ε, (iidDist p (n + 1)) x ≤ δ := le_trans hbad' hsmall
    have hsplit := sum_goodShell_add_sum_badShell (p := p) (N := n + 1) (ε := ε)
    linarith
  rw [sum_typicalSet_eq_sum_goodShell (p := p) (N := n + 1) (ε := ε)]
  exact hgood

/-- Typical-set upper cardinality bound in the i.i.d. case. -/
theorem typicalSet_iidDist_card_le
    (p : ProbDist α) (N : ℕ) (ε : ℝ) :
    (typicalSet p N ε).card ≤ (2 : ℝ) ^ ((N : ℝ) * (entropyBits p + ε)) := by
  let T := typicalSet p N ε
  let c : ℝ := (2 : ℝ) ^ (-(N : ℝ) * (entropyBits p + ε))
  have hsum_ge : ∑ x ∈ T, c ≤ ∑ x ∈ T, (iidDist p N) x := by
    apply Finset.sum_le_sum
    intro x hx
    simpa [c] using iidDist_ge_of_mem_typicalSet (p := p) (N := N) (ε := ε) hx
  have hmass_le_one : ∑ x ∈ T, (iidDist p N) x ≤ 1 := by
    calc
      ∑ x ∈ T, (iidDist p N) x ≤ ∑ x, (iidDist p N) x :=
        Finset.sum_le_univ_sum_of_nonneg fun x => prob_nonneg (iidDist p N) x
      _ = 1 := prob_sum_eq_one (iidDist p N)
  have hcard_mul : (T.card : ℝ) * c ≤ 1 := by
    simpa [T, c, nsmul_eq_mul] using (le_trans hsum_ge hmass_le_one)
  have hpow_cancel : c * (2 : ℝ) ^ ((N : ℝ) * (entropyBits p + ε)) = 1 := by
    unfold c
    rw [← Real.rpow_add (by positivity : 0 < (2 : ℝ))]
    ring_nf
    rw [Real.rpow_zero]
  calc
    (T.card : ℝ) = (T.card : ℝ) * 1 := by ring
    _ = (T.card : ℝ) * (c * (2 : ℝ) ^ ((N : ℝ) * (entropyBits p + ε))) := by rw [hpow_cancel]
    _ = ((T.card : ℝ) * c) * (2 : ℝ) ^ ((N : ℝ) * (entropyBits p + ε)) := by ring
    _ ≤ 1 * (2 : ℝ) ^ ((N : ℝ) * (entropyBits p + ε)) := by gcongr
    _ = (2 : ℝ) ^ ((N : ℝ) * (entropyBits p + ε)) := by ring

/-- Typical-set lower cardinality bound in the i.i.d. case. -/
theorem typicalSet_iidDist_card_ge [DecidableEq α]
    (p : ProbDist α) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (1 - δ) * (2 : ℝ) ^ ((N : ℝ) * (entropyBits p - ε)) ≤ (typicalSet p N ε).card := by
  obtain ⟨N₀, hAEP⟩ := aep_iid (p := p) (hε := hε) (hδ := hδ)
  refine ⟨N₀, ?_⟩
  intro N hN
  let T := typicalSet p N ε
  let c : ℝ := (2 : ℝ) ^ (-(N : ℝ) * (entropyBits p - ε))
  have hmass_ge : (1 - δ : ℝ) ≤ ∑ x ∈ T, (iidDist p N) x := hAEP N hN
  have hsum_le : ∑ x ∈ T, (iidDist p N) x ≤ (T.card : ℝ) * c := by
    calc
      ∑ x ∈ T, (iidDist p N) x ≤ ∑ x ∈ T, c := by
        apply Finset.sum_le_sum
        intro x hx
        simpa [c] using iidDist_le_of_mem_typicalSet (p := p) (N := N) (ε := ε) hx
      _ = (T.card : ℝ) * c := by simp [T, c, nsmul_eq_mul]
  have hcard_mul : (1 - δ : ℝ) ≤ (T.card : ℝ) * c := le_trans hmass_ge hsum_le
  have hpow_cancel : c * (2 : ℝ) ^ ((N : ℝ) * (entropyBits p - ε)) = 1 := by
    unfold c
    rw [← Real.rpow_add (by positivity : 0 < (2 : ℝ))]
    ring_nf
    rw [Real.rpow_zero]
  calc
    (1 - δ) * (2 : ℝ) ^ ((N : ℝ) * (entropyBits p - ε))
        ≤ ((T.card : ℝ) * c) * (2 : ℝ) ^ ((N : ℝ) * (entropyBits p - ε)) := by gcongr
    _ = (T.card : ℝ) * (c * (2 : ℝ) ^ ((N : ℝ) * (entropyBits p - ε))) := by ring
    _ = (T.card : ℝ) := by rw [hpow_cancel]; ring

private def IsCoverCard [DecidableEq α]
    (p : ProbDist α) (N : ℕ) (q : ℝ) (n : ℕ) : Prop :=
  ∃ S : Finset (Fin N → α), S.card = n ∧ q ≤ ∑ x ∈ S, (iidDist p N) x

private lemma minCover_exists [DecidableEq α]
    (p : ProbDist α) (N : ℕ) (q : ℝ) (hq₁ : q < 1) :
    ∃ n : ℕ, IsCoverCard p N q n := by
  classical
  refine ⟨Fintype.card (Fin N → α), Finset.univ, rfl, ?_⟩
  calc
    q ≤ 1 := le_of_lt hq₁
    _ = ∑ x : Fin N → α, ∏ i, p (x i) := by simpa [iidDist_apply] using (prob_sum_eq_one (iidDist p N)).symm

/-- Minimum cardinality of a set of length-`N` words carrying `iidDist p N`-mass at least `q`. -/
@[nolint unusedArguments]
def minCover [DecidableEq α]
    (p : ProbDist α) (N : ℕ) (q : ℝ) (hq₀ : 0 < q) (hq₁ : q < 1) : ℕ :=
  by
    classical
    have _ := hq₀
    let P : ℕ → Prop := fun n => IsCoverCard p N q n
    letI : DecidablePred P := Classical.decPred P
    exact Nat.find (minCover_exists p N q hq₁)


private lemma minCover_spec [DecidableEq α]
    (p : ProbDist α) (N : ℕ) (q : ℝ) (hq₀ : 0 < q) (hq₁ : q < 1) :
    ∃ S : Finset (Fin N → α),
      S.card = minCover p N q hq₀ hq₁ ∧ q ≤ ∑ x ∈ S, (iidDist p N) x := by
  classical
  let P : ℕ → Prop := fun n => IsCoverCard p N q n
  letI : DecidablePred P := Classical.decPred P
  rcases Nat.find_spec (minCover_exists p N q hq₁) with ⟨S, hcard, hmass⟩
  exact ⟨S, by simpa [minCover, P] using hcard, hmass⟩

private lemma minCover_le_card_of_mass_ge [DecidableEq α]
    (p : ProbDist α) (N : ℕ) (q : ℝ) (hq₀ : 0 < q) (hq₁ : q < 1)
    (S : Finset (Fin N → α))
    (hS : q ≤ ∑ x ∈ S, (iidDist p N) x) :
    minCover p N q hq₀ hq₁ ≤ S.card := by
  classical
  let P : ℕ → Prop := fun n => IsCoverCard p N q n
  letI : DecidablePred P := Classical.decPred P
  simpa [minCover, P] using Nat.find_min' (minCover_exists p N q hq₁) ⟨S, rfl, hS⟩

private lemma minCover_pos [DecidableEq α]
    (p : ProbDist α) (N : ℕ) (q : ℝ) (hq₀ : 0 < q) (hq₁ : q < 1) :
    0 < minCover p N q hq₀ hq₁ := by
  classical
  rcases minCover_spec p N q hq₀ hq₁ with ⟨S, hcard, hmass⟩
  by_contra hzero
  have hcard_zero : S.card = 0 := by
    simpa [hcard] using Nat.eq_zero_of_not_pos hzero
  have hSempty : S = ∅ := Finset.card_eq_zero.mp hcard_zero
  have : q ≤ 0 := by simpa [hSempty] using hmass
  linarith

private lemma sum_not_typicalSet_le [DecidableEq α]
    (p : ProbDist α) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∑ x ∈ (Finset.univ : Finset (Fin N → α)).filter (fun x => x ∉ typicalSet p N ε), (iidDist p N) x ≤ δ := by
  classical
  obtain ⟨N₀, hAEP⟩ := aep_iid (p := p) (hε := hε) (hδ := hδ)
  refine ⟨N₀, ?_⟩
  intro N hN
  have hmass : (1 - δ : ℝ) ≤ ∑ x ∈ typicalSet p N ε, (iidDist p N) x := hAEP N hN
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset (Fin N → α)))
    (p := fun x => x ∈ typicalSet p N ε)
    (f := fun x => (iidDist p N) x)
  have hsplit' :
      (∑ x ∈ typicalSet p N ε, (iidDist p N) x)
        + (∑ x ∈ (Finset.univ : Finset (Fin N → α)).filter (fun x => x ∉ typicalSet p N ε), (iidDist p N) x)
          = 1 := by
    simpa using hsplit.trans (prob_sum_eq_one (iidDist p N))
  linarith

/-- Shannon's Theorem 4 in the i.i.d. min-cover form. -/
theorem tendsto_logb_minCover_iid [DecidableEq α]
    (p : ProbDist α) {q : ℝ} (hq₀ : 0 < q) (hq₁ : q < 1) :
    Tendsto (fun N : ℕ => Real.logb 2 ((minCover p N q hq₀ hq₁ : ℝ)) / (N : ℝ))
      atTop (𝓝 (entropyBits p)) := by
  classical
  let δ : ℝ := min (q / 2) ((1 - q) / 2)
  have hδ_pos : 0 < δ := by
    unfold δ
    refine lt_min ?_ ?_
    · positivity
    · linarith
  have hδ_lt_q : δ < q := by
    have hδ_le : δ ≤ q / 2 := min_le_left _ _
    linarith
  have hq_le_one_sub_δ : q ≤ 1 - δ := by
    have hδ_le : δ ≤ (1 - q) / 2 := min_le_right _ _
    linarith
  have hq_minus_δ_pos : 0 < q - δ := by
    linarith
  refine Metric.tendsto_atTop.2 ?_
  intro η hη
  let ε : ℝ := η / 2
  have hε : 0 < ε := by
    unfold ε
    positivity
  obtain ⟨N₁, hAEP⟩ := aep_iid (p := p) (hε := hε) (hδ := hδ_pos)
  obtain ⟨N₂, hBad⟩ := sum_not_typicalSet_le (p := p) (hε := hε) (hδ := hδ_pos)
  have htail : Tendsto (fun N : ℕ => Real.logb 2 (q - δ) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.logb 2 (q - δ))
  rcases Metric.tendsto_atTop.1 htail (η / 2) (by positivity) with ⟨N₃, hTailN⟩
  let N₀ : ℕ := max (max N₁ N₂) (max N₃ 1)
  refine ⟨N₀, ?_⟩
  intro N hN
  have hN₁ : N ≥ N₁ := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hN₂ : N ≥ N₂ := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hN₃ : N ≥ N₃ := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  have hN1 : 1 ≤ N := le_trans (Nat.le_max_right N₃ 1) (le_trans (le_max_right _ _) hN)
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN1
  let T := typicalSet p N ε
  have hcoverT : q ≤ ∑ x ∈ T, (iidDist p N) x := by
    have hmass : (1 - δ : ℝ) ≤ ∑ x ∈ T, (iidDist p N) x := hAEP N hN₁
    exact le_trans hq_le_one_sub_δ hmass
  have hmin_le_cardT : minCover p N q hq₀ hq₁ ≤ T.card :=
    minCover_le_card_of_mass_ge p N q hq₀ hq₁ T hcoverT
  have hcardT : (T.card : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) * (entropyBits p + ε)) :=
    typicalSet_iidDist_card_le (p := p) (N := N) (ε := ε)
  have hmin_real : ((minCover p N q hq₀ hq₁ : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) * (entropyBits p + ε)) := by
    exact le_trans (by exact_mod_cast hmin_le_cardT) hcardT
  have hmin_pos_real : 0 < ((minCover p N q hq₀ hq₁ : ℕ) : ℝ) := by
    exact_mod_cast minCover_pos p N q hq₀ hq₁
  have hlog_upper :
      Real.logb 2 ((minCover p N q hq₀ hq₁ : ℕ) : ℝ) ≤ (N : ℝ) * (entropyBits p + ε) := by
    have hpow_pos : 0 < (2 : ℝ) ^ ((N : ℝ) * (entropyBits p + ε)) := by positivity
    have hlog := (Real.logb_le_logb (b := 2) (by norm_num) hmin_pos_real hpow_pos).2 hmin_real
    rw [Real.logb_rpow (b_pos := by norm_num) (b_ne_one := by norm_num)] at hlog
    exact hlog
  have hupper_div :
      Real.logb 2 ((minCover p N q hq₀ hq₁ : ℕ) : ℝ) / (N : ℝ) ≤ entropyBits p + ε := by
    rw [div_le_iff₀ hN_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlog_upper
  rcases minCover_spec p N q hq₀ hq₁ with ⟨S, hScard, hSmass⟩
  have hbadmass :
      ∑ x ∈ (Finset.univ : Finset (Fin N → α)).filter (fun x => x ∉ T), (iidDist p N) x ≤ δ :=
    hBad N hN₂
  have hsplitS := Finset.sum_filter_add_sum_filter_not
    (s := S) (p := fun x => x ∈ T) (f := fun x => (iidDist p N) x)
  have hSbad_le :
      ∑ x ∈ S.filter (fun x => x ∉ T), (iidDist p N) x
        ≤ ∑ x ∈ (Finset.univ : Finset (Fin N → α)).filter (fun x => x ∉ T), (iidDist p N) x := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_univ x, hx.2⟩
    · intro x _ _
      exact prob_nonneg (iidDist p N) x
  have hSgood_mass : q - δ ≤ ∑ x ∈ S.filter (fun x => x ∈ T), (iidDist p N) x := by
    have hSbad_leδ : ∑ x ∈ S.filter (fun x => x ∉ T), (iidDist p N) x ≤ δ := le_trans hSbad_le hbadmass
    have hsplitS' :
        (∑ x ∈ S.filter (fun x => x ∈ T), (iidDist p N) x)
          + (∑ x ∈ S.filter (fun x => x ∉ T), (iidDist p N) x)
            = ∑ x ∈ S, (iidDist p N) x := by
      simpa using hsplitS
    linarith
  let c : ℝ := (2 : ℝ) ^ (-(N : ℝ) * (entropyBits p - ε))
  have hsum_le_card :
      ∑ x ∈ S.filter (fun x => x ∈ T), (iidDist p N) x ≤ ((S.filter (fun x => x ∈ T)).card : ℝ) * c := by
    calc
      ∑ x ∈ S.filter (fun x => x ∈ T), (iidDist p N) x ≤ ∑ x ∈ S.filter (fun x => x ∈ T), c := by
        apply Finset.sum_le_sum
        intro x hx
        have hxT : x ∈ T := (Finset.mem_filter.mp hx).2
        simpa [c, T] using iidDist_le_of_mem_typicalSet (p := p) (N := N) (ε := ε) hxT
      _ = ((S.filter (fun x => x ∈ T)).card : ℝ) * c := by simp [c, nsmul_eq_mul]
  have hcard_lower :
      (q - δ) * (2 : ℝ) ^ ((N : ℝ) * (entropyBits p - ε)) ≤ ((S.filter (fun x => x ∈ T)).card : ℝ) := by
    have hcard_mul : q - δ ≤ ((S.filter (fun x => x ∈ T)).card : ℝ) * c := le_trans hSgood_mass hsum_le_card
    have hpow_cancel : c * (2 : ℝ) ^ ((N : ℝ) * (entropyBits p - ε)) = 1 := by
      unfold c
      rw [← Real.rpow_add (by positivity : 0 < (2 : ℝ))]
      ring_nf
      rw [Real.rpow_zero]
    calc
      (q - δ) * (2 : ℝ) ^ ((N : ℝ) * (entropyBits p - ε))
          ≤ ((((S.filter (fun x => x ∈ T)).card : ℝ) * c) * (2 : ℝ) ^ ((N : ℝ) * (entropyBits p - ε))) := by gcongr
      _ = ((S.filter (fun x => x ∈ T)).card : ℝ) * (c * (2 : ℝ) ^ ((N : ℝ) * (entropyBits p - ε))) := by ring
      _ = ((S.filter (fun x => x ∈ T)).card : ℝ) := by rw [hpow_cancel]; ring
  have hmin_lower_real :
      (q - δ) * (2 : ℝ) ^ ((N : ℝ) * (entropyBits p - ε)) ≤ ((minCover p N q hq₀ hq₁ : ℕ) : ℝ) := by
    calc
      (q - δ) * (2 : ℝ) ^ ((N : ℝ) * (entropyBits p - ε)) ≤ ((S.filter (fun x => x ∈ T)).card : ℝ) := hcard_lower
      _ ≤ (S.card : ℝ) := by
            exact_mod_cast (Finset.card_filter_le (s := S) (p := fun x => x ∈ T))
      _ = ((minCover p N q hq₀ hq₁ : ℕ) : ℝ) := by exact_mod_cast hScard
  have hleft_pos : 0 < (q - δ) * (2 : ℝ) ^ ((N : ℝ) * (entropyBits p - ε)) := by positivity
  have hlog_lower :
      Real.logb 2 (q - δ) + (N : ℝ) * (entropyBits p - ε)
        ≤ Real.logb 2 ((minCover p N q hq₀ hq₁ : ℕ) : ℝ) := by
    have hlog := (Real.logb_le_logb (b := 2) (by norm_num) hleft_pos hmin_pos_real).2 hmin_lower_real
    have hprod :
        Real.logb 2 ((q - δ) * (2 : ℝ) ^ ((N : ℝ) * (entropyBits p - ε)))
          = Real.logb 2 (q - δ) + (N : ℝ) * (entropyBits p - ε) := by
      rw [Real.logb_mul hq_minus_δ_pos.ne' (by positivity : (2 : ℝ) ^ ((N : ℝ) * (entropyBits p - ε)) ≠ 0),
        Real.logb_rpow (b_pos := by norm_num) (b_ne_one := by norm_num)]
    simpa [hprod] using hlog
  have hlower_div :
      entropyBits p - ε + Real.logb 2 (q - δ) / (N : ℝ)
        ≤ Real.logb 2 ((minCover p N q hq₀ hq₁ : ℕ) : ℝ) / (N : ℝ) := by
    rw [le_div_iff₀ hN_pos]
    have hN_ne : (N : ℝ) ≠ 0 := by positivity
    field_simp [hN_ne]
    simpa [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using hlog_lower
  have hconst_small : |Real.logb 2 (q - δ) / (N : ℝ)| < η / 2 := by
    simpa [Real.dist_eq, abs_div, abs_of_nonneg hN_pos.le] using (hTailN N hN₃)
  have hconst_lower : -(η / 2) < Real.logb 2 (q - δ) / (N : ℝ) := (abs_lt.mp hconst_small).1
  have hlow : entropyBits p - η < Real.logb 2 ((minCover p N q hq₀ hq₁ : ℕ) : ℝ) / (N : ℝ) := by
    unfold ε at hlower_div
    linarith [hlower_div, hconst_lower]
  have hupp : Real.logb 2 ((minCover p N q hq₀ hq₁ : ℕ) : ℝ) / (N : ℝ) < entropyBits p + η := by
    unfold ε at hupper_div
    linarith [hupper_div, hη]
  have habs : |Real.logb 2 ((minCover p N q hq₀ hq₁ : ℕ) : ℝ) / (N : ℝ) - entropyBits p| < η := by
    rw [abs_lt]
    constructor <;> linarith
  simpa [Real.dist_eq] using habs

end Discrete

end

end Shannon
