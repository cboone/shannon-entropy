/-
SPDX-FileCopyrightText: 2026 Christopher Boone
SPDX-License-Identifier: Apache-2.0
-/

import Shannon.Entropy.Bits
import Shannon.Entropy.Converse

/-!
# Shannon.Entropy.IID

I.i.d. product distributions, per-symbol log-probability, and the base-2
typical set.

This module packages the finite-type `Fin N → α` product distribution used for
Phase D, together with the entropy additivity and pointwise typical-set bounds
that feed the AEP proof in `AEP.lean`.

## Main definitions

- `iidDist`: i.i.d. product distribution on `Fin N → α`
- `logProbBits`: per-symbol self-information in bits
- `typicalSet`: support-restricted `ε`-shell around `entropyBits p`

## Main results

- `iidDist_entropyNat`, `iidDist_entropyBits`: N-fold entropy additivity
- `sum_mul_logProbBits`: expected self-information equals entropy in bits
- `iidDist_le_of_mem_typicalSet`, `iidDist_ge_of_mem_typicalSet`: pointwise
  bounds for typical sequences

## References

- [Shannon1948]: Claude E. Shannon, *A Mathematical Theory of Communication*,
  *Bell System Technical Journal* 27 (1948), Section 7.
- [CoverThomas2006]: Thomas M. Cover and Joy A. Thomas, *Elements of
  Information Theory*, 2nd ed., Wiley, 2006, Chapter 3.
-/

namespace Shannon

noncomputable section
open Finset Real

/-- I.i.d. product distribution on `Fin N → α`: `iidDist p N x = ∏ i, p (x i)`. -/
def iidDist {α : Type} [Fintype α] (p : ProbDist α) (N : ℕ) : ProbDist (Fin N → α) := by
  classical
  refine ⟨fun x => ∏ i, p (x i), ?_⟩
  constructor
  · intro x
    exact Finset.prod_nonneg fun i _ => prob_nonneg p (x i)
  · calc
      ∑ x : Fin N → α, ∏ i, p (x i)
          = ∑ x ∈ Fintype.piFinset (fun _ : Fin N => (Finset.univ : Finset α)), ∏ i, p (x i) := by
              rw [Fintype.piFinset_univ]
      _ = ∏ i : Fin N, ∑ a ∈ (Finset.univ : Finset α), p a := by
            simpa using (Finset.prod_univ_sum (t := fun _ : Fin N => (Finset.univ : Finset α))
              (f := fun _ a => p a)).symm
      _ = ∏ _i : Fin N, (1 : ℝ) := by simp [prob_sum_eq_one p]
      _ = 1 := by simp

@[simp] lemma iidDist_apply {α : Type} [Fintype α] (p : ProbDist α) (N : ℕ) (x : Fin N → α) :
    (iidDist p N) x = ∏ i, p (x i) := rfl

/-- Relabel the `(N + 1)`-fold i.i.d. distribution as a head symbol together
with an `N`-block suffix. -/
theorem iidDist_succ_relabel {α : Type} [Fintype α] (p : ProbDist α) (N : ℕ) :
    iidDist p (N + 1)
      = relabelProb (Fin.consEquiv fun _ : Fin (N + 1) => α) (prodDist p (iidDist p N)) := by
  ext x
  change ∏ i, p (x i) = p (x 0) * ∏ i : Fin N, p (x i.succ)
  rw [Fin.prod_univ_succ]

/-- N-fold additivity in nats: `entropyNat (iidDist p N) = N * entropyNat p`. -/
theorem iidDist_entropyNat {α : Type} [Fintype α] (p : ProbDist α) (N : ℕ) :
    entropyNat (iidDist p N) = N * entropyNat p := by
  induction N with
  | zero =>
      unfold entropyNat iidDist
      simp
  | succ N ih =>
      rw [iidDist_succ_relabel, entropyNat_relabelInvariant, entropyNat_prodDist, ih]
      rw [Nat.cast_add]
      ring

/-- N-fold additivity in bits: `entropyBits (iidDist p N) = N * entropyBits p`. -/
theorem iidDist_entropyBits {α : Type} [Fintype α] (p : ProbDist α) (N : ℕ) :
    entropyBits (iidDist p N) = N * entropyBits p := by
  rw [entropyBits_eq_entropyNat_div_log_two, entropyBits_eq_entropyNat_div_log_two,
    iidDist_entropyNat, mul_div_assoc]

/-- Per-symbol base-2 log-probability, also called self-information. -/
def logProbBits {α : Type} [Fintype α] (p : ProbDist α) (a : α) : ℝ :=
  -Real.logb 2 (p a)

/-- Expected self-information equals entropy in bits. -/
theorem sum_mul_logProbBits {α : Type} [Fintype α] (p : ProbDist α) :
    ∑ a, p a * logProbBits p a = entropyBits p := by
  unfold logProbBits entropyBits entropyBase
  simp_rw [mul_neg]
  rw [Finset.sum_neg_distrib]

/-- Base-2 typical set: words whose empirical per-symbol log-probability lies
within `ε` of the entropy rate, restricted to the support of `p`. -/
def typicalSet {α : Type} [Fintype α]
    (p : ProbDist α) (N : ℕ) (ε : ℝ) : Finset (Fin N → α) :=
  by
    classical
    exact Finset.univ.filter fun x =>
      (∀ i, 0 < p (x i)) ∧ |(1 / (N : ℝ)) * (∑ i, logProbBits p (x i)) - entropyBits p| < ε

private lemma iidDist_pos_of_pos {α : Type} [Fintype α] {p : ProbDist α} {N : ℕ} {x : Fin N → α}
    (hx : ∀ i, 0 < p (x i)) : 0 < (iidDist p N) x := by
  rw [iidDist_apply]
  exact Finset.prod_pos fun i _ => hx i

private lemma logb_iidDist_apply_eq_sum {α : Type} [Fintype α] {p : ProbDist α} {N : ℕ}
    {x : Fin N → α} (hx : ∀ i, 0 < p (x i)) :
    Real.logb 2 ((iidDist p N) x) = ∑ i, Real.logb 2 (p (x i)) := by
  rw [iidDist_apply, Real.logb, Real.log_prod]
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp [Real.logb]
  · intro i _
    exact (hx i).ne'

private lemma logb_iidDist_apply_eq_neg_sum_logProbBits {α : Type} [Fintype α]
    {p : ProbDist α} {N : ℕ} {x : Fin N → α} (hx : ∀ i, 0 < p (x i)) :
    Real.logb 2 ((iidDist p N) x) = -∑ i, logProbBits p (x i) := by
  rw [logb_iidDist_apply_eq_sum hx]
  unfold logProbBits
  simp

/-- Per-element upper bound on typical i.i.d. mass. -/
theorem iidDist_le_of_mem_typicalSet
    {α : Type} [Fintype α]
    {p : ProbDist α} {N : ℕ} {ε : ℝ}
    {x : Fin N → α} (hx : x ∈ typicalSet p N ε) :
    (iidDist p N) x ≤ (2 : ℝ) ^ (-(N : ℝ) * (entropyBits p - ε)) := by
  rcases N with _ | N
  · simp [iidDist]
  · rcases Finset.mem_filter.mp hx with ⟨_, hshell⟩
    have hm_pos : 0 < (iidDist p (N + 1)) x := iidDist_pos_of_pos hshell.1
    let s : ℝ := ∑ i, logProbBits p (x i)
    have hshell' : |(1 / ((N + 1 : ℕ) : ℝ)) * s - entropyBits p| < ε := by
      simpa [s] using hshell.2
    have havg_lower : entropyBits p - ε < (1 / ((N + 1 : ℕ) : ℝ)) * s := by
      have := abs_lt.mp hshell'
      linarith
    have hs_lower : (((N + 1 : ℕ) : ℝ) * (entropyBits p - ε)) < s := by
      have hn_pos : 0 < (((N + 1 : ℕ) : ℝ)) := by positivity
      have hn_ne : (((N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hs_lower' := mul_lt_mul_of_pos_left havg_lower hn_pos
      have hmul_inv : (((N + 1 : ℕ) : ℝ) * (1 / (((N + 1 : ℕ) : ℝ)))) = 1 := by
        field_simp [hn_ne]
      calc
        (((N + 1 : ℕ) : ℝ) * (entropyBits p - ε))
            < ((((N + 1 : ℕ) : ℝ) * (1 / (((N + 1 : ℕ) : ℝ)))) * s) := by
                simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hs_lower'
        _ = s := by rw [hmul_inv, one_mul]
    have hlog : Real.logb 2 ((iidDist p (N + 1)) x) ≤ -((((N + 1 : ℕ) : ℝ) * (entropyBits p - ε))) := by
      rw [logb_iidDist_apply_eq_neg_sum_logProbBits hshell.1]
      linarith
    have hbound : (iidDist p (N + 1)) x ≤ (2 : ℝ) ^ (-((((N + 1 : ℕ) : ℝ) * (entropyBits p - ε)))) :=
      (Real.logb_le_iff_le_rpow (b := 2) (x := (iidDist p (N + 1)) x)
        (y := -((((N + 1 : ℕ) : ℝ) * (entropyBits p - ε)))) (by norm_num) hm_pos).mp hlog
    convert hbound using 1
    ring_nf

/-- Per-element lower bound on typical i.i.d. mass. -/
theorem iidDist_ge_of_mem_typicalSet
    {α : Type} [Fintype α]
    {p : ProbDist α} {N : ℕ} {ε : ℝ}
    {x : Fin N → α} (hx : x ∈ typicalSet p N ε) :
    ((2 : ℝ) ^ (-(N : ℝ) * (entropyBits p + ε))) ≤ (iidDist p N) x := by
  rcases N with _ | N
  · simp [iidDist]
  · rcases Finset.mem_filter.mp hx with ⟨_, hshell⟩
    have hm_pos : 0 < (iidDist p (N + 1)) x := iidDist_pos_of_pos hshell.1
    let s : ℝ := ∑ i, logProbBits p (x i)
    have hshell' : |(1 / ((N + 1 : ℕ) : ℝ)) * s - entropyBits p| < ε := by
      simpa [s] using hshell.2
    have havg_upper : (1 / ((N + 1 : ℕ) : ℝ)) * s < entropyBits p + ε := by
      have := abs_lt.mp hshell'
      linarith
    have hs_upper : s < (((N + 1 : ℕ) : ℝ) * (entropyBits p + ε)) := by
      have hn_pos : 0 < (((N + 1 : ℕ) : ℝ)) := by positivity
      have hn_ne : (((N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hs_upper' := mul_lt_mul_of_pos_left havg_upper hn_pos
      have hmul_inv : (((N + 1 : ℕ) : ℝ) * (1 / (((N + 1 : ℕ) : ℝ)))) = 1 := by
        field_simp [hn_ne]
      calc
        s = ((((N + 1 : ℕ) : ℝ) * (1 / (((N + 1 : ℕ) : ℝ)))) * s) := by rw [hmul_inv, one_mul]
        _ < (((N + 1 : ℕ) : ℝ) * (entropyBits p + ε)) := by
              simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hs_upper'
    have hlog : -((((N + 1 : ℕ) : ℝ) * (entropyBits p + ε))) ≤ Real.logb 2 ((iidDist p (N + 1)) x) := by
      rw [logb_iidDist_apply_eq_neg_sum_logProbBits hshell.1]
      linarith
    have hbound : (2 : ℝ) ^ (-((((N + 1 : ℕ) : ℝ) * (entropyBits p + ε)))) ≤ (iidDist p (N + 1)) x :=
      (Real.le_logb_iff_rpow_le (b := 2)
        (x := -((((N + 1 : ℕ) : ℝ) * (entropyBits p + ε))))
        (y := (iidDist p (N + 1)) x) (by norm_num) hm_pos).mp hlog
    convert hbound using 1
    ring_nf


end

end Shannon
