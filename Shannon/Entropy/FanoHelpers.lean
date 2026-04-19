import Shannon.Entropy.MutualInfo
import Shannon.Entropy.Converse

/-!
# Shannon.Entropy.FanoHelpers

Helper constructions for Fano's inequality.

This module provides deterministic point distributions, conditional row
distributions `X | Y = y`, and a row-wise decomposition of
`condEntropy (swapJoint p)`.
-/
namespace Shannon

noncomputable section
open Finset Real

/-- Deterministic point distribution on a finite type. -/
def pointDist {α : Type} [Fintype α] (a0 : α) : ProbDist α := by
  classical
  refine ⟨fun a => if a = a0 then 1 else 0, ?_⟩
  constructor
  · intro a
    by_cases h : a = a0 <;> simp [h]
  · rw [Finset.sum_ite_eq']
    simp

@[simp] theorem pointDist_apply_self {α : Type} [Fintype α] (a0 : α) :
    pointDist a0 a0 = 1 := by
  classical
  simp [pointDist]

@[simp] theorem pointDist_apply_ne {α : Type} [Fintype α] {a0 a : α} (h : a ≠ a0) :
    pointDist a0 a = 0 := by
  classical
  simp [pointDist, h]

theorem entropyNat_pointDist {α : Type} [Fintype α] (a0 : α) :
    entropyNat (pointDist a0) = 0 := by
  simpa [IsDeterministic, pointDist] using (entropyNat_eq_zero_iff (pointDist a0)).2 ⟨a0, by simp⟩

theorem prob_eq_zero_of_marginalSnd_eq_zero {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist (α × β)) (y : β) (hy : marginalSnd p y = 0) (x : α) :
    p (x, y) = 0 := by
  have hswap : marginalFst (swapJoint p) y = 0 := by
    simpa [marginalFst_swapJoint] using hy
  simpa [swapJoint] using prob_eq_zero_of_marginalFst_eq_zero (swapJoint p) y hswap x

/-- Conditional distribution of the first coordinate given a fixed value of the second coordinate.

If the second marginal vanishes, a harmless default point distribution is used; the row weight is then zero, so downstream weighted formulas are unaffected. -/
def condDistFstGivenSnd {α β : Type} [Fintype α] [Fintype β] [Nonempty α]
    (p : ProbDist (α × β)) (y : β) : ProbDist α := by
  classical
  by_cases hy : marginalSnd p y = 0
  · exact pointDist (Classical.choice ‹Nonempty α›)
  · have hy' : marginalSnd p y ≠ 0 := hy
    refine ⟨fun x => p (x, y) / marginalSnd p y, ?_⟩
    constructor
    · intro x
      exact div_nonneg (prob_nonneg p (x, y)) (le_of_lt (lt_of_le_of_ne (prob_nonneg (marginalSnd p) y) (Ne.symm hy')))
    · calc
        ∑ x, p (x, y) / marginalSnd p y = (∑ x, p (x, y)) / marginalSnd p y := by rw [Finset.sum_div]
        _ = 1 := by rw [show (∑ x, p (x, y)) = marginalSnd p y by rfl, div_self hy']

theorem marginalSnd_mul_condDistFstGivenSnd {α β : Type} [Fintype α] [Fintype β] [Nonempty α]
    (p : ProbDist (α × β)) (y : β) (x : α) :
    marginalSnd p y * condDistFstGivenSnd p y x = p (x, y) := by
  classical
  by_cases hy : marginalSnd p y = 0
  · rw [hy, zero_mul]
    exact (prob_eq_zero_of_marginalSnd_eq_zero p y hy x).symm
  · simp [condDistFstGivenSnd, hy, mul_div_cancel₀ _ hy]

private def sigmaProdEquiv (β α : Type) : Sigma (fun _ : β => α) ≃ β × α where
  toFun z := (z.1, z.2)
  invFun yz := ⟨yz.1, yz.2⟩
  left_inv z := by cases z; rfl
  right_inv yz := by cases yz; rfl

private theorem relabel_compose_condDistFstGivenSnd_eq_swapJoint
    {α β : Type} [Fintype α] [Fintype β] [Nonempty α]
    (p : ProbDist (α × β)) :
    relabelProb (sigmaProdEquiv β α)
      (composeProb (marginalSnd p) (fun y => condDistFstGivenSnd p y))
      = swapJoint p := by
  ext yx
  rcases yx with ⟨y, x⟩
  change marginalSnd p y * condDistFstGivenSnd p y x = p (x, y)
  rw [marginalSnd_mul_condDistFstGivenSnd]

theorem condEntropy_swapJoint_eq_sum_marginalSnd_entropyNat_condDistFstGivenSnd
    {α β : Type} [Fintype α] [Fintype β] [Nonempty α]
    (p : ProbDist (α × β)) :
    condEntropy (swapJoint p) = ∑ y, marginalSnd p y * entropyNat (condDistFstGivenSnd p y) := by
  let composed := composeProb (marginalSnd p) (fun y => condDistFstGivenSnd p y)
  have hgroup := entropyNat_grouping (p := marginalSnd p) (q := fun y => condDistFstGivenSnd p y)
  have hrel : entropyNat (swapJoint p) = entropyNat (marginalSnd p) + ∑ y, marginalSnd p y * entropyNat (condDistFstGivenSnd p y) := by
    have hcomp : entropyNat composed = entropyNat (marginalSnd p) + ∑ y, marginalSnd p y * entropyNat (condDistFstGivenSnd p y) := hgroup
    have hswap : entropyNat (swapJoint p) = entropyNat composed := by
      rw [← entropyNat_relabelInvariant (sigmaProdEquiv β α) composed]
      simp [composed, relabel_compose_condDistFstGivenSnd_eq_swapJoint]
    exact hswap.trans hcomp
  have hchain := chain_rule (swapJoint p)
  rw [marginalFst_swapJoint, entropyNat_swapJoint] at hchain
  have hrel' : entropyNat p = entropyNat (marginalSnd p) + ∑ y, marginalSnd p y * entropyNat (condDistFstGivenSnd p y) := by
    simpa [entropyNat_swapJoint] using hrel
  linarith [hrel', hchain]

theorem entropyNat_bool_eq_binEntropy (p : ProbDist Bool) :
    entropyNat p = Real.binEntropy (p true) := by
  have hsum : p true + p false = 1 := by
    simpa [Fintype.sum_bool] using prob_sum_eq_one p
  have hfalse : p false = 1 - p true := by
    linarith
  rw [entropyNat_eq_sum_negMulLog, Fintype.sum_bool, hfalse]
  simpa [add_comm] using (Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub (p true)).symm

/-- Auxiliary family for splitting off a distinguished point. -/
def pointComplementFib {α : Type} (a0 : α) : Bool → Type
  | true => {x // x ≠ a0}
  | false => PUnit

/-- Relabel `Sigma (pointComplementFib a0)` back to `α`. -/
noncomputable def pointComplementEquiv {α : Type} [DecidableEq α] (a0 : α) :
    Sigma (pointComplementFib a0) ≃ α := by
  classical
  refine
    { toFun := fun
        | ⟨true, x⟩ => x.1
        | ⟨false, _⟩ => a0
      invFun := fun x => if h : x = a0 then ⟨false, PUnit.unit⟩ else ⟨true, ⟨x, h⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    cases z with
    | mk b z =>
        cases b with
        | false => cases z; simp
        | true =>
            rcases z with ⟨x, hx⟩
            simp [hx]
  · intro x
    by_cases h : x = a0
    · simp [h]
    · simp [h]

instance pointComplementFibFintype {α : Type} [Fintype α] [DecidableEq α] (a0 : α) (b : Bool) :
    Fintype (pointComplementFib a0 b) := by
  cases b
  · change Fintype PUnit
    infer_instance
  · change Fintype {x : α // x ≠ a0}
    infer_instance

theorem sum_subtype_ne_eq_one_sub {α : Type} [Fintype α] [DecidableEq α]
    (r : ProbDist α) (a0 : α) :
    ∑ x : {x // x ≠ a0}, r x.1 = 1 - r a0 := by
  have hsplit : ∑ x, r x = r a0 + ∑ x : {x // x ≠ a0}, r x.1 := by
    simpa using (Fintype.sum_eq_add_sum_subtype_ne (f := fun x : α => r x) a0)
  rw [prob_sum_eq_one r] at hsplit
  linarith

/-- Bernoulli law that records whether an outcome differs from a distinguished point. -/
def splitAtPoint {α : Type} [Fintype α] (r : ProbDist α) (a0 : α) : ProbDist Bool := by
  refine ⟨fun b => if b then 1 - r a0 else r a0, ?_⟩
  constructor
  · intro b
    cases b
    · simpa using prob_nonneg r a0
    · simp
      linarith [prob_le_one r a0]
  · simp

@[simp] theorem splitAtPoint_false {α : Type} [Fintype α] (r : ProbDist α) (a0 : α) :
    splitAtPoint r a0 false = r a0 := by
  simp [splitAtPoint]

@[simp] theorem splitAtPoint_true {α : Type} [Fintype α] (r : ProbDist α) (a0 : α) :
    splitAtPoint r a0 true = 1 - r a0 := by
  simp [splitAtPoint]

/-- Conditional distributions for the point/complement split at `a0`. -/
def splitAtPointCond {α : Type} [Fintype α] [DecidableEq α] (r : ProbDist α) (a0 : α)
    [Nonempty {x // x ≠ a0}] :
    (b : Bool) → ProbDist (pointComplementFib a0 b)
  | false => pointDist PUnit.unit
  | true => by
      classical
      by_cases he : 1 - r a0 = 0
      · exact pointDist (Classical.choice ‹Nonempty {x // x ≠ a0}›)
      · refine ⟨fun x => r x.1 / (1 - r a0), ?_⟩
        constructor
        · intro x
          exact div_nonneg (prob_nonneg r x.1) (by linarith [prob_le_one r a0])
        · change ∑ x : {x // x ≠ a0}, r x.1 / (1 - r a0) = 1
          calc
            ∑ x : {x // x ≠ a0}, r x.1 / (1 - r a0) = (∑ x : {x // x ≠ a0}, r x.1) / (1 - r a0) := by
                  rw [Finset.sum_div]
            _ = 1 := by simp [sum_subtype_ne_eq_one_sub, he]

theorem splitAtPointCond_true_mass {α : Type} [Fintype α] [DecidableEq α]
    (r : ProbDist α) (a0 : α) [Nonempty {x // x ≠ a0}] (x : {x // x ≠ a0}) :
    splitAtPoint r a0 true * splitAtPointCond r a0 true x = r x.1 := by
  classical
  by_cases he : 1 - r a0 = 0
  · rw [splitAtPoint_true, he, zero_mul]
    have hsum_zero : ∑ x : {x // x ≠ a0}, r x.1 = 0 := by simp [sum_subtype_ne_eq_one_sub, he]
    symm
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => prob_nonneg r y.1)).mp hsum_zero x (Finset.mem_univ x)
  · rw [splitAtPoint_true]
    have hx : splitAtPointCond r a0 true x = r x.1 / (1 - r a0) := by
      simp [splitAtPointCond, he]
    rw [hx]
    field_simp [he]

private theorem relabel_compose_splitAtPoint_eq_self {α : Type} [Fintype α] [DecidableEq α]
    (r : ProbDist α) (a0 : α) [Nonempty {x // x ≠ a0}] :
    relabelProb (pointComplementEquiv a0)
      (composeProb (splitAtPoint r a0) (splitAtPointCond r a0))
      = r := by
  ext x
  by_cases h : x = a0
  · subst x
    unfold relabelProb
    simp [pointComplementEquiv, composeProb, splitAtPointCond, splitAtPoint]
  · unfold relabelProb
    simp [pointComplementEquiv, composeProb, splitAtPointCond, splitAtPoint, h]
    exact splitAtPointCond_true_mass r a0 ⟨x, h⟩

theorem entropyNat_le_qaryEntropy_at_distinguished_of_nonempty_compl
    {α : Type} [Fintype α] [DecidableEq α] (r : ProbDist α) (a0 : α)
    [Nonempty {x // x ≠ a0}] :
    entropyNat r ≤ Real.qaryEntropy (Fintype.card α) (1 - r a0) := by
  let composed := composeProb (splitAtPoint r a0) (splitAtPointCond r a0)
  have hgroup := entropyNat_grouping (p := splitAtPoint r a0) (q := splitAtPointCond r a0)
  have hrel : entropyNat r = entropyNat (splitAtPoint r a0) + ∑ b, splitAtPoint r a0 b * entropyNat (splitAtPointCond r a0 b) := by
    have hcomp : entropyNat composed = entropyNat (splitAtPoint r a0) + ∑ b, splitAtPoint r a0 b * entropyNat (splitAtPointCond r a0 b) := hgroup
    have hself : entropyNat r = entropyNat composed := by
      rw [← entropyNat_relabelInvariant (pointComplementEquiv a0) composed]
      simp [composed, relabel_compose_splitAtPoint_eq_self]
    exact hself.trans hcomp
  have hbool : entropyNat (splitAtPoint r a0) = Real.binEntropy (1 - r a0) := by
    rw [entropyNat_bool_eq_binEntropy, splitAtPoint_true]
  have hfalse : entropyNat (splitAtPointCond r a0 false) = 0 := by
    simp [splitAtPointCond, entropyNat_pointDist]
  haveI : Nonempty (pointComplementFib a0 true) := ‹Nonempty {x // x ≠ a0}›
  have htrue : entropyNat (splitAtPointCond r a0 true) ≤ Real.log (Fintype.card {x // x ≠ a0}) :=
    entropyNat_le_log_card (splitAtPointCond r a0 true)
  have he_nonneg : 0 ≤ 1 - r a0 := by
    linarith [prob_le_one r a0]
  have hmul : (1 - r a0) * entropyNat (splitAtPointCond r a0 true)
      ≤ (1 - r a0) * Real.log (Fintype.card {x // x ≠ a0}) :=
    mul_le_mul_of_nonneg_left htrue he_nonneg
  have hmain : entropyNat r ≤ Real.binEntropy (1 - r a0) + (1 - r a0) * Real.log (Fintype.card {x // x ≠ a0}) := by
    rw [Fintype.sum_bool, splitAtPoint_true, splitAtPoint_false, hfalse] at hrel
    rw [hbool] at hrel
    linarith
  have hcard_ge : 1 ≤ Fintype.card α := Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨a0⟩)
  have hcast : ((Fintype.card α - 1 : ℕ) : ℝ) = (Fintype.card α : ℝ) - 1 := by
    rw [Nat.cast_sub hcard_ge]
    norm_num
  have hcardsub : Fintype.card {x // x ≠ a0} = Fintype.card α - 1 := Set.card_ne_eq a0
  have hlog : Real.log (Fintype.card {x // x ≠ a0}) = Real.log ((Fintype.card α : ℝ) - 1) := by
    rw [hcardsub, hcast]
  calc
    entropyNat r ≤ Real.binEntropy (1 - r a0) + (1 - r a0) * Real.log (Fintype.card {x // x ≠ a0}) := hmain
    _ = Real.qaryEntropy (Fintype.card α) (1 - r a0) := by
          rw [hlog, Real.qaryEntropy]
          simp [Real.binEntropy_one_sub, add_comm, mul_comm]

theorem entropyNat_le_qaryEntropy_at_distinguished
    {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    (r : ProbDist α) (a0 : α) :
    entropyNat r ≤ Real.qaryEntropy (Fintype.card α) (1 - r a0) := by
  classical
  by_cases hcomp : Nonempty {x // x ≠ a0}
  · letI := hcomp
    exact entropyNat_le_qaryEntropy_at_distinguished_of_nonempty_compl r a0
  · have hall : ∀ x : α, x = a0 := by
      intro x
      by_cases hx : x = a0
      · exact hx
      · exact False.elim (hcomp ⟨⟨x, hx⟩⟩)
    letI : Subsingleton α := ⟨fun x y => by rw [hall x, hall y]⟩
    letI : Inhabited α := ⟨a0⟩
    have hpa0 : r a0 = 1 := by
      have hsum : ∑ x, r x = r a0 := by
        simpa using (Fintype.sum_subsingleton (fun x : α => r x) a0)
      rw [prob_sum_eq_one r] at hsum
      exact hsum.symm
    have hzero : entropyNat r = 0 := (entropyNat_eq_zero_iff r).2 ⟨a0, hpa0⟩
    have he0 : 1 - r a0 = 0 := by linarith
    rw [hzero, he0, Real.qaryEntropy_zero]

end

end Shannon
