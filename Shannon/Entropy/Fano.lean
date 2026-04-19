import Shannon.Entropy.FanoHelpers
import Shannon.Entropy.BinaryEntropy

/-!
# Shannon.Entropy.Fano

Fano's inequality for finite-alphabet conditional entropy.

The proof uses the row-wise decomposition of `condEntropy (swapJoint p)` from
`FanoHelpers`, a one-row `q`-ary entropy bound at a distinguished decoder
output, and Jensen's inequality for Mathlib's concave `Real.qaryEntropy`.
-/
namespace Shannon

noncomputable section
open Finset Real

/-- Error probability of an estimator `f : β → α` against a joint law on `(X, Y)`. -/
def errorProb {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    (p : ProbDist (α × β)) (f : β → α) : ℝ :=
  ∑ ab ∈ Finset.univ.filter (fun ab => f ab.2 ≠ ab.1), p ab

theorem errorProb_nonneg {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    (p : ProbDist (α × β)) (f : β → α) :
    0 ≤ errorProb p f := by
  unfold errorProb
  exact Finset.sum_nonneg fun ab _ => prob_nonneg p ab

theorem errorProb_eq_one_sub_sum_correct {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    (p : ProbDist (α × β)) (f : β → α) :
    errorProb p f = 1 - ∑ y, p (f y, y) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (α × β)))
    (p := fun ab : α × β => f ab.2 ≠ ab.1) (f := fun ab => p ab)
  have hcorrect :
      ∑ ab ∈ Finset.univ.filter (fun ab : α × β => ¬f ab.2 ≠ ab.1), p ab = ∑ y, p (f y, y) := by
    simp_rw [not_ne_iff]
    rw [Finset.sum_filter, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl ?_
    intro y _
    have hfun :
        (fun x : α => if f y = x then p (x, y) else 0)
          = (fun x : α => if x = f y then p (x, y) else 0) := by
            funext x
            by_cases h : x = f y <;> simp [h, eq_comm]
    simpa [hfun] using (Fintype.sum_ite_eq' (i := f y) (f := fun x : α => p (x, y)))
  have hsplit' := hsplit
  simp_rw [not_ne_iff] at hsplit'
  have hcorrect' : ∑ ab with f ab.2 = ab.1, p ab = ∑ y, p (f y, y) := by
    simpa [not_ne_iff] using hcorrect
  rw [hcorrect'] at hsplit'
  have hsum : errorProb p f + ∑ y, p (f y, y) = 1 := by
    simpa [errorProb, prob_sum_eq_one p] using hsplit'
  linarith

theorem errorProb_le_one {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    (p : ProbDist (α × β)) (f : β → α) :
    errorProb p f ≤ 1 := by
  rw [errorProb_eq_one_sub_sum_correct]
  have hnonneg : 0 ≤ ∑ y, p (f y, y) := Finset.sum_nonneg fun y _ => prob_nonneg p (f y, y)
  linarith

/-- Row-wise decoder error after conditioning on `Y = y`. -/
def rowErrorProb {α β : Type} [Fintype α] [Fintype β] [Nonempty α]
    (p : ProbDist (α × β)) (f : β → α) (y : β) : ℝ :=
  1 - condDistFstGivenSnd p y (f y)

theorem rowErrorProb_nonneg {α β : Type} [Fintype α] [Fintype β] [Nonempty α]
    (p : ProbDist (α × β)) (f : β → α) (y : β) :
    0 ≤ rowErrorProb p f y := by
  unfold rowErrorProb
  linarith [prob_le_one (condDistFstGivenSnd p y) (f y)]

theorem rowErrorProb_le_one {α β : Type} [Fintype α] [Fintype β] [Nonempty α]
    (p : ProbDist (α × β)) (f : β → α) (y : β) :
    rowErrorProb p f y ≤ 1 := by
  unfold rowErrorProb
  linarith [prob_nonneg (condDistFstGivenSnd p y) (f y)]

theorem errorProb_eq_sum_marginalSnd_mul_rowError {α β : Type}
    [Fintype α] [Fintype β] [Nonempty α] [DecidableEq α]
    (p : ProbDist (α × β)) (f : β → α) :
    errorProb p f = ∑ y, marginalSnd p y * rowErrorProb p f y := by
  rw [errorProb_eq_one_sub_sum_correct]
  unfold rowErrorProb
  symm
  calc
    ∑ y, marginalSnd p y * (1 - condDistFstGivenSnd p y (f y))
        = ∑ y, marginalSnd p y - ∑ y, marginalSnd p y * condDistFstGivenSnd p y (f y) := by
            simp_rw [mul_sub, mul_one]
            rw [Finset.sum_sub_distrib]
    _ = 1 - ∑ y, p (f y, y) := by
          congr 1
          · exact prob_sum_eq_one (marginalSnd p)
          · refine Finset.sum_congr rfl ?_
            intro y _
            rw [marginalSnd_mul_condDistFstGivenSnd p y (f y)]

theorem condEntropy_swapJoint_le_qaryEntropy_errorProb
    {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [DecidableEq α]
    (p : ProbDist (α × β)) (f : β → α) :
    condEntropy (swapJoint p) ≤ Real.qaryEntropy (Fintype.card α) (errorProb p f) := by
  rw [condEntropy_swapJoint_eq_sum_marginalSnd_entropyNat_condDistFstGivenSnd]
  have hrows :
      ∑ y, marginalSnd p y * entropyNat (condDistFstGivenSnd p y)
        ≤ ∑ y, marginalSnd p y * Real.qaryEntropy (Fintype.card α) (rowErrorProb p f y) := by
    refine Finset.sum_le_sum ?_
    intro y _
    have hrow := entropyNat_le_qaryEntropy_at_distinguished (condDistFstGivenSnd p y) (f y)
    exact mul_le_mul_of_nonneg_left hrow (prob_nonneg (marginalSnd p) y)
  have hJensen :
      ∑ y, marginalSnd p y * Real.qaryEntropy (Fintype.card α) (rowErrorProb p f y)
        ≤ Real.qaryEntropy (Fintype.card α) (∑ y, marginalSnd p y * rowErrorProb p f y) := by
    exact Real.strictConcaveOn_qaryEntropy.concaveOn.le_map_sum
      (t := Finset.univ)
      (w := fun y => marginalSnd p y)
      (p := fun y => rowErrorProb p f y)
      (fun y _ => prob_nonneg (marginalSnd p) y)
      (prob_sum_eq_one (marginalSnd p))
      (fun y _ => by
        constructor
        · exact rowErrorProb_nonneg p f y
        · exact rowErrorProb_le_one p f y)
  calc
    ∑ y, marginalSnd p y * entropyNat (condDistFstGivenSnd p y)
        ≤ ∑ y, marginalSnd p y * Real.qaryEntropy (Fintype.card α) (rowErrorProb p f y) := hrows
    _ ≤ Real.qaryEntropy (Fintype.card α) (∑ y, marginalSnd p y * rowErrorProb p f y) := hJensen
    _ = Real.qaryEntropy (Fintype.card α) (errorProb p f) := by
          rw [errorProb_eq_sum_marginalSnd_mul_rowError]

/-- **Fano's inequality** (base 2): the conditional entropy of `X` given `Y` is controlled by the decoder error probability. -/
theorem fanoInequality
    {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [DecidableEq α]
    (p : ProbDist (α × β)) (f : β → α) :
    let Pe := errorProb p f
    condEntropyBits (swapJoint p) ≤
      binEntropyBits Pe + Pe * Real.logb 2 ((Fintype.card α - 1 : ℕ) : ℝ) := by
  let Pe := errorProb p f
  have hnat : condEntropy (swapJoint p) ≤ Real.qaryEntropy (Fintype.card α) Pe :=
    condEntropy_swapJoint_le_qaryEntropy_errorProb p f
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard_ge : 1 ≤ Fintype.card α := Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ‹Nonempty α›)
  have hcast : ((Fintype.card α - 1 : ℕ) : ℝ) = (Fintype.card α : ℝ) - 1 := by
    rw [Nat.cast_sub hcard_ge]
    norm_num
  have hcastInt : ((((Fintype.card α : ℤ) - 1 : ℤ) : ℝ)) = ((Fintype.card α - 1 : ℕ) : ℝ) := by
    norm_num [Nat.cast_sub hcard_ge]
  have hdiv : condEntropy (swapJoint p) / Real.log 2 ≤ Real.qaryEntropy (Fintype.card α) Pe / Real.log 2 :=
    (div_le_div_iff_of_pos_right hlog2_pos).2 hnat
  have hterm : Pe * Real.log ((((Fintype.card α : ℤ) - 1 : ℤ) : ℝ)) / Real.log 2
      = Pe * Real.logb 2 ((Fintype.card α - 1 : ℕ) : ℝ) := by
    rw [hcastInt, mul_div_assoc, Real.logb]
  have hqary : Real.qaryEntropy (Fintype.card α) Pe / Real.log 2
      = binEntropyBits Pe + Pe * Real.logb 2 ((Fintype.card α - 1 : ℕ) : ℝ) := by
    unfold binEntropyBits
    rw [Real.qaryEntropy, add_div, hterm]
    ring_nf
  simpa [condEntropyBits, Pe] using hdiv.trans_eq hqary

end

end Shannon
