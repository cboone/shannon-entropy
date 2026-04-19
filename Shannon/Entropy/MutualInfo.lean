import Shannon.Entropy.Properties
import Shannon.Entropy.RelativeEntropy
import Shannon.Entropy.Converse

/-!
# Shannon.Entropy.MutualInfo

Finite-alphabet mutual information and its basic identities.

This module relocates the `mutualInfo` definition out of `Joint.lean`, proves
the standard Section 6 identities, adds base-2 wrappers for mutual and
conditional entropy, and provides the kernel pushforward construction used by
the information-form data processing inequality.

## Main definitions

- `mutualInfo`: mutual information in nats
- `mutualInfoBits`: mutual information in bits
- `condEntropyBits`: conditional entropy in bits
- `swapJoint`: swap the coordinates of a joint distribution
- `diagonalDist`: diagonal joint used to express `I(X;X) = H(X)`
- `kernelPushforward`: push a joint forward along a finite Markov kernel

## Main results

- `mutualInfo_nonneg`, `mutualInfo_eq_zero_iff_independent`, `mutualInfo_symm`
- `mutualInfo_eq_entropyFst_sub_condEntropy_swap`, `mutualInfo_eq_entropySnd_sub_condEntropy`
- `mutualInfo_self`, `mutualInfo_le_entropyFst`, `mutualInfo_le_entropySnd`
- Base-2 counterparts for the main identities and bounds
-/
namespace Shannon

noncomputable section
open Finset Real

/-- Mutual information `I(X;Y) = H(X) + H(Y) - H(X,Y)`. -/
def mutualInfo {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist (α × β)) : ℝ :=
  entropyNat (marginalFst p) + entropyNat (marginalSnd p) - entropyNat p

/-- Swap the coordinates of a joint distribution. Implemented via `relabelProb Equiv.prodComm`. -/
def swapJoint {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist (α × β)) : ProbDist (β × α) :=
  relabelProb (Equiv.prodComm α β) p

/-- Diagonal distribution: `(diagonalDist p)(a, a') = if a = a' then p a else 0`. Used to state `mutualInfo_self`. -/
def diagonalDist {α : Type} [Fintype α] [DecidableEq α]
    (p : ProbDist α) : ProbDist (α × α) := by
  refine ⟨fun ab => if ab.1 = ab.2 then p ab.1 else 0, ?_⟩
  constructor
  · intro ab
    by_cases h : ab.1 = ab.2
    · simp [h, prob_nonneg p _]
    · simp [h]
  · calc
      ∑ ab : α × α, (if ab.1 = ab.2 then p ab.1 else 0)
          = ∑ a, ∑ b, (if a = b then p a else 0) := Fintype.sum_prod_type _
      _ = ∑ a, p a := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [Finset.sum_ite_eq]
            simp
      _ = 1 := prob_sum_eq_one p

private theorem marginalSnd_pos_of_prob_pos {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist (α × β)) (a : α) (b : β) (h : 0 < p (a, b)) :
    0 < marginalSnd p b :=
  lt_of_lt_of_le h
    (Finset.single_le_sum (fun a' _ => prob_nonneg p (a', b)) (Finset.mem_univ a))

theorem marginalFst_swapJoint {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist (α × β)) :
    marginalFst (swapJoint p) = marginalSnd p := by
  ext b
  rfl

theorem marginalSnd_swapJoint {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist (α × β)) :
    marginalSnd (swapJoint p) = marginalFst p := by
  ext a
  rfl

theorem entropyNat_swapJoint {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist (α × β)) :
    entropyNat (swapJoint p) = entropyNat p :=
  entropyNat_relabelInvariant (Equiv.prodComm α β) p

theorem marginalFst_diagonalDist {α : Type} [Fintype α] [DecidableEq α]
    (p : ProbDist α) :
    marginalFst (diagonalDist p) = p := by
  ext a
  rw [show (marginalFst (diagonalDist p)) a = ∑ b, (if a = b then p a else 0) by rfl]
  rw [Finset.sum_ite_eq]
  simp

theorem marginalSnd_diagonalDist {α : Type} [Fintype α] [DecidableEq α]
    (p : ProbDist α) :
    marginalSnd (diagonalDist p) = p := by
  ext b
  rw [show (marginalSnd (diagonalDist p)) b = ∑ a, (if a = b then p a else 0) by rfl]
  rw [Finset.sum_ite_eq']
  simp

theorem entropyNat_diagonalDist {α : Type} [Fintype α] [DecidableEq α]
    (p : ProbDist α) :
    entropyNat (diagonalDist p) = entropyNat p := by
  unfold entropyNat diagonalDist
  simp only
  rw [Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro a _
  have hterm : ∀ b, (if a = b then p a else 0) * Real.log (if a = b then p a else 0)
      = if a = b then p a * Real.log (p a) else 0 := by
    intro b
    split_ifs <;> simp [*]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq]
  simp

/-- **Mutual information is nonnegative**: `0 ≤ I(X; Y)`. -/
theorem mutualInfo_nonneg
    {α β : Type} [Fintype α] [Fintype β] (p : ProbDist (α × β)) :
    0 ≤ mutualInfo p := by
  unfold mutualInfo
  linarith [entropyNat_joint_le_add p]

/-- **Mutual information equals KL to the product of marginals**:
    `I(X;Y) = D(p ‖ marginalFst p × marginalSnd p)`. -/
theorem mutualInfo_eq_relEntropy_prodMarginals
    {α β : Type} [Fintype α] [Fintype β] (p : ProbDist (α × β)) :
    mutualInfo p = relEntropy p (prodDist (marginalFst p) (marginalSnd p)) := by
  let q := prodDist (marginalFst p) (marginalSnd p)
  have hqval : ∀ ab : α × β, q ab = marginalFst p ab.1 * marginalSnd p ab.2 := fun _ => rfl
  have hterm : ∀ ab : α × β,
      p ab * Real.log (p ab / q ab) =
      p ab * Real.log (p ab) - p ab * Real.log (marginalFst p ab.1) - p ab * Real.log (marginalSnd p ab.2) := by
    intro ab
    by_cases hp : p ab = 0
    · simp [hp]
    · have hpa : 0 < p ab := lt_of_le_of_ne (prob_nonneg p ab) (Ne.symm hp)
      have hm1 : 0 < marginalFst p ab.1 := marginalFst_pos_of_prob_pos p ab.1 ab.2 hpa
      have hm2 : 0 < marginalSnd p ab.2 := marginalSnd_pos_of_prob_pos p ab.1 ab.2 hpa
      rw [hqval, Real.log_div (ne_of_gt hpa) (ne_of_gt (mul_pos hm1 hm2)), Real.log_mul (ne_of_gt hm1) (ne_of_gt hm2)]
      ring
  have hm1sum : ∑ ab : α × β, p ab * Real.log (marginalFst p ab.1) =
      ∑ a, marginalFst p a * Real.log (marginalFst p a) := by
    calc
      ∑ ab : α × β, p ab * Real.log (marginalFst p ab.1)
          = ∑ a, ∑ b, p (a, b) * Real.log (marginalFst p a) := Fintype.sum_prod_type _
      _ = ∑ a, (∑ b, p (a, b)) * Real.log (marginalFst p a) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [Finset.sum_mul]
      _ = ∑ a, marginalFst p a * Real.log (marginalFst p a) := rfl
  have hm2sum : ∑ ab : α × β, p ab * Real.log (marginalSnd p ab.2) =
      ∑ b, marginalSnd p b * Real.log (marginalSnd p b) := by
    calc
      ∑ ab : α × β, p ab * Real.log (marginalSnd p ab.2)
          = ∑ b, ∑ a, p (a, b) * Real.log (marginalSnd p b) := Fintype.sum_prod_type_right _
      _ = ∑ b, (∑ a, p (a, b)) * Real.log (marginalSnd p b) := by
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [Finset.sum_mul]
      _ = ∑ b, marginalSnd p b * Real.log (marginalSnd p b) := rfl
  have hrel : relEntropy p q = -entropyNat p + entropyNat (marginalFst p) + entropyNat (marginalSnd p) := by
    unfold relEntropy entropyNat
    simp_rw [hterm, sub_eq_add_neg]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_neg_distrib,
      hm1sum, hm2sum]
    ring
  calc
    mutualInfo p = -entropyNat p + entropyNat (marginalFst p) + entropyNat (marginalSnd p) := by
      unfold mutualInfo
      ring
    _ = relEntropy p q := by symm; exact hrel
    _ = relEntropy p (prodDist (marginalFst p) (marginalSnd p)) := rfl

/-- **Mutual information is zero iff X and Y are independent**. -/
theorem mutualInfo_eq_zero_iff_independent
    {α β : Type} [Fintype α] [Fintype β] (p : ProbDist (α × β)) :
    mutualInfo p = 0 ↔ IsIndependent p := by
  rw [mutualInfo_eq_relEntropy_prodMarginals]
  constructor
  · intro h
    have hsupp : Supports (prodDist (marginalFst p) (marginalSnd p)) p := by
      intro ab hab
      exact mul_pos (marginalFst_pos_of_prob_pos p ab.1 ab.2 hab)
        (marginalSnd_pos_of_prob_pos p ab.1 ab.2 hab)
    intro a b
    exact (relEntropy_eq_zero_iff p _ hsupp).mp h (a, b)
  · intro hind
    have hprod : prodDist (marginalFst p) (marginalSnd p) = p := by
      ext ab
      exact (hind ab.1 ab.2).symm
    rw [hprod]
    exact relEntropy_self p

/-- **Symmetry**: `I(X;Y) = I(Y;X)`. -/
theorem mutualInfo_symm
    {α β : Type} [Fintype α] [Fintype β] (p : ProbDist (α × β)) :
    mutualInfo p = mutualInfo (swapJoint p) := by
  unfold mutualInfo
  rw [marginalFst_swapJoint, marginalSnd_swapJoint, entropyNat_swapJoint]
  ring

/-- **Chain-rule identity**: `I(X;Y) = H(X) - H(X|Y)`. Here `H(X|Y) = condEntropy (swapJoint p)`. -/
theorem mutualInfo_eq_entropyFst_sub_condEntropy_swap
    {α β : Type} [Fintype α] [Fintype β] (p : ProbDist (α × β)) :
    mutualInfo p = entropyNat (marginalFst p) - condEntropy (swapJoint p) := by
  have hchain := chain_rule (swapJoint p)
  rw [marginalFst_swapJoint, entropyNat_swapJoint] at hchain
  unfold mutualInfo
  linarith

/-- **Chain-rule identity, dual**: `I(X;Y) = H(Y) - H(Y|X)`. -/
theorem mutualInfo_eq_entropySnd_sub_condEntropy
    {α β : Type} [Fintype α] [Fintype β] (p : ProbDist (α × β)) :
    mutualInfo p = entropyNat (marginalSnd p) - condEntropy p := by
  have hchain := chain_rule p
  unfold mutualInfo
  linarith

/-- **Self mutual information**: `I(X;X) = H(X)`. -/
theorem mutualInfo_self
    {α : Type} [Fintype α] [DecidableEq α] (p : ProbDist α) :
    mutualInfo (diagonalDist p) = entropyNat p := by
  unfold mutualInfo
  rw [marginalFst_diagonalDist, marginalSnd_diagonalDist, entropyNat_diagonalDist]
  ring

/-- **MI bounded by marginal entropy (first)**: `I(X;Y) ≤ H(X)`. -/
theorem mutualInfo_le_entropyFst
    {α β : Type} [Fintype α] [Fintype β] (p : ProbDist (α × β)) :
    mutualInfo p ≤ entropyNat (marginalFst p) := by
  rw [mutualInfo_eq_entropyFst_sub_condEntropy_swap]
  linarith [condEntropy_nonneg (swapJoint p)]

/-- **MI bounded by marginal entropy (second)**: `I(X;Y) ≤ H(Y)`. -/
theorem mutualInfo_le_entropySnd
    {α β : Type} [Fintype α] [Fintype β] (p : ProbDist (α × β)) :
    mutualInfo p ≤ entropyNat (marginalSnd p) := by
  rw [mutualInfo_eq_entropySnd_sub_condEntropy]
  linarith [condEntropy_nonneg p]

/-- Base-2 mutual information (bits). -/
def mutualInfoBits {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist (α × β)) : ℝ :=
  mutualInfo p / Real.log 2

/-- Base-2 conditional entropy (bits). -/
def condEntropyBits {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist (α × β)) : ℝ :=
  condEntropy p / Real.log 2

theorem mutualInfoBits_nonneg
    {α β : Type} [Fintype α] [Fintype β] (p : ProbDist (α × β)) :
    0 ≤ mutualInfoBits p := by
  unfold mutualInfoBits
  exact div_nonneg (mutualInfo_nonneg p) (Real.log_nonneg (by norm_num))

theorem mutualInfoBits_symm
    {α β : Type} [Fintype α] [Fintype β] (p : ProbDist (α × β)) :
    mutualInfoBits p = mutualInfoBits (swapJoint p) := by
  unfold mutualInfoBits
  rw [mutualInfo_symm]

theorem mutualInfoBits_eq_entropyBitsFst_sub_condEntropyBits_swap
    {α β : Type} [Fintype α] [Fintype β] (p : ProbDist (α × β)) :
    mutualInfoBits p = entropyBits (marginalFst p) - condEntropyBits (swapJoint p) := by
  unfold mutualInfoBits condEntropyBits
  rw [mutualInfo_eq_entropyFst_sub_condEntropy_swap, entropyBits_eq_entropyNat_div_log_two, sub_div]

theorem mutualInfoBits_eq_entropyBitsSnd_sub_condEntropyBits
    {α β : Type} [Fintype α] [Fintype β] (p : ProbDist (α × β)) :
    mutualInfoBits p = entropyBits (marginalSnd p) - condEntropyBits p := by
  unfold mutualInfoBits condEntropyBits
  rw [mutualInfo_eq_entropySnd_sub_condEntropy, entropyBits_eq_entropyNat_div_log_two, sub_div]

theorem mutualInfoBits_self
    {α : Type} [Fintype α] [DecidableEq α] (p : ProbDist α) :
    mutualInfoBits (diagonalDist p) = entropyBits p := by
  unfold mutualInfoBits
  rw [mutualInfo_self, entropyBits_eq_entropyNat_div_log_two]

theorem mutualInfoBits_le_entropyBitsFst
    {α β : Type} [Fintype α] [Fintype β] (p : ProbDist (α × β)) :
    mutualInfoBits p ≤ entropyBits (marginalFst p) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold mutualInfoBits
  rw [entropyBits_eq_entropyNat_div_log_two]
  exact (div_le_div_iff_of_pos_right hlog2_pos).2 (mutualInfo_le_entropyFst p)

theorem mutualInfoBits_le_entropyBitsSnd
    {α β : Type} [Fintype α] [Fintype β] (p : ProbDist (α × β)) :
    mutualInfoBits p ≤ entropyBits (marginalSnd p) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold mutualInfoBits
  rw [entropyBits_eq_entropyNat_div_log_two]
  exact (div_le_div_iff_of_pos_right hlog2_pos).2 (mutualInfo_le_entropySnd p)

/-- **Push-forward of a joint via a kernel**: given a joint `p : ProbDist (α × β)` modeling `(X, Y)` and a kernel `W : β → ProbDist γ` modeling the conditional distribution of `Z` given `Y`, form the induced joint `(X, Z)`. -/
def kernelPushforward
    {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (p : ProbDist (α × β)) (W : β → ProbDist γ) :
    ProbDist (α × γ) := by
  refine ⟨fun ac => ∑ b, p (ac.1, b) * W b ac.2, ?_⟩
  constructor
  · intro ac
    exact Finset.sum_nonneg fun b _ => mul_nonneg (prob_nonneg p (ac.1, b)) (prob_nonneg (W b) ac.2)
  · calc
      ∑ ac : α × γ, ∑ b, p (ac.1, b) * W b ac.2
          = ∑ a, ∑ c, ∑ b, p (a, b) * W b c := Fintype.sum_prod_type _
      _ = ∑ a, ∑ b, p (a, b) * ∑ c, W b c := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [← Finset.mul_sum]
      _ = ∑ a, ∑ b, p (a, b) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [prob_sum_eq_one (W b), mul_one]
      _ = ∑ ab : α × β, p ab := (Fintype.sum_prod_type _).symm
      _ = 1 := prob_sum_eq_one p

theorem marginalFst_kernelPushforward
    {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (p : ProbDist (α × β)) (W : β → ProbDist γ) :
    marginalFst (kernelPushforward p W) = marginalFst p := by
  ext a
  calc
    (marginalFst (kernelPushforward p W)) a
        = ∑ c, ∑ b, p (a, b) * W b c := rfl
    _ = ∑ b, ∑ c, p (a, b) * W b c := by rw [Finset.sum_comm]
    _ = ∑ b, p (a, b) * ∑ c, W b c := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [← Finset.mul_sum]
    _ = ∑ b, p (a, b) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [prob_sum_eq_one (W b), mul_one]
    _ = marginalFst p a := rfl

theorem marginalSnd_kernelPushforward
    {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (p : ProbDist (α × β)) (W : β → ProbDist γ) (c : γ) :
    marginalSnd (kernelPushforward p W) c = ∑ b, marginalSnd p b * W b c := by
  calc
    (marginalSnd (kernelPushforward p W)) c
        = ∑ a, ∑ b, p (a, b) * W b c := rfl
    _ = ∑ b, ∑ a, p (a, b) * W b c := by rw [Finset.sum_comm]
    _ = ∑ b, (∑ a, p (a, b)) * W b c := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Finset.sum_mul]
    _ = ∑ b, marginalSnd p b * W b c := rfl

set_option maxHeartbeats 800000

/-- **Data processing inequality (information form)**: for a Markov chain `X → Y → Z`, `I(X; Z) ≤ I(X; Y)`. -/
theorem mutualInfo_kernelPushforward_le
    {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (p : ProbDist (α × β)) (W : β → ProbDist γ) :
    mutualInfo (kernelPushforward p W) ≤ mutualInfo p := by
  let q := kernelPushforward p W
  rw [mutualInfo_eq_relEntropy_prodMarginals, mutualInfo_eq_relEntropy_prodMarginals]
  have hfiber : ∀ ac : α × γ,
      q ac * Real.log (q ac / prodDist (marginalFst q) (marginalSnd q) ac) ≤
        ∑ b, p (ac.1, b) * W b ac.2 * Real.log
          ((p (ac.1, b) * W b ac.2) / (marginalFst p ac.1 * marginalSnd p b * W b ac.2)) := by
    rintro ⟨a, c⟩
    have hls := log_sum_inequality
      (fun b => p (a, b) * W b c)
      (fun b => marginalFst p a * marginalSnd p b * W b c)
      (fun b => mul_nonneg (prob_nonneg p (a, b)) (prob_nonneg (W b) c))
      (fun b => mul_nonneg
        (mul_nonneg (prob_nonneg (marginalFst p) a) (prob_nonneg (marginalSnd p) b))
        (prob_nonneg (W b) c))
      (fun b hab => by
        have hpab : 0 < p (a, b) := by
          exact pos_of_mul_pos_right (by simpa [mul_comm] using hab) (prob_nonneg (W b) c)
        have hWbc : 0 < W b c := by
          exact pos_of_mul_pos_left (by simpa [mul_comm] using hab) (prob_nonneg p (a, b))
        exact mul_pos
          (mul_pos (marginalFst_pos_of_prob_pos p a b hpab) (marginalSnd_pos_of_prob_pos p a b hpab))
          hWbc)
    simpa [q, prodDist, marginalFst_kernelPushforward, marginalSnd_kernelPushforward, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm] using hls
  have hsum :
      ∑ ac : α × γ, q ac * Real.log (q ac / prodDist (marginalFst q) (marginalSnd q) ac) ≤
        ∑ ac : α × γ, ∑ b, p (ac.1, b) * W b ac.2 * Real.log
          ((p (ac.1, b) * W b ac.2) / (marginalFst p ac.1 * marginalSnd p b * W b ac.2)) := by
    exact Finset.sum_le_sum fun ac _ => hfiber ac
  have hterm_kernel : ∀ a b c,
      p (a, b) * W b c * Real.log ((p (a, b) * W b c) / (marginalFst p a * marginalSnd p b * W b c)) =
        W b c * (p (a, b) * Real.log (p (a, b) / (marginalFst p a * marginalSnd p b))) := by
    intro a b c
    by_cases hW : W b c = 0
    · simp [hW]
    · by_cases hpab0 : p (a, b) = 0
      · simp [hpab0]
      · have hpab : 0 < p (a, b) := lt_of_le_of_ne (prob_nonneg p (a, b)) (Ne.symm hpab0)
        have hm1 : 0 < marginalFst p a := marginalFst_pos_of_prob_pos p a b hpab
        have hm2 : 0 < marginalSnd p b := marginalSnd_pos_of_prob_pos p a b hpab
        have hratio :
            (p (a, b) * W b c) / (marginalFst p a * marginalSnd p b * W b c)
              = p (a, b) / (marginalFst p a * marginalSnd p b) := by
          field_simp [hW, hm1.ne', hm2.ne']
        rw [hratio]
        ring
  have hrhs :
      ∑ ac : α × γ, ∑ b, p (ac.1, b) * W b ac.2 * Real.log
        ((p (ac.1, b) * W b ac.2) / (marginalFst p ac.1 * marginalSnd p b * W b ac.2))
        = relEntropy p (prodDist (marginalFst p) (marginalSnd p)) := by
    rw [Fintype.sum_prod_type]
    simp_rw [hterm_kernel]
    calc
      ∑ a, ∑ c, ∑ b, W b c * (p (a, b) * Real.log (p (a, b) / (marginalFst p a * marginalSnd p b)))
          = ∑ a, ∑ b, ∑ c, W b c * (p (a, b) * Real.log (p (a, b) / (marginalFst p a * marginalSnd p b))) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              rw [Finset.sum_comm]
      _ = ∑ a, ∑ b, p (a, b) * Real.log (p (a, b) / (marginalFst p a * marginalSnd p b)) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [← Finset.sum_mul, prob_sum_eq_one (W b), one_mul]
      _ = ∑ ab : α × β, p ab * Real.log (p ab / prodDist (marginalFst p) (marginalSnd p) ab) := by
            exact (Fintype.sum_prod_type (fun ab : α × β => p ab * Real.log (p ab / prodDist (marginalFst p) (marginalSnd p) ab))).symm
      _ = relEntropy p (prodDist (marginalFst p) (marginalSnd p)) := by
            rw [relEntropy]
    
  simpa [q] using
    (calc
      relEntropy q (prodDist (marginalFst q) (marginalSnd q))
          = ∑ ac : α × γ, q ac * Real.log (q ac / prodDist (marginalFst q) (marginalSnd q) ac) := rfl
      _ ≤ ∑ ac : α × γ, ∑ b, p (ac.1, b) * W b ac.2 * Real.log
            ((p (ac.1, b) * W b ac.2) / (marginalFst p ac.1 * marginalSnd p b * W b ac.2)) := hsum
      _ = relEntropy p (prodDist (marginalFst p) (marginalSnd p)) := hrhs)

theorem mutualInfoBits_kernelPushforward_le
    {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (p : ProbDist (α × β)) (W : β → ProbDist γ) :
    mutualInfoBits (kernelPushforward p W) ≤ mutualInfoBits p := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold mutualInfoBits
  exact (div_le_div_iff_of_pos_right hlog2_pos).2 (mutualInfo_kernelPushforward_le p W)

set_option maxHeartbeats 200000

end

end Shannon
