# 2026-04-21 Phase D: i.i.d. AEP and typical sets (Theorems 3 and 4, i.i.d. case)

Date: 2026-04-21
Status: Draft. Targets Phase D of `docs/plans/todo/2026-04-14-shannon-proofs-roadmap.md`. Branch `formalize/phase-d-iid-aep-and-typical-sets` off `main` at the current `7c29b4a` tip (post Phase C merge). Current branch state is still planning-only: no `Shannon/Entropy/IID.lean`, `Shannon/Entropy/AEP.lean`, or matching tests and book chapter have landed yet.

## Context

Phase C shipped on 2026-04-19 (`formalize/c-information-theoretic-primitives`, merged as `b83abbf`). The library now exposes the information-theoretic primitives layer: `relEntropy`, `mutualInfo`, base-2 counterparts (`mutualInfoBits`, `condEntropyBits`, `relEntropyBits`, `binEntropyBits`), the log-sum inequality, the information-form DPI, and Fano's inequality. The companion Verso book gained three chapters (`MutualInformation`, `RelativeEntropy`, `FanoInequality`). The natural-log workhorse `entropyNat` and the base-2 public surface (`entropyBits`, `entropyBits_prodDist`, `entropyBits_uniformPNat`, `entropyBits_le_logb_two_card`) are all in place.

Phase D specializes Shannon's Theorems 3 and 4 to the i.i.d. setting, stated in base 2 to match Shannon's `2^{NH}` phrasing directly. Concretely:

- Build the i.i.d. product distribution `iidDist p N : ProbDist (Fin N → α)` with per-symbol masses multiplied.
- Prove N-fold additivity `entropyBits (iidDist p N) = N * entropyBits p` as the arithmetic anchor for every AEP statement.
- Define the base-2 typical set as the support-restricted `ε`-shell around `entropyBits p` of the empirical per-symbol log-probability.
- Prove per-element bounds `2 ^ (-N * (entropyBits p + ε)) ≤ iidDist p N x ≤ 2 ^ (-N * (entropyBits p - ε))` on typical `x`.
- Prove Theorem 3 (i.i.d. AEP): for any `ε, δ > 0`, there is `N₀` such that the typical set has mass at least `1 − δ` for all `N ≥ N₀`.
- Prove Theorem 4 (i.i.d. typical set size): `(1 − δ) · 2 ^ (N · (entropyBits p − ε)) ≤ |typicalSet p N ε| ≤ 2 ^ (N · (entropyBits p + ε))` and the `minCover` consequence that the per-symbol log-cardinality of any coverage-`q` subset converges to `entropyBits p`.

Every new theorem is stated in bits. Natural-log variants are internal. Phase E will upgrade the same statements to the transcription-faithful finite-state-source setting (and there mark Theorems 3 and 4 as unqualified complete); Phase D is explicitly the i.i.d. special case and the transcription cross-references reflect that.

Three observations from the current code that shape Phase D:

- `composeProb` (on `Sigma`) and `prodDist` (on `α × β`) already exist in `Core.lean` and `Joint.lean`. The i.i.d. product `Fin N → α` needs a fresh construction: `composeProb` lives on dependent sigma types, not on constant-`Fin`-indexed function spaces, and iterating `prodDist` to `Fin N → α` via `finTwoEquivProd` chains is uglier than a direct `∏ i, p (x i)` definition. Build `iidDist` directly; the simplex proof is one `Finset.prod_univ_sum`-style reshape.
- `entropyBits_prodDist` (Phase C Task 1 landing) supplies the two-factor additivity. N-fold additivity follows by induction on `N`, at each step folding off the leftmost factor via an `Equiv (Fin (N + 1) → α) (α × (Fin N → α))` relabel plus `entropyBits_prodDist`. Relabel invariance in bits is an easy corollary of `entropyNat_relabelInvariant` combined with the natural-log / bits bridge.
- Mathlib does not ship a finite-sum Chebyshev inequality on a custom `ProbDist α` type. The pinned Mathlib's `ProbabilityTheory.meas_ge_le_variance_div_sq` lives in `Mathlib/Probability/Moments/Variance.lean` and is measure-theoretic; wrapping `ProbDist α` as a `Measure` to invoke it is strictly more adapter work than proving Chebyshev directly by a short `Finset.sum_le_sum` argument. Phase D rolls its own finite Chebyshev helper and skips the measure-theory detour. The helper is short (≈20 lines) and lives inside `AEP.lean` unless another phase finds a second consumer.

Single-phase design caveats recorded in the roadmap (honored unchanged in this plan):

- **Chapters under `Book/` must not `import Shannon` or any `Shannon.*` module.** Lake links every transitive C object on the `generate-book` argv, and pulling Mathlib through `Shannon` pushes the macOS command line past `ARG_MAX`. The Phase D book chapter references Lean identifiers by backticks only, with no direct `import Shannon`.
- **`entropyBits` is the primary public surface from Phase C onward.** Every Phase D theorem is stated in bits; nat versions surface only as private or unit-tested corollaries where a proof wants them internally.

## Goal

Deliver six things in one branch:

1. `Shannon/Entropy/IID.lean`: the i.i.d. product distribution `iidDist`, the per-symbol log-probability `logProbBits`, and the N-fold additivity identity `iidDist_entropyBits` (plus a nat companion `iidDist_entropyNat` kept for internal use).
2. The base-2 typical set `typicalSet p N ε : Finset (Fin N → α)` as a support-restricted ε-shell around `entropyBits p`, plus the per-element bounds `iidDist_le_of_mem_typicalSet` and `iidDist_ge_of_mem_typicalSet` stated in `2 ^ …` form directly (no natural-log detour).
3. A finite Chebyshev-style concentration helper on `ProbDist α` in the AEP module (or split into a local `Concentration` section if the helper grows) and the Theorem 3 statement `aep_iid`: for every `ε, δ > 0`, there is `N₀` such that for `N ≥ N₀`, the typical set has `iidDist p N`-mass at least `1 − δ`.
4. Theorem 4 statements `typicalSet_iidDist_card_le` and `typicalSet_iidDist_card_ge` bounding `|typicalSet p N ε|` above and (for `N` large, conditional on `δ`) below by the base-2 expressions the roadmap locks in.
5. The `minCover` functional on interior coverage thresholds `0 < q < 1` and its `Tendsto` consequence: `Tendsto (fun N => Real.logb 2 (minCover p N q hq₀ hq₁) / N) atTop (𝓝 (entropyBits p))`.
6. A new Verso book chapter `Book/IIDAndAEP.lean` walking through the product construction, typical set, and the i.i.d. case of Theorems 3 and 4; transcription cross-references for the i.i.d. row; roadmap sync; facade update; test mirrors; `cspell-words.txt` additions.

Non-goals (reserved for Phase E):

- Finite-state statistical sources `FiniteStateSource`, entropy rate, stationary distributions.
- Per-symbol entropy `Gₙ`, `Fₙ` convergence (Theorems 5 and 6).
- The transducer form of Theorem 7.
- Upgrading Theorems 3 and 4 to a finite-state source. Phase D leaves a forward pointer; the transcription cross-reference entries for Theorems 3 and 4 stay marked as "i.i.d. case" until Phase E lands.

Non-goals (Phase F; permanently out of scope for this roadmap):

- Continuous / differential entropy, channel capacity.

## Tasks

### 1. I.i.d. product distribution and N-fold additivity (`Shannon/Entropy/IID.lean`)

Create `Shannon/Entropy/IID.lean`. Imports: `Shannon.Entropy.Bits` for the base-2 API and `Shannon.Entropy.Converse` for `entropyNat_relabelInvariant` (the latter is not re-exported by `Bits.lean`).

Module skeleton:

```lean
import Shannon.Entropy.Bits
import Shannon.Entropy.Converse

namespace Shannon

noncomputable section
open Finset Real

/-- **I.i.d. product distribution on `Fin N → α`**: `iidDist p N x = ∏ i, p (x i)`. Shannon's
"long sequences of independent draws" construction. -/
def iidDist {α : Type} [Fintype α]
    (p : ProbDist α) (N : ℕ) : ProbDist (Fin N → α) := by
  refine ⟨fun x => ∏ i, p (x i), ?_⟩
  constructor
  · intro x
    exact Finset.prod_nonneg fun i _ => prob_nonneg p (x i)
  · -- simplex: ∑_{x : Fin N → α} ∏_i p (x i) = (∑ a, p a) ^ N = 1
    classical
    calc
      ∑ x : Fin N → α, ∏ i, p (x i)
          = (∑ a, p a) ^ N := ?_
      _ = (1 : ℝ) ^ N := by rw [prob_sum_eq_one p]
      _ = 1 := one_pow N
    -- The reshape uses `Finset.prod_univ_sum` / `Finset.sum_prod_univ` (name varies by Mathlib
    -- revision; grep for `prod_univ_sum` / `sum_pow` during implementation).
    sorry
```

Before writing the proof body, grep the pinned Mathlib for the right-hand reshape:

```bash
rg -n "prod_univ_sum|Finset\\.sum_pow|Fintype\\.sum_pow" \
  .lake/packages/mathlib/Mathlib/Algebra/BigOperators/
```

`Finset.prod_univ_sum` exists and directly realizes `∏ i ∈ s, ∑ j ∈ t i, f i j = ∑ g ∈ Fintype.piFinset t, ∏ i ∈ s, f i (g i)`. Specialized to constant fibers, this yields exactly the shape we need. If the landed form of that lemma changes between now and implementation, the reshape is a three-line calc; it does not rely on a brittle lemma name.

Definitional expansion:

```lean
@[simp] lemma iidDist_apply {α : Type} [Fintype α]
    (p : ProbDist α) (N : ℕ) (x : Fin N → α) :
    (iidDist p N) x = ∏ i, p (x i) := rfl
```

N-fold additivity in nats, then in bits:

```lean
/-- **N-fold additivity in nats**: `entropyNat (iidDist p N) = N * entropyNat p`. Internal;
the public bits form is `iidDist_entropyBits`. -/
theorem iidDist_entropyNat {α : Type} [Fintype α]
    (p : ProbDist α) (N : ℕ) :
    entropyNat (iidDist p N) = N * entropyNat p := by
  induction N with
  | zero =>
    -- `Fin 0 → α` has exactly one element (the empty function); iidDist is a point mass.
    -- entropy of a point mass is 0.
    ...
  | succ N ih =>
    -- relabel `Fin (N + 1) → α` ≃ α × (Fin N → α)` by `Fin.cons` / `Fin.succ`,
    -- use `entropyNat_prodDist` and `ih`, concluding via `entropyNat_relabelInvariant`.
    ...

/-- **N-fold additivity in bits**: `entropyBits (iidDist p N) = N * entropyBits p`. Shannon's
    `H(X^N) = N H(X)` for i.i.d. sources, base 2. -/
theorem iidDist_entropyBits {α : Type} [Fintype α]
    (p : ProbDist α) (N : ℕ) :
    entropyBits (iidDist p N) = N * entropyBits p := by
  rw [entropyBits_eq_entropyNat_div_log_two, entropyBits_eq_entropyNat_div_log_two,
      iidDist_entropyNat, mul_div_assoc]
```

Two internal helpers the induction step uses:

- `iidDist_succ_relabel : iidDist p (N + 1) = relabelProb (finSuccEquivCons α N) (prodDist p (iidDist p N))` (or the appropriate equivalence in Mathlib; `Fin.consEquiv` is the likely name). The equivalence sends `Fin.cons a x` to `(a, x)` and is the one that makes the left factor align with a single draw.
- `entropyBits_relabelInvariant : entropyBits (relabelProb e p) = entropyBits p`. This is not currently in `Bits.lean`; it is a one-line consequence of `entropyNat_relabelInvariant` from `Converse.lean` plus the bits / nat bridge. Add it to `Bits.lean` in a small Task 1a commit so `iidDist_entropyBits` can close without reaching into internals.

Task 1a (one-line helper in `Bits.lean`):

```lean
theorem entropyBits_relabelInvariant
    {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (p : ProbDist α) :
    entropyBits (relabelProb e p) = entropyBits p := by
  simp only [entropyBits_eq_entropyNat_div_log_two]
  rw [entropyNat_relabelInvariant]
```

Ship Task 1a alongside Task 1 in one commit (it is a feeder lemma for the N-fold induction; committing it separately bloats the history with a one-liner).

Also define the per-symbol log-probability used by the typical set (Task 2):

```lean
/-- Per-symbol base-2 log-probability: `logProbBits p a = -Real.logb 2 (p a)` on the support
of `p`, and `0` elsewhere (Lean's `Real.log 0 = 0` convention keeps it total). Used inside
the typical-set definition; the support restriction on the typical set ensures every term
entering an arithmetic identity comes from a strictly positive `p a`. -/
def logProbBits {α : Type} [Fintype α] (p : ProbDist α) (a : α) : ℝ :=
  -Real.logb 2 (p a)
```

A two-line identity the AEP proof will use:

```lean
/-- **Expected log-probability equals entropy (bits)**:
    `∑ a, p a * logProbBits p a = entropyBits p`. -/
theorem sum_mul_logProbBits {α : Type} [Fintype α] (p : ProbDist α) :
    ∑ a, p a * logProbBits p a = entropyBits p := by
  unfold logProbBits entropyBits entropyBase
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro a _
  ring
```

Module docstring follows the Phase B / C template ("## Main definitions", "## Main results", "## References" pointing at Shannon 1948 Section 7 plus Cover and Thomas Chapter 3).

### 2. Typical set and per-element bounds (`Shannon/Entropy/IID.lean`)

Still in `IID.lean` (the typical set is tightly coupled to `iidDist`; splitting it into a separate module does not pay for the extra import hop at this scale).

Definition:

```lean
/-- **Base-2 typical set**: the support-restricted set of sequences whose empirical per-symbol
log-probability is within `ε` of `entropyBits p`:
    `{ x : Fin N → α | (∀ i, 0 < p (x i)) ∧
        |(1/N) * ∑ i, logProbBits p (x i) - entropyBits p| < ε }`.
The support restriction keeps every `logProbBits p (x i)` finite on the set; for `p` with full
support the restriction is vacuous. -/
def typicalSet {α : Type} [Fintype α] [DecidableEq α]
    (p : ProbDist α) (N : ℕ) (ε : ℝ) : Finset (Fin N → α) :=
  Finset.univ.filter fun x =>
    (∀ i, 0 < p (x i)) ∧
      |(1 / (N : ℝ)) * (∑ i, logProbBits p (x i)) - entropyBits p| < ε
```

The `DecidableEq α` instance is needed for the `Finset.filter` to be computable; it also ensures `(∀ i, 0 < p (x i))` has a decidable instance (finite conjunction over `Fin N` of decidable `<` on `ℝ`). Mathlib's `decidableBallFin` already provides that; include `classical` where needed to elaborate.

Per-element bounds (the AEP uses these in nats first, then bits):

```lean
/-- **Per-element upper bound on typical i.i.d. mass**: a typical sequence has
    `iidDist p N x ≤ 2 ^ (-N * (entropyBits p - ε))`. -/
theorem iidDist_le_of_mem_typicalSet
    {α : Type} [Fintype α] [DecidableEq α]
    {p : ProbDist α} {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    {x : Fin N → α} (hx : x ∈ typicalSet p N ε) :
    (iidDist p N) x ≤ (2 : ℝ) ^ (-(N : ℝ) * (entropyBits p - ε)) := by
  ...

/-- **Per-element lower bound on typical i.i.d. mass**: a typical sequence has
    `2 ^ (-N * (entropyBits p + ε)) ≤ iidDist p N x`. -/
theorem iidDist_ge_of_mem_typicalSet
    {α : Type} [Fintype α] [DecidableEq α]
    {p : ProbDist α} {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    {x : Fin N → α} (hx : x ∈ typicalSet p N ε) :
    ((2 : ℝ) ^ (-(N : ℝ) * (entropyBits p + ε))) ≤ (iidDist p N) x := by
  ...
```

Proof strategy for both (they are mirror-image): take the `Real.logb 2` of `iidDist p N x = ∏ i, p (x i)`:

```text
Real.logb 2 (iidDist p N x) = ∑ i, Real.logb 2 (p (x i)) = -∑ i, logProbBits p (x i).
```

The membership condition gives `|(1/N) * ∑ i, logProbBits p (x i) - entropyBits p| < ε`, hence

```text
-(entropyBits p + ε) < -(1/N) * ∑ i, logProbBits p (x i) < -(entropyBits p - ε),
N * -(entropyBits p + ε) < -∑ i, logProbBits p (x i) < N * -(entropyBits p - ε).
```

Exponentiating base 2 (monotone, support-positive ensures `iidDist p N x > 0` so `Real.rpow_logb` applies) yields the bounds directly in `2 ^ …` form.

Key Mathlib lemmas (confirmed in Mathlib 4.29.0):

- `Real.logb_prod`: `Real.logb b (∏ i ∈ s, f i) = ∑ i ∈ s, Real.logb b (f i)` given positivity.
- `Real.rpow_logb`: `b ^ Real.logb b x = x` for `0 < x` and `1 < b`.
- `Real.rpow_natCast`: bridges `(2 : ℝ) ^ (n : ℝ) = (2 : ℝ) ^ (n : ℕ)` when needed.
- `Real.rpow_le_rpow_left_iff`: monotonicity `b ^ x ≤ b ^ y ↔ x ≤ y` for `1 < b`.
- `Real.rpow_add`, `Real.rpow_neg`, `Real.rpow_mul`: arithmetic.

If the `Real.logb` / `Real.rpow` bookkeeping causes friction (the open question flagged in the roadmap), introduce a tiny `Bits` namespace inside `IID.lean` with `log2 x := Real.logb 2 x` and `exp2 x := (2 : ℝ) ^ x`, plus three arithmetic lemmas (`log2_exp2`, `exp2_log2`, `exp2_add`). Keep the wrapper local to this module; do not widen the public surface until Phase E finds a second consumer.

Testing anchor: on `α := Fin 2`, `p := uniformPNat 2`, every sequence is typical for any `ε > 0` (entropy rate is `1` and every sequence has log-prob exactly `-N`). `typicalSet` equals `Finset.univ` and the per-element bounds reduce to `2 ^ (-N) ≤ 2 ^ (-N * (1 - ε))` and `2 ^ (-N * (1 + ε)) ≤ 2 ^ (-N)`. This is a good first unit test.

### 3. Finite Chebyshev and AEP (Theorem 3) in `Shannon/Entropy/AEP.lean`

Create `Shannon/Entropy/AEP.lean`. Imports: `Shannon.Entropy.IID`.

Two layers: a finite concentration helper, then the AEP itself.

#### 3a. Finite Chebyshev on `ProbDist`

Stated in self-contained finite form to avoid the Mathlib measure-theoretic detour:

```lean
/-- **Finite Chebyshev inequality on a distribution**: for a random variable `f : α → ℝ` on a
finite probability space `p : ProbDist α` with mean `μ := ∑ a, p a * f a`, the mass of the
ε-tail is bounded by the variance divided by `ε^2`:
    `∑ a ∈ univ.filter (fun a => ε ≤ |f a - μ|), p a ≤ (∑ a, p a * (f a - μ)^2) / ε^2`. -/
theorem chebyshev_finite
    {α : Type} [Fintype α] [DecidableEq α]
    (p : ProbDist α) (f : α → ℝ) (ε : ℝ) (hε : 0 < ε) :
    (∑ a ∈ Finset.univ.filter (fun a => ε ≤ |f a - (∑ b, p b * f b)|), p a) ≤
      (∑ a, p a * (f a - (∑ b, p b * f b))^2) / ε^2 := by
  ...
```

Proof: on the filtered set, `(f a − μ)^2 ≥ ε^2`, so `p a ≤ p a * (f a − μ)^2 / ε^2`. Sum over the filtered set, bound by the full sum (nonnegativity of `p a * (f a − μ)^2`), divide. This is a direct `Finset.sum_le_sum` argument; the `write-lean-code` skill's "let the type system guide implementation" applies directly. Budget ≈ 25 lines.

Keep this lemma in `AEP.lean` rather than lifting it to a shared module. It has no other current consumer; if Phase E finds one, extract it then (standard YAGNI).

#### 3b. The empirical per-symbol log-probability is the sample mean

Before invoking Chebyshev, show that the `(1/N) * ∑ i, logProbBits p (x i)` expression in `typicalSet` is the sample mean of `Y_i := logProbBits p (X_i)` under `iidDist p N`:

```lean
/-- Sample mean under `iidDist`: for any `g : α → ℝ`,
    `∑ x, iidDist p N x * (∑ i, g (x i)) = N * (∑ a, p a * g a)`.
Specialized at `g = logProbBits p`, this gives
`∑ x, iidDist p N x * ∑ i, logProbBits p (x i) = N * entropyBits p`. -/
private lemma iidDist_sum_apply_sample
    {α : Type} [Fintype α]
    (p : ProbDist α) (N : ℕ) (g : α → ℝ) :
    ∑ x : Fin N → α, (iidDist p N) x * (∑ i, g (x i)) =
      (N : ℝ) * (∑ a, p a * g a) := by
  ...
```

Proof: expand `iidDist p N x = ∏ i, p (x i)`, swap `∑ x` and `∑ i`, factor the product at each `i`, reduce each fiber via `∑ a, p a = 1`. A direct `Finset.prod_univ_sum` / `Finset.sum_comm` calc; ≈ 15 lines.

The per-symbol variance bound is likewise a standard `log^2`-weighted sum:

```lean
/-- Sample-mean variance bound: the empirical average of `logProbBits` under `iidDist p N`
    has variance at most `(∑ a, p a * (logProbBits p a - entropyBits p)^2) / N`.
    The `1 / N` decay is the point: it is what feeds Chebyshev in `aep_iid`. -/
private lemma iidDist_variance_logProb_bound
    {α : Type} [Fintype α]
    (p : ProbDist α) (N : ℕ) :
    ∑ x, (iidDist p N) x *
      ((1 / (N : ℝ)) * (∑ i, logProbBits p (x i)) - entropyBits p)^2
    ≤ (∑ a, p a * (logProbBits p a - entropyBits p)^2) / N := by
  ...
```

This is the scaling law `Var(Y̅_N) = Var(Y) / N` for i.i.d. samples, specialized to `Y = logProbBits p`. The proof uses `iidDist_sum_apply_sample` for the linear-in-`g` case and an independence-style cross-term argument for the quadratic case; budget ≈ 40 lines. If the cross-term bookkeeping is ugly, keep a weakened but still vanishing estimate of the form `≤ C / N` for some explicit constant `C` depending only on `p`. Do not weaken all the way to `≤ C`: Chebyshev would then give only a fixed tail bound and would not prove the AEP.

#### 3c. The AEP statement

```lean
/-- **Shannon's Theorem 3 (i.i.d. AEP, base 2)**: for `0 < ε` and `0 < δ`, there is a length
`N₀` such that for all `N ≥ N₀`, the typical set carries at least `1 − δ` mass:
    `∑ x ∈ typicalSet p N ε, iidDist p N x ≥ 1 − δ`.

The i.i.d. case of Shannon's Theorem 3 (Section 7). Phase E upgrades to finite-state sources. -/
theorem aep_iid
    {α : Type} [Fintype α] [DecidableEq α] (p : ProbDist α)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (1 - δ : ℝ) ≤ ∑ x ∈ typicalSet p N ε, (iidDist p N) x := by
  -- Apply chebyshev_finite with f := fun x => (1/N) * ∑ i, logProbBits p (x i) on `iidDist p N`,
  -- using mean = entropyBits p (from iidDist_sum_apply_sample) and variance ≤ C / N (from
  -- iidDist_variance_logProb_bound). Complement of the typical-set tail has mass ≤ C / (N ε^2),
  -- take N₀ := ⌈C / (ε^2 δ)⌉ + 1.
  ...
```

The one subtlety: the typical-set definition adds the `(∀ i, 0 < p (x i))` support condition; the Chebyshev-based proof above bounds the event `|(1/N) ∑ logProbBits p (x i) − entropyBits p| ≥ ε` without support. Account for this by showing that sequences violating the support condition have `iidDist p N` mass zero:

```lean
private lemma iidDist_eq_zero_of_off_support
    {α : Type} [Fintype α] (p : ProbDist α) (N : ℕ) (x : Fin N → α)
    (hx : ∃ i, p (x i) = 0) :
    (iidDist p N) x = 0 := by
  obtain ⟨i, hi⟩ := hx
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi
```

So the support restriction is vacuous on the support of `iidDist p N`, and the Chebyshev bound transfers cleanly: every `x` with positive mass automatically satisfies `∀ i, 0 < p (x i)`, and the numerical tail condition is the only active filter. Fold this into the `aep_iid` proof as a two-line rewrite; do not expose it on the public API.

Exactly the statement in the roadmap: `∃ N₀, ∀ N ≥ N₀, (1 - δ) ≤ mass of typicalSet`. If the implementation prefers the `≥ 1 - δ` direction of the inequality as written in Shannon, pick whichever reads more naturally with `linarith`; both land the same theorem.

### 4. Typical set cardinality (Theorem 4, i.i.d. case) in `Shannon/Entropy/AEP.lean`

Two bounds, stated directly in `2 ^ …` form:

```lean
/-- **Typical set upper bound (bits)**: `|typicalSet p N ε| ≤ 2 ^ (N * (entropyBits p + ε))`.
Holds for every `N : ℕ` and `0 < ε`; no AEP (large `N`) condition needed. -/
theorem typicalSet_iidDist_card_le
    {α : Type} [Fintype α] [DecidableEq α]
    (p : ProbDist α) (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (typicalSet p N ε).card ≤ (2 : ℝ) ^ ((N : ℝ) * (entropyBits p + ε)) := by
  -- mass(typicalSet) ≤ 1, each element has mass ≥ 2 ^ (-N (H + ε)), so |typicalSet| ≤ 2 ^ (N(H+ε))
  ...

/-- **Typical set lower bound (bits)**: for `0 < ε, δ` and all sufficiently large `N`,
    `(1 - δ) * 2 ^ (N * (entropyBits p - ε)) ≤ |typicalSet p N ε|`. -/
theorem typicalSet_iidDist_card_ge
    {α : Type} [Fintype α] [DecidableEq α]
    (p : ProbDist α) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (1 - δ) * (2 : ℝ) ^ ((N : ℝ) * (entropyBits p - ε))
        ≤ (typicalSet p N ε).card := by
  -- mass(typicalSet) ≥ 1 - δ (by aep_iid), each element has mass ≤ 2 ^ (-N (H - ε)),
  -- so (1 - δ) ≤ |typicalSet| * 2 ^ (-N (H - ε)), rearrange.
  ...
```

Both proofs are short: the upper bound is `∑ x ∈ typicalSet, iidDist p N x ≤ 1` combined with `iidDist_ge_of_mem_typicalSet` (each term `≥ 2 ^ (-N (H + ε))`) giving `|typicalSet| * 2 ^ (-N (H + ε)) ≤ 1`, rearrange. The lower bound is the `aep_iid` tail bound combined with `iidDist_le_of_mem_typicalSet`.

The `Nat` cast on the cardinality is the minor bookkeeping detail: `(typicalSet p N ε).card : ℕ` coerces to `ℝ` for the comparison with `(2 : ℝ) ^ _`. Use `Nat.cast_le` and `exact_mod_cast` where appropriate.

### 5. `minCover` and asymptotic rate in `Shannon/Entropy/AEP.lean`

```lean
/-- **Minimum-cover cardinality**: the size of the smallest subset whose `iidDist p N` mass is
at least `q`, for an interior coverage threshold with `0 < q < 1`. Shannon's "starting from
the most probable, how many sequences to accumulate probability `q`". Implemented via
`Nat.find` on the set of cardinalities achieving the mass. -/
def minCover {α : Type} [Fintype α] [DecidableEq α]
    (p : ProbDist α) (N : ℕ) (q : ℝ) (hq₀ : 0 < q) (hq₁ : q < 1) : ℕ :=
  Nat.find (h := ?_) ...

/-- **Shannon's Theorem 4 (i.i.d. case, minCover form)**:
    `Tendsto (fun N => Real.logb 2 (minCover p N q hq₀ hq₁) / N) atTop (𝓝 (entropyBits p))`
    for `0 < q < 1`. -/
theorem tendsto_logb_minCover_iid
    {α : Type} [Fintype α] [DecidableEq α]
    (p : ProbDist α) {q : ℝ} (hq₀ : 0 < q) (hq₁ : q < 1) :
    Tendsto (fun N : ℕ => Real.logb 2 ((minCover p N q hq₀ hq₁ : ℝ)) / (N : ℝ))
      atTop (𝓝 (entropyBits p)) := by
  -- upper bound: minCover ≤ |typicalSet| (for N large, typical set already carries mass ≥ q),
  -- so logb 2 minCover / N ≤ logb 2 |typicalSet| / N ≤ (H + ε) + (logb 2 factor) / N → H + ε
  -- lower bound: any set with mass ≥ q must contain ≥ q - δ mass from the typical set, giving
  -- a size bound ≥ (q - δ) * 2 ^ (N (H - ε)) by the upper bound on per-typical mass.
  -- Upgrade to `Tendsto` via `Metric.tendsto_atTop`.
  ...
```

Implementation notes:

- `Nat.find` requires decidability of the existential `∃ n, ∃ S : Finset (Fin N → α), S.card = n ∧ q ≤ ∑ x ∈ S, iidDist p N x`. Use `Finset.decidableDExistsFinset` plus the decidability of the membership/cardinality conjunction on a finite type.
- Under `hq₁ : q < 1`, the existential is nonempty because the full `Finset.univ` has mass `1`. Add a helper `minCover_exists` proving nonemptiness cleanly; the lower hypothesis `hq₀` is part of the intended public contract, but the witness argument only needs `q < 1`.
- The `Tendsto` proof routes through `NNReal.tendsto_nhds` / `Metric.tendsto_atTop_nhds`: for every `ε' > 0`, produce `N₀` such that `|logb 2 (minCover p N q hq₀ hq₁) / N − entropyBits p| ≤ ε'` for `N ≥ N₀`. Take `ε' := ε/2` (or `ε/3` depending on how the tail-inclusion argument unfolds), then combine `typicalSet_iidDist_card_le` and `typicalSet_iidDist_card_ge` with `aep_iid`.

Base-2 corollaries on mass and cardinality use `(2 : ℝ) ^ x = Real.rpow 2 x`; `Real.rpow` plays well with `Real.logb` via `Real.logb_rpow`. If the reshaping cost inside this proof dominates the task, introduce the local `log2` / `exp2` wrappers proposed in Task 2; Task 5 is the deadline for making that call.

### 6. Testing (`ShannonTest/Entropy/{IID,AEP}.lean` and extensions)

New test files (one `example` per exported symbol, per the `write-lean-tests` skill and the existing Phase C mirror discipline):

- `ShannonTest/Entropy/IID.lean`: cover `iidDist`, `iidDist_apply`, `iidDist_entropyBits`, `iidDist_entropyNat`, `iidDist_succ_relabel`, `entropyBits_relabelInvariant`, `logProbBits`, `sum_mul_logProbBits`, `typicalSet`, `iidDist_le_of_mem_typicalSet`, `iidDist_ge_of_mem_typicalSet`.
- `ShannonTest/Entropy/AEP.lean`: cover `chebyshev_finite`, `aep_iid`, `typicalSet_iidDist_card_le`, `typicalSet_iidDist_card_ge`, `minCover`, `tendsto_logb_minCover_iid`.

Concrete composition tests (at least one per test file, in addition to the per-symbol regression mirrors):

- `ShannonTest/Entropy/IID.lean`:
  - `iidDist_entropyBits (uniformPNat 2) 4 = 4`. Closes by `rw [iidDist_entropyBits, entropyBits_uniformPNat]; norm_num` followed by `Real.logb_self`-style simplification.
  - `iidDist_entropyBits (uniformPNat 2) 0 = 0`. Edge case.
  - Explicit element of a typical set: on `α := Fin 2`, `p := ⟨fun i => if i = 0 then 0.3 else 0.7, ...⟩` (build `threeSeven : ProbDist (Fin 2)` as a local `let`), `N := 10`, `ε := 0.1`, and a concrete `x : Fin 10 → Fin 2` with six `0`s and four `1`s; check `x ∈ typicalSet threeSeven 10 0.1`. The empirical log-prob works out exactly (within 2026 Lean's `norm_num` reach), so the `example` closes by `decide` / `norm_num` once the arithmetic is spelled out. Budget this as the single largest test in the file (≈ 30 lines).
- `ShannonTest/Entropy/AEP.lean`:
  - `chebyshev_finite` on a two-point distribution (`uniformPNat 2`) with `f := id`, `ε := 1/2`; compute variance exactly, check the inequality.
  - `aep_iid` on `uniformPNat 2` with explicit `ε, δ`; check that the produced `N₀` is the expected value (the statement is an existential, so this is more of a smoke test: call the theorem and pattern-match on the witness).
  - `typicalSet_iidDist_card_le` on `uniformPNat 2`, `N := 4`, `ε := 0.1`: `|typicalSet|` coincides with `2 ^ 4 = 16` (every sequence is typical on a uniform source), and the bound `16 ≤ 2 ^ (4 * (1 + 0.1)) = 2 ^ 4.4 ≈ 21.1` holds comfortably. Close by `decide`-ish machinery on the cardinality side and `norm_num` on the bound side.
  - Skip a concrete `minCover` test (numerical; the `Tendsto` statement is the thing under test, and a concrete witness test would need extensive `Nat.find` unfolding). A symbol-mirror `example : minCover (uniformPNat 2) 4 0.5 = minCover (uniformPNat 2) 4 0.5 := rfl` plus a symbol mirror for `tendsto_logb_minCover_iid` suffices.

Aggregator update: add `import ShannonTest.Entropy.IID` and `import ShannonTest.Entropy.AEP` to `ShannonTest/Entropy.lean`.

Skill compliance: run `write-lean-tests` before writing each test file. Remember the discipline that a test case exercising a `def` through a downstream lemma counts as a regression test (per the Phase C review); it is better to exercise `iidDist` through `iidDist_entropyBits` than to write a standalone `example : iidDist p 3 = iidDist p 3 := rfl`.

### 7. Verso book chapter, transcription, facade, documentation

New chapter (`import VersoManual`, `#doc (Manual) "<Title>" => %%% tag := "<slug>" %%%`, single-long-line paragraphs, Lean identifiers in backticks, no `import Shannon`):

- `Book/IIDAndAEP.lean`: sections "I.i.d. Sources and the Product Distribution", "Per-Symbol Log-Probability and the Typical Set", "Theorem 3: The i.i.d. AEP", "Theorem 4: Counting the Typical Set", "Toward Finite-State Sources (Phase E)". Include the inline numerical walkthrough on `p = (0.3, 0.7)`, `N = 10`, `ε = 0.1` that the roadmap calls out: the most probable six-`1`s sequence has log-prob `log₂(0.7^6 * 0.3^4) = 6 log₂ 0.7 + 4 log₂ 0.3 ≈ -10.3`, the entropy is `h₂(0.3) ≈ 0.881`, so `(1/10) * 10.3 ≈ 1.03 ≈ 0.881 + 0.15`; sequences within `ε = 0.1` of entropy are "balanced" around the 7-to-3 split. Cross-link to `Book/MutualInformation.lean` for the role of information rate (rate = entropy under i.i.d.) and forward-reference `Book/FiniteStateAEP.lean` (Phase E) for the general case.

Chapter ordering update in `Book.lean` (insert between `FanoInequality` and `Bibliography`):

```
{include 0 Book.Introduction}
{include 0 Book.AxiomaticEntropy}
{include 0 Book.Properties}
{include 0 Book.Logarithm}
{include 0 Book.MutualInformation}
{include 0 Book.RelativeEntropy}
{include 0 Book.FanoInequality}
{include 0 Book.IIDAndAEP}
{include 0 Book.Bibliography}
```

Update the "Reading Order" list in `Book/Introduction.lean` to mention the new chapter and add pointers to `Shannon/Entropy/{IID, AEP}.lean`.

Transcription cross-references in `references/shannon1948-transcription.md`:

Replace the planned forward-pointer for Theorems 3 and 4 (the transcription currently lacks explicit cross-reference rows for those theorems; add them now) with:

- `**Theorem 3 (AEP, i.i.d. case)**: aep_iid in Shannon/Entropy/AEP.lean. Phase E will upgrade this to stationary finite-state sources; Theorem 3 is only "complete" in that broader setting.`
- `**Theorem 4 (typical set size, i.i.d. case)**: typicalSet_iidDist_card_le, typicalSet_iidDist_card_ge, and tendsto_logb_minCover_iid in Shannon/Entropy/AEP.lean. Same Phase E upgrade caveat as Theorem 3.`

Do not remove the existing Section-6 / Phase-C entries. Keep the existing cross-reference ordering otherwise.

Facade update in `Shannon/Entropy.lean`: add `import Shannon.Entropy.IID` and `import Shannon.Entropy.AEP`; extend the bulleted list ("Import this file to access...") to mention `iidDist`, `typicalSet`, `aep_iid`, `typicalSet_iidDist_card_le`, `typicalSet_iidDist_card_ge`, `minCover`, `tendsto_logb_minCover_iid`. Module-chain diagram additions:

```
- `{Joint, Bits} → IID → AEP`
```

`AEP` imports `IID`, which imports `Bits`, which imports `Joint`. No connection to the Phase C `MutualInfo → Fano` branch (the AEP machinery is orthogonal to Fano).

Update `AGENTS.md` / `CLAUDE.md` "Module Layout" section: add one-line entries for `Shannon/Entropy/{IID, AEP}.lean`. Mention in the `entropyBits`/`entropyNat` paragraph that Phase D adds the i.i.d. product and typical-set API (`iidDist`, `typicalSet`, `aep_iid`) to the base-2 public surface.

`cspell-words.txt` additions (alphabetical insertion, check after the prose edits):

- `aep` (AEP initialism, surfaces in module names and book prose)
- `Chebyshev` (prose; the helper lemma is named `chebyshev_finite`, all-lowercase)
- `iid` (IID initialism, common in book prose)
- `logProb` or `logprob` (surfaces in `logProbBits` and book prose)
- `minCover` or `mincover` (identifier casings)
- `typicalSet` or `typicalset` (identifier casings)

Re-run `make lint-spelling` after prose edits; add any additional words surfaced.

Roadmap sync in `docs/plans/todo/2026-04-14-shannon-proofs-roadmap.md`: mark Phase D's module list as finalized (the parent roadmap already says `Shannon/Entropy/{IID, AEP}.lean`; confirm this matches the landing structure). Update Phase D's open issue ("whether `Real.logb 2` / `(2 : ℝ) ^ _` arithmetic has enough Mathlib support to keep proofs clean...") with the resolution decided during Task 5 (either "kept Mathlib-native, no wrapper needed" or "introduced local `log2`/`exp2` helpers in `IID.lean`").

## Critical files

Existing, to modify (rough task order):

- `Shannon/Entropy/Bits.lean`: add `entropyBits_relabelInvariant` (Task 1a, small feeder lemma).
- `Shannon/Entropy.lean`: add imports and update module-chain diagram (Task 7).
- `docs/plans/todo/2026-04-14-shannon-proofs-roadmap.md`: sync Phase D inventory and resolve the `Real.logb 2` / `rpow` open question with the decision taken during Task 5 (Task 7).
- `ShannonTest/Entropy.lean`: register the two new test modules (Task 6).
- `ShannonTest/Entropy/Bits.lean`: add the `entropyBits_relabelInvariant` example (Task 6).
- `Book.lean`: include the new chapter (Task 7).
- `Book/Introduction.lean`: extend reading-order list (Task 7).
- `references/shannon1948-transcription.md`: add two cross-reference bullets (Task 7).
- `AGENTS.md` / `CLAUDE.md` (symlink): module-layout entries (Task 7).
- `cspell-words.txt`: add words surfaced by prose (Task 7).

New, to create:

- `Shannon/Entropy/IID.lean` (Tasks 1 and 2).
- `Shannon/Entropy/AEP.lean` (Tasks 3, 4, 5).
- `ShannonTest/Entropy/IID.lean` (Task 6).
- `ShannonTest/Entropy/AEP.lean` (Task 6).
- `Book/IIDAndAEP.lean` (Task 7).

## Commit strategy

Seven commits keep the branch reviewable. Each library commit is self-contained (library + its test mirror + any docstring and facade edits needed for that commit to pass `make check` in isolation). The Verso book chapter plus transcription cross-references plus facade plus docs ride a single trailing commit so the code-reviewable commits do not interleave with prose-dense ones.

1. `feat(entropy): entropyBits_relabelInvariant corollary` (Task 1a, `Bits.lean` plus `ShannonTest/Entropy/Bits.lean`). Small preparatory commit; lands independently so Task 1's induction step cites a committed lemma rather than one being introduced in the same diff.
2. `feat(entropy): iidDist and N-fold entropy additivity` (Task 1, `IID.lean` with `iidDist`, `iidDist_apply`, `iidDist_succ_relabel`, `iidDist_entropyNat`, `iidDist_entropyBits`, `logProbBits`, `sum_mul_logProbBits`, matching test entries in the new `ShannonTest/Entropy/IID.lean`).
3. `feat(entropy): typical set and per-element bounds (bits)` (Task 2, `typicalSet` definition plus `iidDist_le_of_mem_typicalSet` and `iidDist_ge_of_mem_typicalSet`, test extension). If local `log2`/`exp2` wrappers are needed, they land here.
4. `feat(entropy): finite Chebyshev concentration on ProbDist` (Task 3a plus the sample-mean and variance-scaling internal lemmas, new `AEP.lean` file with a smoke-test example in `ShannonTest/Entropy/AEP.lean`).
5. `feat(entropy): i.i.d. AEP (Theorem 3, base 2)` (Task 3c, `aep_iid`, test extension).
6. `feat(entropy): typical set cardinality bounds and minCover rate (Theorem 4, i.i.d. case)` (Tasks 4 and 5, `typicalSet_iidDist_card_le`, `typicalSet_iidDist_card_ge`, `minCover`, `tendsto_logb_minCover_iid`, test extension). Tasks 4 and 5 share consumers and are kept together; Task 5's `Tendsto` proof directly reuses Task 4's bounds.
7. `docs(book): IIDAndAEP chapter, transcription cross-refs, facade and docs` (Task 7 book addition, transcription cross-references, facade edits, Introduction reading-order update, AGENTS.md module-layout entries, cspell-words updates, roadmap sync).

If commit 6 grows beyond ~200 insertions in `AEP.lean`, split it into `6a: card bounds` (Tasks 4) and `6b: minCover asymptotic rate` (Task 5). The split is honest: Task 4 is an algebraic corollary of Task 2's per-element bounds plus the AEP mass from Task 3; Task 5 is a distinct `Tendsto` argument that packages Tasks 3 and 4 together.

If the branch exceeds ~15 commits during implementation, consider splitting into two PRs:

- PR 1: Tasks 1, 2, 3 (product construction, typical set, AEP) plus partial book coverage (the first three sections of `Book/IIDAndAEP.lean`).
- PR 2: Tasks 4, 5 (Theorem 4 bounds and minCover rate) plus the remaining two sections of `Book/IIDAndAEP.lean`, transcription, facade, docs.

The roadmap's Phase D unit stays coherent across both PRs; splitting is an implementation convenience, not a scope change.

## Verification

Per-task tripwires (run locally before committing each task):

- Task 1a: `lake build Shannon.Entropy.Bits` compiles; the one-line test example in `ShannonTest/Entropy/Bits.lean` passes.
- Task 1: `lake build Shannon.Entropy.IID` compiles cold; `iidDist_entropyBits (uniformPNat 2) 4 = 4` passes; `iidDist_entropyBits _ 0 = 0` passes.
- Task 2: the typical-set definition elaborates without a classical-axiom warning (`DecidableEq α` is sufficient); the explicit `(0.3, 0.7)` / `N = 10` / `ε = 0.1` membership example passes; both per-element bounds close.
- Task 3: `lake build Shannon.Entropy.AEP` compiles cold; the Chebyshev smoke test passes; `aep_iid (uniformPNat 2) (hε := by norm_num) (hδ := by norm_num)` is typable and produces a concrete `N₀`.
- Task 4: `typicalSet_iidDist_card_le (uniformPNat 2) 4 0.1` numerically passes (`|typicalSet| = 16 ≤ 2 ^ 4.4`).
- Task 5: `lake build Shannon.Entropy.AEP` compiles in full; the `Tendsto` statement elaborates (witnessed by `apply Metric.tendsto_atTop.2` or equivalent); symbol-mirror test passes.
- Task 6: `lake test` green end-to-end; every new public definition or theorem has a matching `example` in the appropriate `ShannonTest/Entropy/*.lean` file.
- Task 7: `lake build Book` compiles cold; `make book` produces `_site/html-multi/index.html` listing all nine chapters (Introduction, AxiomaticEntropy, Properties, Logarithm, MutualInformation, RelativeEntropy, FanoInequality, IIDAndAEP, Bibliography) in the TOC.

End-of-phase checks (`make check` is the blanket command):

- `make check` passes end-to-end: markdownlint, cspell, `lake lint`, `lake build`, `lake test`.
- `make book` produces non-empty rendered output under `_site/html-multi/` with the expected nine-chapter TOC.
- `bin/bootstrap-worktree` still works from a clean worktree (spot-check by deleting `.lake/` and re-running). Phase D adds no new Lake dependencies, so this is a regression check rather than a new-behavior check.
- Spot-check the rendered book via `make serve`: confirm the new chapter renders, internal cross-references resolve (including the forward pointer to `Book/FiniteStateAEP.lean` which will not yet exist; render it as plain prose "Phase E will introduce..." rather than as a broken `Book.FiniteStateAEP` link), and the depth-2 TOC view still looks right after the addition.

Roadmap-level sanity checks (Phase D row of the roadmap's `## Verification` section):

- Pick `α := Fin 2`, `p := (0.3, 0.7)`, `N := 10`, `ε := 0.1`; check an explicit element of the typical set and the bounds on `|typicalSet|`. Concrete case lives in `ShannonTest/Entropy/IID.lean`; any refinement during implementation (for example a different `ε` that makes the arithmetic cleaner) is recorded in the test file and in the final-commit message.

Upstream-sync note: Phase D introduces strictly new modules (`IID`, `AEP`) that do not exist in `upstream/main`, plus one feeder lemma (`entropyBits_relabelInvariant`) in `Bits.lean`, which is itself a Phase B module not yet upstream. The only modification to a shared upstream module is `Joint.lean`, which is unchanged in this phase; facade and test-aggregator edits are strictly additive. Upstream-PR consideration stays deferred to after merge.

## Open questions (to resolve during execution)

- **`Real.logb 2` / `Real.rpow` ergonomics**: the roadmap's Phase D open question. Task 5's `Tendsto` proof is the stress test; if the Mathlib API is enough to keep proofs readable, skip the local wrapper. Otherwise, introduce a one-module-scope `log2 x := Real.logb 2 x` / `exp2 x := (2 : ℝ) ^ x` namespace inside `IID.lean` with the three arithmetic lemmas (`log2_exp2`, `exp2_log2`, `exp2_add`) the AEP proofs need, and land it with Task 5. Do **not** widen the public surface with this wrapper; Phase E can lift it if a second consumer materializes.
- **Variance-scaling proof style**: the standard `Var(Y̅_N) = Var(Y) / N` identity factors cleanly through an independence-style cross-term cancellation. If the cross-term bookkeeping becomes fragile at the pinned Mathlib (especially around `Finset.sum_pow` / `sum_prod_comm` reshapes), weaken the statement only to an explicit `≤ C / N` bound for some constant `C := ∑ a, p a * (logProbBits p a - entropyBits p)^2` (or a slightly larger closed-form constant). Do not weaken to `≤ C`: Chebyshev would then fail to force the tail to `0`, so `aep_iid` would not follow.
- **`minCover` witness shape**: the `Nat.find` formulation is the cleanest statement, but the proof needs explicit decidability instances and a nonemptiness witness, and the definition is intentionally restricted to interior thresholds `0 < q < 1`. If `Nat.find`'s decidability chain proves painful, fall back to a `Classical.choose`-based definition (strictly noncomputable) plus a `minCover_spec` characterization with the same threshold hypotheses. The book chapter cites `minCover` by name; the choice between `Nat.find` and `Classical.choose` is invisible from the prose.
- **`typicalSet` on `p` with partial support**: the plan's support restriction is `∀ i, 0 < p (x i)`. For `p` with full support (the common case, including `uniformPNat`), the restriction is vacuous. For `p` with zero atoms, the restriction automatically excludes `x` with any zero coordinate, which is already mass-zero under `iidDist p N`. Confirm in the Task 2 implementation that `typicalSet p N ε = Finset.univ.filter (numerical condition only)` on full-support `p`; if not, add a `typicalSet_of_fullSupport` convenience lemma.
- **Book chapter forward pointer**: `Book/IIDAndAEP.lean` references Phase E's `Book.FiniteStateAEP`, which does not exist yet. Render the pointer as plain prose inside `Section "Toward Finite-State Sources (Phase E)"`, not as a `{docPage Book.FiniteStateAEP}` reference that would fail to resolve at book build time. When Phase E lands, upgrade the prose to an actual cross-reference.
