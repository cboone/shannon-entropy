# Shannon Proofs Roadmap

Date: 2026-04-14
Status: proposed

## Context

The Lean 4 formalization currently covers Shannon Appendix 2 (uniqueness of
`H = -K Σ pᵢ log pᵢ`) and Section 6 Properties 1–6, all with complete proofs
(no `sorry`, no external axioms). Fidelity to Shannon's Appendix 2 argument
is already very close: the `Apos_mul` / `Apos_pow` / ratio-squeeze chain in
`Shannon/Entropy/Uniform.lean` mirrors Shannon's derivation step by step, and
`Rational.lean` includes Shannon's worked `(1/2, 1/3, 1/6)` tree example.

The paper transcription in `references/shannon1948-transcription.md` declares
a wider target scope:

- Theorem 2 (uniqueness) — done
- Properties 1–6 — done
- Theorem 3 (AEP) — not yet formalized
- Theorem 4 (typical set size) — not yet formalized
- Theorems 5–6 (per-symbol entropy `Gₙ`, `Fₙ` convergence) — not yet formalized
- Theorem 7 (data processing inequality) — not yet formalized

Goal: extend the formalization to cover the transcription's stated scope,
tighten the existing proofs' correspondence to Shannon's narrative, and
publish a Verso companion book that walks a reader through the paper and
the Lean formalization side by side. Each phase is shippable on its own;
later phases depend on earlier ones.

Non-goal: full coverage of Shannon's paper. Continuous / differential
entropy, channel capacity, and the noisy channel coding theorem stay out of
scope here (see Phase F note). Upstream PRs are welcome but not prioritized
(the fork's primary purpose is independent maintenance).

Design decisions locked in for this plan:

- The formalization ships through Phase E (transcription-faithful
  finite-state statistical sources, Shannon Theorems 3–7). Phase F is
  explicitly deferred.
- Phase D is explicitly the i.i.d. special case of Shannon's Theorems 3
  and 4. Phase E upgrades those results to the paper's finite-state source
  setting using Shannon's state-space model and product-state transducer
  proof pattern.
- Base-2 logarithms are the native output for all new Phase C+ theorems.
  `entropyBits` becomes the primary public entropy API; `entropyNat` (natural
  log) stays as an internal helper used inside proofs. Phase B introduces
  the base-2 API so downstream phases can state results directly as
  bits-valued.
- Every phase has explicit testing tasks, matching the existing
  `ShannonTest/` discipline.
- Every phase (B onward) includes a Verso book update so the companion
  walkthrough stays in lockstep with the code.

## Phase A — Verso companion book setup

Goal: add a Verso-powered book that will grow alongside the Lean code,
containing a math-and-Lean walkthrough of Shannon's paper. The book lives
in-repo as a separate Lake target; each later phase adds at least one
chapter.

Tasks:

1. Add Verso as a Lake dependency. Pick a Verso revision compatible with
   Lean `v4.29.0` (currently pinned in `lean-toolchain`). Document the
   compatibility check in `lakefile.toml` as a trailing comment or in the
   first book chapter. If no compatible Verso exists, fall back to plain
   Pandoc Markdown under `docs/book/` and revisit when Verso catches up.
2. Scaffold the book.
   - Create a new Lake library target `ShannonBook`.
   - Layout: `Book/Main.lean` as entry, `Book/Chapters/` for per-chapter
     files, `Book/Chapters/Bibliography.lean` for citations, a
     `Book/Config.lean` for genre/style config.
3. Initial chapters.
   - `Chapters/Introduction.lean`: paper overview, fork relationship,
     scope (what is formalized, what is not), reading order, how to run
     `lake build Shannon`.
   - `Chapters/Foundations.lean`: `ProbDist`, `composeProb`, `relabelProb`,
     `uniformPNat`; quote relevant Shannon paragraphs and the
     `ShannonEntropyAxioms` structure side by side.
   - `Chapters/Bibliography.lean`: Shannon 1948 with DOI, supporting
     references (Cover and Thomas, MacKay).
4. Build target.
   - `lake build ShannonBook` builds HTML / PDF output under `.lake/build/doc/`.
   - Add a `make book` convenience target.
   - Document in `README.md` under a new "Companion book" section.
5. CI integration.
   - Extend `.github/workflows/ci.yml` with a `book` job that runs
     `lake build ShannonBook`.
   - Optional follow-up (flagged, not required this phase): publish to
     GitHub Pages on `main` merges.
6. Testing.
   - `lake build ShannonBook` passes in CI.
   - `make check` still passes end-to-end.
   - Add an `example`-style smoke test under `ShannonTest/Book.lean` that
     imports the book's top-level module to catch import regressions.
   - Ensure cspell dictionary covers Verso-specific terms added to prose.

Files created: `Book/Main.lean`, `Book/Chapters/*.lean`, `Book/Config.lean`,
`ShannonTest/Book.lean`. Files modified: `lakefile.toml`, `lake-manifest.json`,
`README.md`, `Makefile`, `.github/workflows/ci.yml`, `cspell-words.txt`.

## Phase B — Revision: tighten correspondence with Shannon's narrative

Goal: make each existing proof traceable to a specific page / argument in
Shannon's paper; fill test-coverage gaps; introduce the base-2 public API
that Phases D and E will use; start populating the Verso book with the
already-done material.

Tasks:

1. Base-2 public API.
   - Introduce `entropyBits` (base-2 Shannon entropy) in a new
     `Shannon/Entropy/Bits.lean`, defined via `entropyBase 2` but exposed as
     the primary name.
   - Add the bridge lemma `entropyBits_eq_entropyNat_div_log_two`
     (and reverse direction) so downstream proofs can switch base without
     fighting `Real.logb` unfolding each time.
   - Restate `entropyNat_unique` and `entropyBase_unique` in terms of
     `entropyBits` as corollaries (keeps old names; adds new ones).
   - Re-export `entropyBits` from the `Shannon.Entropy` facade.
2. Narrative docstrings in existing modules. For `Uniform.lean`,
   `Rational.lean`, `Approx.lean`, `Final.lean`, expand the top-of-module
   docstring with Shannon's informal argument adjacent to the formal
   statement, with page references (Appendix 2, pp. 48–49). Surface the
   mnemonic `A(sᵐ) = m·A(s)` and the ratio-confinement bound
   `sᵐ ≤ tⁿ < sᵐ⁺¹`.
3. Shannon-form conditional entropy. Add `condEntropy_eq_shannon_form` in
   `Shannon/Entropy/Joint.lean`: Shannon writes
   `H_x(y) = -∑ p(i, j) log p_i(j)`; expose that as a named lemma.
   Default conditional entropy definition stays unchanged.
4. Sync upstream stylistic cleanups. `Properties.lean`, `Rational.lean`,
   `Uniform.lean` differ from upstream in minor tactic choices
   (`push Not` → `push_neg`; `simp only … rw …` → `simpa …`). Bring these
   over in one commit so a future upstream PR has a clean diff.
5. Testing.
   - New test files: `ShannonTest/Entropy/Uniform.lean`,
     `ShannonTest/Entropy/Rational.lean`, `ShannonTest/Entropy/Gibbs.lean`,
     `ShannonTest/Entropy/Bits.lean`.
   - Cases to exercise: `Apos_mul` on concrete `n, m`; `Apos_eq_K_mul_log`
     on `n = 4` equal to `2 · Apos H 2`; `entropyNat_of_rational_counts` on
     Shannon's `(1/2, 1/3, 1/6)` distribution; `gibbs_inequality` with a
     concrete non-equal `p, q`; `entropyBits (uniformPNat 2) = 1`;
     `entropyBits (uniformPNat 4) = 2`.
   - Update existing `ShannonTest/Entropy/Final.lean` to additionally check
     the `entropyBits`-flavored corollary.
   - `make check` green end-to-end.
6. Verso book update.
   - New chapter `Chapters/AxiomaticEntropy.lean` walks Shannon's Appendix 2
     proof with references into `Shannon/Entropy/{Uniform, Rational, Approx,
     Final}.lean`.
   - New chapter `Chapters/Properties.lean` walks Section 6 Properties
     1–6 with references into `Shannon/Entropy/{Joint, Properties,
     Gibbs}.lean`.
   - New chapter `Chapters/Logarithm.lean` discusses the `K` scale
     constant, base choice, and the `entropyBits` API.
   - `Book/Main.lean` links the new chapters in order.

Files touched: `Shannon/Entropy/{Uniform, Rational, Approx, Final, Joint,
Properties}.lean`, new `Shannon/Entropy/Bits.lean`, new files in
`ShannonTest/Entropy/`, new files in `Book/Chapters/`.

## Phase C — Information-theoretic primitives

Goal: complete the primitives layer (mutual information properties,
relative entropy, log-sum inequality, data processing inequality in its
information form). All items are short derivations from Gibbs and existing
infrastructure; they unblock Phase D and round out Section 6.

Tasks:

1. New module `Shannon/Entropy/MutualInfo.lean`. Prove:
   - `mutualInfo_nonneg`: `I(X;Y) ≥ 0`
     (Gibbs applied to `p(x,y)` vs. `p(x)·p(y)`)
   - `mutualInfo_eq_zero_iff_independent`
   - `mutualInfo_symm`: `I(X;Y) = I(Y;X)`
   - `mutualInfo_eq_entropy_sub_condEntropy`: `I(X;Y) = H(X) − H(X|Y)`
     (and the `H(Y) − H(Y|X)` dual)
   - `mutualInfo_self`: `I(X;X) = H(X)`
   - `mutualInfo_le_entropy`: `I(X;Y) ≤ min(H(X), H(Y))`
   - Also provide the base-2 variants `mutualInfoBits` via `entropyBits`.
2. New module `Shannon/Entropy/RelativeEntropy.lean`. Define
   `relEntropy (p q : ProbDist α) : ℝ := ∑ a, p a * log (p a / q a)` (KL
   divergence `D(p‖q)`) with the `0 · log 0 = 0`, `log 0 = 0` conventions,
   and a `relEntropyBits` variant. Prove:
   - `relEntropy_nonneg`
   - `relEntropy_eq_zero_iff`: `D(p‖q) = 0 ↔ p = q` pointwise
   - Reframe `gibbs_inequality` to additionally state `−relEntropy p q ≤ 0`
     (keep existing form for backward compatibility).
3. Log-sum inequality. In `RelativeEntropy.lean`: for nonneg sequences
   `aᵢ, bᵢ` with `∑ aᵢ = A`, `∑ bᵢ = B`,
   `∑ aᵢ · log (aᵢ/bᵢ) ≥ A · log (A/B)`.
4. Data processing inequality (information form). In `MutualInfo.lean`:
   given a kernel `W : α → ProbDist γ` and a joint `(X, Y)`, the Markov
   chain `X → Y → Z := (W (Y ·))` satisfies `I(X;Z) ≤ I(X;Y)`. (Phase E
   covers Shannon's transducer form, which is Theorem 7.)
5. Fano's inequality. `H(X|Y) ≤ h₂(Pₑ) + Pₑ · log(|X| − 1)` where `Pₑ` is
   the error probability of an estimator. State and prove in base 2 via
   `entropyBits`.
6. Testing.
   - New test files `ShannonTest/Entropy/MutualInfo.lean`,
     `ShannonTest/Entropy/RelativeEntropy.lean`.
   - Cases: `mutualInfo_nonneg` on an independent `prodDist` gives exactly
     zero; `mutualInfo_self` on a two-point uniform gives `1` bit;
     `relEntropy` of `(1/2, 1/2)` vs. `(1/4, 3/4)` matches the closed-form
     value; `log_sum_inequality` equality case when `aᵢ = bᵢ`; Fano's
     inequality numerically sanity-checked on a two-symbol alphabet with a
     known error probability.
   - `make check` green.
7. Verso book update.
   - New chapter `Chapters/MutualInformation.lean` covers `I(X;Y)` and the
     identities proved in this phase.
   - New chapter `Chapters/RelativeEntropy.lean` covers `D(p‖q)`, the
     log-sum inequality, and the information-form DPI.
   - New chapter `Chapters/FanoInequality.lean` discusses the estimator
     setting and points forward to Phase E.
   - Chapter ordering in `Book/Main.lean` updated.

Files created: `Shannon/Entropy/MutualInfo.lean`,
`Shannon/Entropy/RelativeEntropy.lean`, matching test files, new Book
chapters. Facade `Shannon.Entropy.lean` updated.

## Phase D — I.i.d. AEP and typical sets (Theorems 3–4 special case)

Goal: formalize the i.i.d. special case of Shannon's Theorems 3 and 4,
with statements in base 2 (matching Shannon's `2^(NH)` phrasing directly
rather than converting from natural log after the fact). Phase E upgrades
these statements to the transcription-faithful finite-state-source setting.

Tasks:

1. New module `Shannon/Entropy/IID.lean`.
   - `iidDist (p : ProbDist α) (N : ℕ) : ProbDist (Fin N → α)` defined via
     `fun x => ∏ i, p (x i)`. The simplex proof iterates `prodDist` or uses
     `Finset.prod_univ_sum` style lemmas.
   - `iidDist_entropyBits`:
     `entropyBits (iidDist p N) = N · entropyBits p` (N-fold additivity).
   - `logProbBits p x := -Real.logb 2 (p x)` on the support of `p`; add a
     support-aware wrapper so typical-set statements exclude impossible
     symbols.
2. Typical set (base 2 directly).
   - `typicalSet (p : ProbDist α) (N : ℕ) (ε : ℝ) : Finset (Fin N → α)`
     defined as the support-restricted set
      `{x | (∀ i, 0 < p (x i)) ∧
        |(1/N) · ∑ i, -Real.logb 2 (p (x i)) − entropyBits p| < ε}`.
   - Per-element bounds
     `2^(-N·(entropyBits p + ε)) ≤ iidDist p N x ≤ 2^(-N·(entropyBits p - ε))`
     for `x` typical (directly in `2^…`, no natural-log detour).
3. Theorem 3 (AEP). `aep_iid`:
   `∀ ε δ > 0, ∃ N₀, ∀ N ≥ N₀,
      ∑ x ∈ typicalSet p N ε, iidDist p N x ≥ 1 − δ`.
   Proof route: apply a Chebyshev bound to the random variable
   `Yᵢ := -Real.logb 2 (p (Xᵢ))`. Mean is `entropyBits p`; variance is
   bounded by `∑ p a · (Real.logb 2 (p a))²` on a finite alphabet. Prefer a
   direct Chebyshev argument to invoking Mathlib's measure-theoretic LLN.
4. Theorem 4 (typical set size).
   - `typicalSet_card_lower`:
     `(1 − δ) · 2^(N · (entropyBits p − ε)) ≤ |typicalSet p N ε|` for
     `N` large enough
   - `typicalSet_card_upper`:
     `|typicalSet p N ε| ≤ 2^(N · (entropyBits p + ε))`
   - Add `minCover p N q := min {|S| : S ⊆ univ ∧ iidDist p N S ≥ q}` and
     derive `Tendsto (fun N => (Real.logb 2 (minCover p N q)) / N)`
     `atTop (𝓝 (entropyBits p))` for `0 < q < 1`.
5. Testing.
   - New test files `ShannonTest/Entropy/IID.lean`,
     `ShannonTest/Entropy/AEP.lean`.
   - Cases: `iidDist_entropyBits` on `α := Fin 2`, `p := (0.5, 0.5)`,
     `N := 4` gives `4`; explicit element-of-typical-set construction for
     `p := (0.3, 0.7)`, `N := 10`, `ε := 0.1`; upper bound on
     `|typicalSet|` numerically checked; `minCover` computed on a small
     fixed case.
   - `make check` green.
6. Verso book update.
   - New chapter `Chapters/IIDAndAEP.lean` covers the i.i.d. product
     construction, the typical set, and the i.i.d. special case of
     Theorems 3 and 4.
   - Inline numerical example: walk through the `p = (0.3, 0.7)`, `N = 10`
     case with explicit probabilities, showing the typical set bounds.
   - Cross-link to `Chapters/MutualInformation.lean` for the role of
     information rate.

Files created: `Shannon/Entropy/IID.lean`, `Shannon/Entropy/AEP.lean`,
matching tests, new Book chapter.

Open issue to resolve during execution: whether `Real.logb 2` /
`(2 : ℝ) ^ _` arithmetic has enough Mathlib support to keep proofs clean,
or whether we need a thin wrapper. If awkward, add a small `Bits` namespace
with `log2`, `exp2`, and conversion lemmas used across Phases D and E.

## Phase E — Finite-state statistical sources and entropy rate (Theorems 3–7)

Goal: upgrade Phase D's i.i.d. results to Shannon's transcription-faithful
finite-state-source setting and formalize Theorems 5, 6, and 7 in the same
model. The source model follows Shannon's state-space presentation: hidden
states carry the residue of influence, emitted symbols arise on
transitions, and finite-state transducers are handled by product state
spaces. All entropy-rate statements use base 2 (`entropyBits`-valued).

Tasks:

1. New module `Shannon/Entropy/FiniteStateSource.lean`.
   - `structure FiniteStateSource (S A : Type) [Fintype S] [Fintype A]`
     bundling `init : ProbDist S` and
     `step : S → ProbDist (S × A)`.
   - `outputDist (M : FiniteStateSource S A) (N : ℕ) : ProbDist (Fin N → A)`
     for output-block probabilities.
   - `nextStateKernel` extracted from the transition/emission kernel.
   - `IsStationary (π : ProbDist S) (K : S → ProbDist (S × A)) :=
        ∀ s, π s = ∑ s', ∑ a, π s' · K s' (s, a)`.
   - Existence of a stationary distribution for any irreducible finite
     hidden-state chain (Perron–Frobenius; use Mathlib's stochastic-matrix
     results if available, otherwise an elementary argument via the
     simplex).
   - Provide constructors / special cases for i.i.d. sources and visible
     Markov chains, so the old `MarkovSource` viewpoint is recovered as a
     special case rather than the primary abstraction.
2. Upgrade Theorems 3 and 4 to the transcription-faithful finite-state
   source setting.
   - Define a per-symbol information-density notion and a typical set for
     output blocks of a stationary finite-state source.
   - Prove the base-2 AEP and typical-set cardinality / `minCover` results
     in this model, reusing Phase D's i.i.d. theorems as warm-up lemmas or
     corollaries where appropriate.
   - Update the transcription cross-references so Theorems 3 and 4 are only
     marked complete once this phase lands.
3. Block entropy definitions.
   - `G (M : FiniteStateSource S A) (N : ℕ) : ℝ :=
        (1 / N) · entropyBits (outputDist M N)`
   - `F (M : FiniteStateSource S A) (N : ℕ) : ℝ` = entropy (base 2) of the
     N-th emitted symbol conditional on the preceding `N − 1` emitted
     symbols.
   - `entropyRate (M : FiniteStateSource S A) (π : ProbDist S) : ℝ :=`
     `∑ s, π s · entropyBits (M.step s)` under `IsStationary π M.step`.
4. Theorem 5. For a stationary finite-state source:
   - `G_monotone_decreasing`: `G (N + 1) ≤ G N`
   - `G_tendsto_entropyRate`
5. Theorem 6. Algebraic identities:
   - `F_eq_NG_sub_prev`: `F N = N · G N − (N − 1) · G (N − 1)`
   - `G_eq_avg_F`:
     `G N = (1 / N) · ∑ n ∈ Finset.range N, F (n + 1)`
   - `F_le_G`
   - `F_monotone_decreasing`
   - `F_tendsto_entropyRate`
6. Theorem 7 (data processing, transducer form).
   - Model a finite-state transducer with internal state and emitted output
     blocks.
   - Form the product state space `(sourceState × transducerState)` to show
     that the output process is again a finite-state statistical source in
     Shannon's sense.
   - Prove that output entropy rate is no larger than input entropy rate,
     with equality for non-singular transducers.
7. Testing.
   - New test files `ShannonTest/Entropy/FiniteStateSource.lean`,
     `ShannonTest/Entropy/EntropyRate.lean`,
     `ShannonTest/Entropy/Transducer.lean`.
   - Cases: concrete 2-state Markov chain with transition matrix
     `[[0.8, 0.2], [0.4, 0.6]]`, encoded as a `FiniteStateSource` special
     case; stationary distribution computed and verified; `G N`, `F N`
     evaluated at `N = 1, 2, 3` and compared against hand-computed values;
     product-state closure sanity check for a nontrivial transducer;
     transducer example where a merging transducer strictly decreases
     entropy rate.
   - `make check` green.
8. Verso book update.
   - New chapter `Chapters/FiniteStateSources.lean` on Shannon's
     state-space source model, stationary distributions, and product-state
     constructions.
   - Update `Chapters/IIDAndAEP.lean` to mark Phase D as the i.i.d. warm-up
     special case.
   - New chapter `Chapters/FiniteStateAEP.lean` on the
     transcription-faithful finite-state-source versions of Theorems 3
     and 4.
   - New chapter `Chapters/PerSymbolEntropy.lean` on `G_N`, `F_N`,
     Theorems 5 and 6.
   - New chapter `Chapters/DataProcessing.lean` on the transducer form of
     Theorem 7; tie back to the information-form DPI from Phase C.
   - Final chapter `Chapters/Conclusion.lean` summarizes scope covered
     and explicitly lists Phase F items as future work.

Files created: `Shannon/Entropy/FiniteStateSource.lean`,
`Shannon/Entropy/EntropyRate.lean`, `Shannon/Entropy/Transducer.lean`,
matching tests, new Book chapters.

## Phase F — Out of scope

Explicitly deferred:

- Continuous / differential entropy (Shannon's Sections 17+).
- Discrete memoryless channel model and channel capacity.
- Noisy channel coding theorem.
- Source coding theorem for the noiseless channel.
- Fundamental theorem for a noisy channel with a cost constraint.

Each is a multi-month subproject and belongs in its own plan. The Phase E
Verso conclusion chapter will flag these as natural successors.

## Critical files

Existing, to modify:

- `Shannon/Entropy/Joint.lean` — add `condEntropy_eq_shannon_form`
- `Shannon/Entropy/Gibbs.lean` — cross-reference with `relEntropy`
- `Shannon/Entropy/Final.lean` — add `entropyBits`-flavored corollaries
- `Shannon/Entropy.lean` — facade imports for every new module
- `Shannon.lean` — top-level re-export
- `lakefile.toml`, `lake-manifest.json` — Verso dependency, new lean_libs
- `Makefile` — `make book` target
- `.github/workflows/ci.yml` — Verso build job
- `README.md` — companion book section, updated scope
- `references/shannon1948-transcription.md` — append cross-references for
  each newly formalized theorem as it lands
- `cspell-words.txt` — Verso / information-theory vocabulary

New, to create:

- Phase A: `Book/Main.lean`, `Book/Chapters/{Introduction, Foundations,
  Bibliography}.lean`, `Book/Config.lean`, `ShannonTest/Book.lean`
- Phase B: `Shannon/Entropy/Bits.lean`,
  `ShannonTest/Entropy/{Uniform, Rational, Gibbs, Bits}.lean`,
  `Book/Chapters/{AxiomaticEntropy, Properties, Logarithm}.lean`
- Phase C: `Shannon/Entropy/{MutualInfo, RelativeEntropy}.lean`,
  `ShannonTest/Entropy/{MutualInfo, RelativeEntropy}.lean`,
  `Book/Chapters/{MutualInformation, RelativeEntropy, FanoInequality}.lean`
- Phase D: `Shannon/Entropy/{IID, AEP}.lean`,
  `ShannonTest/Entropy/{IID, AEP}.lean`,
  `Book/Chapters/IIDAndAEP.lean`
- Phase E: `Shannon/Entropy/{FiniteStateSource, EntropyRate, Transducer}.lean`,
  `ShannonTest/Entropy/{FiniteStateSource, EntropyRate, Transducer}.lean`,
  `Book/Chapters/{FiniteStateSources, FiniteStateAEP, PerSymbolEntropy,
  DataProcessing, Conclusion}.lean`

## Existing utilities to reuse

From the current codebase:

- `ProbDist`, `composeProb`, `relabelProb`, `uniformPNat`,
  `sigmaConstFinEquivFinMul` (`Shannon/Entropy/Core.lean`)
- `entropyNat`, `entropyBase`, `Apos`, `K`, `Apos_mul`, `Apos_eq_K_mul_log`
  (`Shannon/Entropy/Uniform.lean`)
- `gibbs_inequality`, `entropyNat_eq_sum_negMulLog`, `entropyNat_uniformPNat`,
  `entropyNat_le_log_card`, `entropyNat_nonneg` (`Shannon/Entropy/Gibbs.lean`)
- `marginalFst`, `marginalSnd`, `prodDist`, `IsIndependent`, `condEntropy`,
  `mutualInfo`, `chain_rule`, `entropyNat_prodDist`
  (`Shannon/Entropy/Joint.lean`)
- `entropyNat_doublyStochastic_le`, `condEntropy_le_entropyNat`,
  `condEntropy_nonneg`, `entropyNat_eq_log_card_iff`,
  `entropyNat_eq_zero_iff` (`Shannon/Entropy/Properties.lean`)
- `entropyNat_shannonAxioms` (`Shannon/Entropy/Converse.lean`)

From Mathlib:

- `Real.negMulLog`, `Real.log_le_sub_one_of_pos`, `Real.logb`, `Real.rpow`,
  `Real.exp_log`
- `Finset.sum_prod_type`, `Finset.prod_univ_sum`, `Fintype.sum_sigma`
- `Matrix.doublyStochastic`, `Matrix.stochastic` (Phase E Perron–Frobenius)
- `Probability.ProbabilityTheory` modules (possibly useful for Phase D
  variance / Chebyshev, but lightweight direct arguments are preferred)

## Verification

Applies to every phase:

- `make check` passes (markdown lint, cspell, `lake lint`, `lake build`,
  `lake test`).
- `lake build ShannonBook` passes starting in Phase A.
- Every new public definition or theorem has a corresponding entry in
  `ShannonTest/Entropy/…` exercising a concrete instance.
- Each phase updates the `Formalization Cross-References` section in
  `references/shannon1948-transcription.md` with the new theorem names,
  and adds the corresponding Book chapter.

Per-phase sanity checks:

- Phase A: `lake build ShannonBook` generates non-empty output in
  `.lake/build/doc/`; the book's table of contents lists the Introduction
  and Foundations chapters.
- Phase B: `entropyBits (uniformPNat 2) = 1`;
  `entropyBits (uniformPNat 4) = 2`; Shannon's worked `(1/2, 1/3, 1/6)`
  example computes to the expected value in the new test file.
- Phase C: for a specific independent `prodDist p q`, `mutualInfo = 0` and
  `mutualInfoBits = 0`; `relEntropy` of a hand-picked pair matches the
  analytic value.
- Phase D: pick `α := Fin 2`, `p := (0.3, 0.7)`, `N := 10`, `ε := 0.1`;
  check an explicit element of the typical set and the bounds on
  `|typicalSet|`.
- Phase E: 2-state Markov chain with transition matrix
  `[[0.8, 0.2], [0.4, 0.6]]`, treated as a `FiniteStateSource` special
  case; verify `G N`, `F N` converge to the analytically computed entropy
  rate as `N` grows (check `N = 1, 2, 3, 4`), and check the
  transcription-faithful finite-state-source upgrade of Theorems 3 and 4 on
  a stationary example.

All phases follow the existing documented workflow: `bin/bootstrap-worktree`
for fresh worktrees, `lake build Shannon.Entropy.<Module>` for single-module
iteration, `lake test` for the regression suite, `lake build ShannonBook`
for the companion book.
