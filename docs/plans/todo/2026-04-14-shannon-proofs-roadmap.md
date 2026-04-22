# Shannon Proofs Roadmap

Date: 2026-04-14
Status: Phase A shipped 2026-04-18 on branch `docs/implement-phase-a-verso`; Phase B shipped 2026-04-18 on branch `chore/implement-phase-b`; Phase C shipped 2026-04-19 on branch `formalize/c-information-theoretic-primitives`; Phase D shipped 2026-04-22 on branch `formalize/phase-d-iid-aep-and-typical-sets`; Phase E pending.

## Context

The Lean 4 formalization currently covers Shannon Appendix 2 (uniqueness of
`H = -K Σ pᵢ log pᵢ`) and Section 6 Properties 1–6, all with complete proofs
(no `sorry`, no external axioms). Fidelity to Shannon's Appendix 2 argument
is already very close: the `Apos_mul` / `Apos_pow` / ratio-squeeze chain in
`Shannon/Entropy/Uniform.lean` mirrors Shannon's derivation step by step, and
`Rational.lean` includes Shannon's worked `(1/2, 1/3, 1/6)` tree example.

The paper transcription in `references/shannon1948-transcription.md` declares
a wider target scope:

- Theorem 2 (uniqueness): done
- Properties 1–6: done
- Theorem 3 (AEP): not yet formalized
- Theorem 4 (typical set size): not yet formalized
- Theorems 5–6 (per-symbol entropy `Gₙ`, `Fₙ` convergence): not yet formalized
- Theorem 7 (data processing inequality): not yet formalized

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
- Chapters under `Book/` must not `import Shannon` or any `Shannon.*` module.
  Lake links every transitive C object on the `generate-book` argv, and
  pulling Mathlib through `Shannon` pushes the macOS link command past
  `ARG_MAX` (~1 MB). Chapters that need to render Lean code will use
  `subverso` highlight artifacts instead of direct imports. This applies
  to every later phase and is documented in `AGENTS.md`.

## Phase A: Verso companion book setup

Status: shipped 2026-04-18 on branch `docs/implement-phase-a-verso`. All
seven tasks below were delivered. Rendered output lives under
`_site/html-multi/` rather than `_site/` directly; the `import Shannon`
prohibition added during implementation is recorded as a cross-cutting
design decision above and should be honored by every later phase.

Goal: add a Manual-genre Verso book that grows alongside the Lean
formalization, modeled structurally on the [Lean Reference
Manual](https://github.com/leanprover/reference-manual). The book lives
in-repo as a separate Lake library plus executable pair; each later phase
adds at least one chapter.

Design notes:

- Manual genre, not Blog. Shannon walkthrough wants hierarchical parts and
  chapters, TOC, cross-references from prose into `Shannon.Entropy.*` Lean
  definitions, and a bibliography. Manual supplies these; Blog does not.
- Single `verso` dependency, pinned to `v4.29.0` to match `lean-toolchain`.
  Skip `verso-web-components` (Lean-website styling, not needed), `illuminate`
  (diagramming, not needed for Shannon's prose), and Plausible analytics.
  All three are optional adornments reference-manual chose to add.
- Short namespace `Book`, matching reference-manual's use of the short name
  `Manual` for its lean_lib and root module.

Tasks:

1. Add Verso as a Lake dependency.
   - In `lakefile.toml`, add a `[[require]]` entry for `verso` at
     `https://github.com/leanprover/verso.git` rev `v4.29.0`.
   - Verso publishes a tag per Lean release, so this pinning is stable.
   - Run `lake update` to confirm Mathlib and Verso co-exist at 4.29.0.
     The strength-model repo already uses this combination successfully, so
     failure here would indicate a real problem worth investigating rather
     than a reason to fall back to an alternative toolchain.
   - Record the compatibility check outcome as a one-line comment in
     `lakefile.toml` next to the Verso require.

2. Scaffold the book.
   - New `lean_lib` target `Book` in `lakefile.toml`.
   - New `lean_exe` target `generate-book` with `root = "Main"`.
   - Add `moreLeancArgs = ["-O0"]` at the package level to cut C compile
     time (reference-manual does this; the optimization cost exceeds the
     savings for doc builds).
   - The `Book` library does **not** import `Shannon` or any `Shannon.*`
     module. Lake places every transitive C object on the `generate-book`
     link argv, and pulling Mathlib through `Shannon` pushes the macOS
     command line past `ARG_MAX`. Chapters that need to render Lean code
     use `subverso` highlight artifacts instead of direct imports.
   - Layout:
     - `Main.lean` at repo root: executable entry point; calls
       `manualMain (%doc Book) (config := config)` with `sourceLink` and
       `issueLink` pointing at this repo.
     - `Book.lean` at repo root: root document; opens with
       `#doc (Manual) "Shannon 1948: A Formalization Companion" => ...`
       followed by chapter imports and `{include 0 ...}` splices.
     - `Book/` directory: per-chapter modules, mirroring `Manual/` in
       reference-manual.

3. Initial chapters (Phase A scope).

   Keep Phase A content narrow to prove the pipeline works; defer
   content-heavy chapters to Phase B.

   - `Book/Introduction.lean`: paper overview, fork relationship
     (cboone/shannon-entropy off SamuelSchlesinger's), scope (Appendix 2 and
     Section 6 Properties 1-6 done; Theorems 3-7 planned), reading order,
     `bin/bootstrap-worktree` and `make book` invocations.
   - `Book/Bibliography.lean`: Shannon 1948 with DOI, supporting references
     (Cover and Thomas, MacKay).

   The earlier `Foundations` placeholder is folded into `AxiomaticEntropy` in
   Phase B, to avoid splitting the axiomatic content across phases.

4. Build targets.

   Add to `Makefile`:

   ```makefile
   book: ## Build the companion book HTML
     @test -f .lake/packages/verso/.lake/build/lib/lean/VersoManual.olean || \
       (printf "Verso not bootstrapped. Run bin/bootstrap-worktree first.\n" >&2; exit 1)
     lake build Book
     lake exe generate-book --depth 2 --output _site

   serve: book ## Build and serve the book locally
     uv run python -m http.server 8000 --directory _site/html-multi
   ```

   The two-step invocation (`lake build Book` then `lake exe generate-book`)
   mirrors reference-manual's pattern. `--depth 2` controls TOC granularity
   (Parts and chapters expanded; sections collapsed by default). The
   rendered HTML lands in `_site/html-multi/`; `.gitignore` the `_site/`
   directory.

   Update `bin/bootstrap-worktree` to also run `lake build Book` alongside
   `lake build Shannon` so fresh worktrees are book-ready.

   Document in `README.md` under a new "Companion book" section: `make book`
   renders, `make serve` previews locally. Note that `lake build Book` alone
   is a compile-only check, useful in tight iteration loops.

5. CI integration.
   - Extend `.github/workflows/ci.yml` with a `book` job that runs after
     the existing Lean job succeeds: checkout, install lean-action, run
     `lake build Book`, run `lake exe generate-book --depth 2 --output _site`,
     upload `_site/` as an artifact.
   - Optional follow-up (flagged, not required this phase): GitHub Pages
     deployment from `main` merges. Ship as a separate workflow and a
     separate PR.

6. Testing.
   - `lake build Book` passes as a source-compile check.
   - `lake exe generate-book --depth 2 --output _site` produces a non-empty
     `_site/html-multi/index.html` with per-chapter subdirectories.
   - `make check` still passes end-to-end.
   - Add `ShannonTest/Book.lean` with a single `example` that imports
     `Book` to catch import regressions without duplicating content tests.
   - Update `cspell-words.txt` with any Verso-specific terms surfaced by
     prose (e.g. `Verso`, `manualMain`, `versowebcomponents` if cross-refs
     mention it).

7. Documentation.
   - Update `CLAUDE.md` / `AGENTS.md` module layout section to list `Book/`
     and note the companion-book convention.
   - README "Companion book" section per Task 4.

Files created: `Main.lean`, `Book.lean`, `Book/Introduction.lean`,
`Book/Bibliography.lean`, `ShannonTest/Book.lean`. Files modified:
`lakefile.toml`, `lake-manifest.json`, `README.md`, `Makefile`,
`.github/workflows/ci.yml`, `bin/bootstrap-worktree`, `.gitignore`,
`cspell-words.txt`, `CLAUDE.md`.

## Phase B: Revision, tighten correspondence with Shannon's narrative

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
   `Shannon/Entropy/Joint.lean` asserting that the Lean `condEntropy`
   definition equals Shannon's summation form
   `H_x(y) = -∑ p(i, j) log p_i(j)`. In the transcription, this is the
   defining equation Shannon gives in Property 5 (chain rule), so the
   lemma directly ties the Lean API to that property rather than
   introducing a new side-lemma. Default conditional entropy definition
   stays unchanged.
4. Sync upstream stylistic cleanups. `Properties.lean`, `Rational.lean`,
   `Uniform.lean` differ from upstream in minor tactic choices
   (`push Not` → `push_neg`; `simp only … rw …` → `simpa …`). Bring these
   over in one commit so a future upstream PR has a clean diff.
5. Testing.
   - `ShannonTest/Entropy/Uniform.lean`,
     `ShannonTest/Entropy/Rational.lean`, and
     `ShannonTest/Entropy/Gibbs.lean` were added in the 2026-04-14 test
     backfill; Phase B extends those files and adds the new
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
   - New chapter `Book/AxiomaticEntropy.lean` walks Shannon's Appendix 2
     proof with references into `Shannon/Entropy/{Uniform, Rational, Approx,
     Final}.lean`.
   - New chapter `Book/Properties.lean` walks Section 6 Properties
     1–6 with references into `Shannon/Entropy/{Joint, Properties,
     Gibbs}.lean`.
   - New chapter `Book/Logarithm.lean` discusses the `K` scale
     constant, base choice, and the `entropyBits` API.
   - `Book.lean` (the root document) links the new chapters in order.

Files touched: `Shannon/Entropy/{Uniform, Rational, Approx, Final, Joint,
Properties}.lean`, new `Shannon/Entropy/Bits.lean`, new files in
`ShannonTest/Entropy/`, new files in `Book/`.

## Phase C: Information-theoretic primitives

Goal: complete the primitives layer (mutual information properties,
relative entropy, log-sum inequality, data processing inequality in its
information form, a base-2 binary-entropy helper, and Fano's inequality).
All items are short derivations from Gibbs and existing infrastructure;
they unblock Phase D and round out Section 6.

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
   - Along the way, add `entropyBits_prodDist`:
     `entropyBits (prodDist p q) = entropyBits p + entropyBits q`, a one-line
     consequence of `entropyNat_prodDist` and the
     `entropyBits_eq_entropyNat_div_log_two` bridge. Called out in the Phase
     B branch review (`docs/reviews/2026-04-18-chore-implement-phase-b.md`)
     as a natural companion lemma to land with Phase C's first base-2
     statements. Lives in `Shannon/Entropy/Bits.lean`, not `MutualInfo.lean`.
2. New module `Shannon/Entropy/RelativeEntropy.lean`. Define a support
   predicate `Supports q p := ∀ a, 0 < p a → 0 < q a`. Define
   `relEntropy (p q : ProbDist α) : ℝ := ∑ a, p a * log (p a / q a)` (KL
   divergence `D(p‖q)`) as the finite-valued expression used on
   support-covered pairs, and a `relEntropyBits` variant. State the standard
   KL theorems under `Supports q p`. Prove:
   - `relEntropy_nonneg (hsupp : Supports q p)`
   - `relEntropy_eq_zero_iff (hsupp : Supports q p)`:
     `D(p‖q) = 0 ↔ p = q` pointwise
   - Reframe `gibbs_inequality` to additionally state `0 ≤ relEntropy p q`
     under the same support hypothesis (keep existing form for backward
     compatibility).
3. Log-sum inequality. In `RelativeEntropy.lean`: for nonneg sequences
   `aᵢ, bᵢ` with `∑ aᵢ = A`, `∑ bᵢ = B`, and support condition
   `aᵢ > 0 → bᵢ > 0`,
   `∑ aᵢ · log (aᵢ/bᵢ) ≥ A · log (A/B)`.
   State it in a form that also handles the degenerate `A = 0` case, since
   the Phase C DPI proof applies log-sum fiberwise and some fibers can have
   zero total mass.
4. Data processing inequality (information form). In `MutualInfo.lean`:
   given a kernel `W : α → ProbDist γ` and a joint `(X, Y)`, the Markov
   chain `X → Y → Z := (W (Y ·))` satisfies `I(X;Z) ≤ I(X;Y)`. (Phase E
   covers Shannon's transducer form, which is Theorem 7.) The proof should
   use the zero-total-friendly log-sum statement above rather than baking in
   positivity assumptions that fail on vanishing fibers.
5. Binary entropy helper. New module `Shannon/Entropy/BinaryEntropy.lean`.
   Define `binEntropyBits : ℝ → ℝ` by dividing Mathlib's `Real.binEntropy`
   by `Real.log 2`, and expose the small base-2 lemma set Phase C needs
   (`0`, `1`, `1/2`, symmetry, nonnegativity, `≤ 1`, continuity, endpoint
   characterization).
6. Fano's inequality. New module `Shannon/Entropy/Fano.lean` proving
   `H(X|Y) ≤ h₂(Pₑ) + Pₑ · log(|X| − 1)` where `Pₑ` is the error
   probability of an estimator. State and prove it in base 2 via
   `entropyBits`, `condEntropyBits`, and `binEntropyBits`. Budget the proof
   against nested-pair encodings of the `(E, X, Y)` construction and split a
   small helper module only if that bookkeeping outgrows a compact local
   section. The landed implementation uses `Shannon/Entropy/FanoHelpers.lean`
   to package the conditional-row decomposition and the one-row `q`-ary
   entropy bound at a distinguished decoder output.
7. Testing.
   - New test files `ShannonTest/Entropy/MutualInfo.lean`,
     `ShannonTest/Entropy/RelativeEntropy.lean`,
     `ShannonTest/Entropy/BinaryEntropy.lean`, and
     `ShannonTest/Entropy/Fano.lean`.
   - Cases: `mutualInfo_nonneg` on an independent `prodDist` gives exactly
   zero; `mutualInfo_self` on a two-point uniform gives `1` bit;
   `relEntropy` of a support-covering pair such as `(1/2, 1/2)` vs.
   `(1/4, 3/4)` matches the closed-form value; `log_sum_inequality`
   equality case when `aᵢ = bᵢ`; `binEntropyBits (1/2) = 1`; Fano's inequality numerically
   sanity-checked on a two-symbol alphabet with a known error
   probability.
   - `make check` green.
8. Verso book update.
   - New chapter `Book/MutualInformation.lean` covers `I(X;Y)` and the
     identities proved in this phase.
   - New chapter `Book/RelativeEntropy.lean` covers `D(p‖q)`, the
     log-sum inequality, and the information-form DPI.
   - New chapter `Book/FanoInequality.lean` discusses the estimator
     setting and points forward to Phase E.
   - Chapter ordering in `Book.lean` updated.

Files created: `Shannon/Entropy/MutualInfo.lean`,
`Shannon/Entropy/RelativeEntropy.lean`,
`Shannon/Entropy/BinaryEntropy.lean`, `Shannon/Entropy/FanoHelpers.lean`,
`Shannon/Entropy/Fano.lean`,
matching test files, new Book chapters. Facade `Shannon.Entropy.lean`
updated.

## Phase D: I.i.d. AEP and typical sets (Theorems 3–4 special case)

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
     The support restriction keeps `Real.logb 2 (p (x i))` finite on the
     set without needing a defaulted value for zero-probability symbols;
     for `p` with full support the restriction is vacuous.
   - Per-element bounds
     `2^(-N·(entropyBits p + ε)) ≤ iidDist p N x ≤ 2^(-N·(entropyBits p - ε))`
     for `x` typical (directly in `2^…`, no natural-log detour).
3. Theorem 3 (AEP). `aep_iid`:
   `∀ ε δ > 0, ∃ N₀, ∀ N ≥ N₀,
      ∑ x ∈ typicalSet p N ε, iidDist p N x ≥ 1 − δ`.
   Proof route: apply a Chebyshev bound to the random variable
   `Yᵢ := -Real.logb 2 (p (Xᵢ))`. Mean is `entropyBits p`; the sample mean
   must satisfy a vanishing variance bound of the form `Var(Y̅_N) ≤ C / N`
   for an explicit finite constant `C` depending only on `p` (for example
   `C := ∑ p a · (logProbBits p a - entropyBits p)^2`). Prefer a direct
   Chebyshev argument to invoking Mathlib's measure-theoretic LLN.
4. Theorem 4 (typical set size).
   - `typicalSet_card_lower`:
      `(1 − δ) · 2^(N · (entropyBits p − ε)) ≤ |typicalSet p N ε|` for
      `N` large enough
   - `typicalSet_card_upper`:
      `|typicalSet p N ε| ≤ 2^(N · (entropyBits p + ε))`
   - Add `minCover` for interior thresholds `0 < q < 1`, for example as
      `minCover p N q hq₀ hq₁ := min {|S| : S ⊆ univ ∧ iidDist p N S ≥ q}`,
      and derive `Tendsto (fun N => (Real.logb 2 (minCover p N q hq₀ hq₁)) / N)`
      `atTop (𝓝 (entropyBits p))`.
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
   - New chapter `Book/IIDAndAEP.lean` covers the i.i.d. product
     construction, the typical set, and the i.i.d. special case of
     Theorems 3 and 4.
   - Inline numerical example: walk through the `p = (0.3, 0.7)`, `N = 10`
     case with explicit probabilities, showing the typical set bounds.
   - Cross-link to `Book/MutualInformation.lean` for the role of
     information rate.

Files created: `Shannon/Entropy/IID.lean`, `Shannon/Entropy/AEP.lean`,
matching tests, new Book chapter.

Resolved during execution: Mathlib's native `Real.logb` and `Real.rpow`
lemmas were sufficient for Phase D. No wrapper namespace was needed.

## Phase E: Finite-state statistical sources and entropy rate (Theorems 3–7)

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
     hidden-state chain. Plan on an elementary argument via the simplex
     (Brouwer fixed point on the compact convex set of distributions, or a
     direct averaged-iterates construction) as the default route; treat
     Mathlib's stochastic-matrix spectral results as an optional
     simplification only if they are available and stable at the pinned
     Lean version.
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
   - Update the transcription cross-references so the unqualified Theorems
     3 and 4 entries are only marked complete once this phase lands. At the
     end of Phase D, add interim cross-references such as
     "Theorem 3 (i.i.d. case): `aep_iid` in `Shannon/Entropy/AEP.lean`"
     and a matching entry for Theorem 4, so partial progress is visible in
     the transcription between phases.
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
   - New chapter `Book/FiniteStateSources.lean` on Shannon's
     state-space source model, stationary distributions, and product-state
     constructions.
   - Update `Book/IIDAndAEP.lean` to mark Phase D as the i.i.d. warm-up
     special case.
   - New chapter `Book/FiniteStateAEP.lean` on the
     transcription-faithful finite-state-source versions of Theorems 3
     and 4.
   - New chapter `Book/PerSymbolEntropy.lean` on `G_N`, `F_N`,
     Theorems 5 and 6.
   - New chapter `Book/DataProcessing.lean` on the transducer form of
     Theorem 7; tie back to the information-form DPI from Phase C.
   - Final chapter `Book/Conclusion.lean` summarizes scope covered
     and explicitly lists Phase F items as future work.

Files created: `Shannon/Entropy/FiniteStateSource.lean`,
`Shannon/Entropy/EntropyRate.lean`, `Shannon/Entropy/Transducer.lean`,
matching tests, new Book chapters.

## Phase F: Out of scope

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

- `Shannon/Entropy/Joint.lean`: add `condEntropy_eq_shannon_form`
- `Shannon/Entropy/Gibbs.lean`: cross-reference with `relEntropy`
- `Shannon/Entropy/Final.lean`: add `entropyBits`-flavored corollaries
- `Shannon/Entropy.lean`: facade imports for every new module
- `Shannon.lean`: top-level re-export
- `lakefile.toml`, `lake-manifest.json`: Verso dependency pinned at
  `v4.29.0`; new `Book` lean_lib and `generate-book` lean_exe
- `Makefile`: `make book` and `make serve` targets
- `.github/workflows/ci.yml`: Verso build job
- `bin/bootstrap-worktree`: add `lake build Book` after Shannon build
- `README.md`: companion book section, updated scope
- `references/shannon1948-transcription.md`: append cross-references for
  each newly formalized theorem as it lands. Note: Phase B's
  `condEntropy_eq_shannon_form` corresponds to the existing Property 5
  entry (chain rule), not a new one; only genuinely new theorems (Phase
  C's mutual-info / KL lemmas, Phase D's i.i.d. AEP, Phase E's
  finite-state results) warrant new cross-reference entries.
- `cspell-words.txt`: Verso / information-theory vocabulary

New, to create:

- Phase A: `Main.lean`, `Book.lean`, `Book/{Introduction,
  Bibliography}.lean`, `ShannonTest/Book.lean`
- Phase B: `Shannon/Entropy/Bits.lean`,
  `ShannonTest/Entropy/{Uniform, Rational, Gibbs, Bits}.lean`,
  `Book/{AxiomaticEntropy, Properties, Logarithm}.lean`
- Phase C: `Shannon/Entropy/{MutualInfo, RelativeEntropy, BinaryEntropy,
  Fano}.lean`, `ShannonTest/Entropy/{MutualInfo, RelativeEntropy,
  BinaryEntropy, Fano}.lean`,
  `Book/{MutualInformation, RelativeEntropy, FanoInequality}.lean`
- Phase D: `Shannon/Entropy/{IID, AEP}.lean`,
  `ShannonTest/Entropy/{IID, AEP}.lean`,
  `Book/IIDAndAEP.lean`
- Phase E: `Shannon/Entropy/{FiniteStateSource, EntropyRate, Transducer}.lean`,
  `ShannonTest/Entropy/{FiniteStateSource, EntropyRate, Transducer}.lean`,
  `Book/{FiniteStateSources, FiniteStateAEP, PerSymbolEntropy,
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
- `lake build Book` passes starting in Phase A as a compile-only
  check.
- `make book` passes starting in Phase A and produces non-empty rendered
  output.
- Every new public definition or theorem has a corresponding entry in
  `ShannonTest/Entropy/…` exercising a concrete instance.
- Each phase updates the `Formalization Cross-References` section in
  `references/shannon1948-transcription.md` with the new theorem names,
  and adds the corresponding Book chapter.

Per-phase sanity checks (a minimal tripwire subset, not a restatement of
each phase's full test coverage; pick these as the quick smoke checks
when iterating):

- Phase A: `lake build Book` succeeds as a source-compile check;
  `make book` generates non-empty rendered output under `_site/`; the
  book's table of contents lists the Introduction and Bibliography
  chapters (`AxiomaticEntropy` lands in Phase B).
- Phase B: `entropyBits (uniformPNat 2) = 1`;
  `entropyBits (uniformPNat 4) = 2`; Shannon's worked `(1/2, 1/3, 1/6)`
  example computes to the expected value in the new test file.
- Phase C: for a specific independent `prodDist p q`, `mutualInfo = 0` and
  `mutualInfoBits = 0`; `relEntropy` of a support-covering hand-picked pair
  matches the analytic value; `binEntropyBits (1/2) = 1`; and the
  two-symbol Fano sanity check closes with the expected error probability.
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
iteration, `lake test` for the regression suite, `lake build Book`
for book-source compile checks, and `make book` for companion-book
rendering.
