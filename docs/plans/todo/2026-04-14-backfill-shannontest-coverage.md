# 2026-04-14 Backfill ShannonTest coverage

## Context

`ShannonTest/` currently mirrors only three of the nine `Shannon/` library modules:

| Library module | Lines | Test file | Status |
|---|---|---|---|
| `Shannon/Entropy/Core.lean` | 170 | `ShannonTest/Entropy/Core.lean` | present |
| `Shannon/Entropy/Final.lean` | 105 | `ShannonTest/Entropy/Final.lean` | present |
| `Shannon/Entropy/Properties.lean` | 287 | `ShannonTest/Entropy/Properties.lean` | present |
| `Shannon/Entropy/Uniform.lean` | 381 | — | **missing** |
| `Shannon/Entropy/Rational.lean` | 239 | — | **missing** |
| `Shannon/Entropy/Approx.lean` | 299 | — | **missing** |
| `Shannon/Entropy/Joint.lean` | 187 | — | **missing** |
| `Shannon/Entropy/Gibbs.lean` | 116 | — | **missing** |
| `Shannon/Entropy/Converse.lean` | 104 | — | **missing** |

Six modules totaling about 1,300 lines of proof code have no test file. AGENTS.md states that "`ShannonTest/` mirrors the Shannon library's public API with `example`-based tests" and that "when adding, renaming, or removing public definitions or theorems, update the corresponding test file in the same change so `lake test` continues to pass" -- a rule that presupposes those test files exist. Silent regressions in the uncovered modules will not be caught by `lake test` today.

Goal: create the six missing test files so the mirror rule is structurally satisfied, and populate each with enough `example` statements to exercise the module's public API at roughly the density of the existing test files (about 30-40% of public declarations touched, with every headline result covered). This is not an exhaustive test pass; it is a smoke-test baseline that makes future API changes loud.

## Existing convention (to match)

The three existing test files share a tight style:

- **Imports:** each test file imports the corresponding library module and nothing else (e.g. `import Shannon.Entropy.Core`).
- **Namespace:** each test file does `open Shannon` (or enters the namespace) so declarations can be referenced without qualification.
- **Test form:** `example` statements exclusively. No `theorem`, `lemma`, or `#check`. Each example is a tactic or term proof that the declaration exists, has the expected shape, and evaluates correctly on at least one concrete instance.
- **Grouping:** examples are ordered to roughly follow the library file's section headings; a short comment or sectioning header precedes each group when the file covers multiple concerns.
- **Coverage density:** about 5-7 examples per test file for 15-20 public declarations. Existence and basic type signature is the common bar; computational instances (e.g. `entropyNat (uniformPNat 2) = log 2`) are added when the library exports a closed-form result worth pinning.

The new test files should match this style exactly. Do not introduce a richer test framework, property-based testing, or coverage metrics. Do not reprove library theorems; call them.

## Per-module plan

For each missing test file, the plan lists (a) headline results that must be covered and (b) a reasonable selection of support lemmas to bring total coverage to the existing-file density. Exact example count is a guide, not a contract; match the library module's phase and scope.

Each test file lives at `ShannonTest/Entropy/<Module>.lean`, imports `Shannon.Entropy.<Module>`, opens `Shannon`, and follows the existing file template.

### `ShannonTest/Entropy/Uniform.lean` (largest; roughly 6-8 examples)

Library exports 20 public declarations across the equiprobable-characterization phase.

- **Headline results (must cover):**
  - `Apos_mul`: multiplicative identity on uniform-entropy scale across products.
  - `Apos_eq_K_mul_log`: core logarithmic characterization.
  - `K_pos`: positivity of the scale constant.
  - `Apos_pow`: power expansion for equiprobable entropy.
- **Supporting examples:**
  - `Apos_one_zero`: uniform entropy at cardinality 1 vanishes.
  - `Apos_pos_of_one_lt`: strict positivity for sizes greater than 1.
  - `A_monotone` or `Apos_monotone`: monotonicity in alphabet size (pick the form closer to existing tests).
  - Optionally `Apos_eq_K_mul_logb` to pin the base-parametric variant.

### `ShannonTest/Entropy/Rational.lean` (5-6 examples)

Library exports 11 public declarations for the rational case, including a worked (1/2, 1/3, 1/6) example.

- **Headline results:**
  - `entropyNat_of_rational_counts`: main rational-entropy formula.
  - `worked_grouping_identity`: worked-example decomposition identity.
  - `grouping_on_rational_counts`: grouping axiom instantiated on rationals.
- **Supporting examples:**
  - `relabel_compose_rational_eq_uniform`: relabel invariance on rational composition.
  - `workedCompose_masses`: pin the exact masses of the worked-example composed distribution.

### `ShannonTest/Entropy/Approx.lean` (5-6 examples)

Library exports 12 public declarations for the floor-count approximant phase.

- **Headline results:**
  - `tendsto_approxProb`: uniform convergence of approximants (the phase 3 payoff).
  - `approxProb_error_bound`: explicit pointwise error bound.
  - `entropyNat_approxProb`: rational-entropy formula applied to approximants.
- **Supporting examples:**
  - `approxCount_pos`, `approxTotal_pos`: positivity smoke.
  - `approxProb_apply`: evaluation formula on a concrete input.

### `ShannonTest/Entropy/Joint.lean` (5-7 examples)

Library exports 12 public declarations for joint distributions, marginals, conditional entropy, mutual information.

- **Headline results:**
  - `chain_rule`: `H(X,Y) = H(X) + H_X(Y)`.
  - `entropyNat_prodDist`: additivity for independent distributions.
  - `marginalFst_prodDist`, `marginalSnd_prodDist`: marginals recover the factors of a product.
- **Supporting examples:**
  - `IsIndependent` on a concrete product, to pin the predicate shape.
  - `condEntropy` applied to a concrete distribution (e.g. a two-point joint).
  - `mutualInfo` applied to the same concrete distribution.

### `ShannonTest/Entropy/Gibbs.lean` (4-5 examples)

Library exports 5 public declarations; this is the analytical bridge module. Aim for near-full surface coverage.

- **Headline results:**
  - `gibbs_inequality`: KL inequality.
  - `entropyNat_nonneg`: corollary non-negativity.
  - `entropyNat_le_log_card`: uniform-maximum upper bound.
- **Supporting examples:**
  - `entropyNat_eq_sum_negMulLog`: bridge to Mathlib's `negMulLog`.
  - `entropyNat_uniformPNat`: uniform entropy equals `log n` on a concrete cardinality.

### `ShannonTest/Entropy/Converse.lean` (3-4 examples)

Library exports 4 public declarations; all three non-main results feed the main theorem. Aim for near-full surface coverage.

- **Headline results:**
  - `entropyNat_shannonAxioms`: main theorem asserting `entropyNat` satisfies the axioms.
- **Supporting examples:**
  - `entropyNat_relabelInvariant`: relabel invariance.
  - `entropyNat_uniformMonotone`: strict monotonicity on uniforms.
  - `entropyNat_grouping`: two-stage grouping identity.

## Critical files to modify

Six new files to create:

- `ShannonTest/Entropy/Uniform.lean`
- `ShannonTest/Entropy/Rational.lean`
- `ShannonTest/Entropy/Approx.lean`
- `ShannonTest/Entropy/Joint.lean`
- `ShannonTest/Entropy/Gibbs.lean`
- `ShannonTest/Entropy/Converse.lean`

One existing file to update:

- `ShannonTest/Entropy.lean` -- add six new `import ShannonTest.Entropy.<Module>` lines so `lake test` picks them up.

Reference files to match in style:

- `ShannonTest/Entropy/Core.lean`
- `ShannonTest/Entropy/Final.lean`
- `ShannonTest/Entropy/Properties.lean`

Reference files for public-API surface (the things being tested):

- `Shannon/Entropy/{Uniform,Rational,Approx,Joint,Gibbs,Converse}.lean`

## Execution order

Build in ascending size order so early wins keep momentum and the long modules benefit from any template refinements:

1. `Converse.lean` (4 decls, smallest; also high-leverage since it holds the main theorem)
2. `Gibbs.lean` (5 decls, self-contained bridge)
3. `Joint.lean` (12 decls, but straightforward mirrors of product/marginal structure)
4. `Approx.lean` (12 decls; convergence tests need concrete sequences)
5. `Rational.lean` (11 decls; worked-example arithmetic is the tricky part)
6. `Uniform.lean` (20 decls, largest)

After each new file is created, add its import to `ShannonTest/Entropy.lean` in the same change and run `lake test` immediately; do not batch file creation without verifying each one compiles.

Each file is independently committable. Use conventional-commits `test: add ShannonTest/Entropy/<Module>.lean smoke coverage` per file, or a single `test: backfill ShannonTest coverage for six modules` commit if the run is uninterrupted.

## Verification

After each new test file:

1. `lake test` passes without errors or warnings.
2. `make lean-lint` passes (no new linter hits against the test file).
3. `make check` passes end-to-end (markdown + spelling + lean-lint + build + test).
4. The new file compiles in isolation: `lake env lean ShannonTest/Entropy/<Module>.lean` succeeds.
5. Spot-check: remove or rename a public declaration in the corresponding library module, rebuild, and confirm the test file now fails. Revert. This proves the test actually exercises the declaration rather than merely importing it.

Full-run after all six files:

- `lake test` runs all nine test modules (three existing + six new).
- `make check` passes on a clean worktree.
- `git diff --stat ShannonTest/` shows roughly 30-40 new lines per file, matching existing-file density; large deviations indicate either over- or under-testing.

## Out of scope (explicit)

- Exhaustive coverage of every public declaration. The target is headline + a few support lemmas per module, matching existing-file density (~35%).
- Property-based or randomized tests. The existing convention is concrete `example` statements; do not introduce new testing infrastructure.
- Internal (`private`) declarations. Tests only touch the public surface.
- Library refactors. If a library module's public API is awkward to test, note it and keep the test minimal; a separate issue can track the refactor.
- Upstream parity. `SamuelSchlesinger/shannon-1948-formalization` may or may not have tests of its own; this plan is about satisfying shannon-entropy's own mirror rule, not about aligning with upstream. If upstream later adds tests, reconcile then.
- The hardwrapped-docstrings cleanup. That is tracked separately; this plan does not edit library files.

## Follow-up (not required by this plan)

If the mirror rule is worth enforcing mechanically, a follow-up issue can add a small check (a shell script or `lake exe` program) that fails when a file exists under `Shannon/Entropy/` without a sibling under `ShannonTest/Entropy/`. That would prevent the gap from reopening silently. Out of scope here; worth filing.
