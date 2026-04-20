# A Mathematical Theory of Communication

> [!NOTE]
> This is a fork of [SamuelSchlesinger/shannon-1948-formalization](https://github.com/SamuelSchlesinger/shannon-1948-formalization), in which I'm expanding the formalization to cover the entirety of [Shannon's paper](./references/shannon1948.pdf).

This repository is a Lean 4 formalization of Shannon's finite-alphabet entropy theory from Shannon (1948). The completed core covers Appendix 2's characterization theorem, the converse showing that Shannon entropy satisfies the axioms, and the Section 6 entropy properties built on top of that foundation.

The project also includes a base-2 public API, `entropyBits`, and a Verso companion book, `Shannon 1948: A Formalization Companion`. The active roadmap extends the fork toward Shannon's Theorems 3 through 7 for finite-state sources. Continuous / differential entropy, channel capacity, and the noisy-channel coding theorem remain out of scope for now.

## Main Result

- For any uncertainty functional `H` satisfying the Shannon-style axiom bundle (continuity, strict monotonicity on uniform distributions, grouping, and relabel invariance), there is a positive constant `K` such that `H(p) = -K * Σ p_i log p_i`.
- Equivalently, for any base `b > 1`, there is `Kb > 0` such that `H(p) = -Kb * Σ p_i log_b p_i`.

## Project Status

### Done Today

- Appendix 2 uniqueness theorem in `Shannon/Entropy/Final.lean`.
- Converse theorem `entropyNat_shannonAxioms` in `Shannon/Entropy/Converse.lean`.
- Section 6 properties, including deterministic iff zero entropy, uniform iff maximal entropy, subadditivity, Schur-concavity, conditioning reduces entropy, conditional-entropy nonnegativity, chain rule, and product additivity.
- Base-2 public API in `Shannon/Entropy/Bits.lean`, where `entropyBits` is the primary public entropy API.
- Companion book infrastructure and current chapters under `Book/`.

### Planned Next

- Shannon Theorems 3 and 4, first in the i.i.d. setting, then in the finite-state-source setting described in the roadmap.
- Theorems 5 through 7, including entropy rates and data processing in Shannon's source model.
- Additional companion-book chapters that track the formalization phase by phase.

### Out of Scope

- Continuous / differential entropy.
- Channel capacity and the noisy-channel coding theorem.
- A full formalization of every part of Shannon's 1948 paper.

## Repository Surfaces

- `Shannon/`: Lean library modules.
- `ShannonTest/`: `example`-based regression tests that mirror the public API.
- `Book/`, `Book.lean`, `Main.lean`: Verso companion book sources and renderer.
- `references/`: the bundled Shannon paper and related study materials.

## Imports and Entry Points

- `Shannon.lean`: project entrypoint.
- `Shannon/Entropy.lean`: facade import for the full entropy development.
- `ShannonTest/Entropy.lean`: aggregate import for the entropy test suite.

## Representative Results

- `entropyNat_unique` and `entropyBase_unique` in `Shannon/Entropy/Final.lean`: Appendix 2 characterization in natural-log and arbitrary-base form.
- `entropyNat_shannonAxioms` in `Shannon/Entropy/Converse.lean`: the converse direction.
- `entropyBits`, `entropyBits_eq_entropyNat_div_log_two`, and `entropyBits_unique` in `Shannon/Entropy/Bits.lean`: the base-2 public API and uniqueness restatement.
- `chain_rule` and `entropyNat_prodDist` in `Shannon/Entropy/Joint.lean`: chain rule and product additivity.
- `entropyNat_eq_zero_iff`, `entropyNat_eq_log_card_iff`, `entropyNat_joint_le_add`, `condEntropy_le_entropyNat`, `condEntropy_nonneg`, and `entropyNat_doublyStochastic_le` in `Shannon/Entropy/Properties.lean`: core Section 6 properties.

## Reading Paths

1. Proof path: `Shannon/Entropy/Core.lean -> Uniform.lean -> Rational.lean -> Approx.lean -> Final.lean`.
2. API path: `Shannon/Entropy/Bits.lean -> Joint.lean -> Properties.lean -> Converse.lean`.
3. Book path: `Book/Introduction.lean -> Book/AxiomaticEntropy.lean -> Book/Properties.lean -> Book/Logarithm.lean`.

For a worked Shannon-style grouping example, see `worked_grouping_identity` and `workedCompose_masses` in `Shannon/Entropy/Rational.lean`.

## Build and Verify

In every fresh clone or worktree, start with:

```bash
bin/bootstrap-worktree
```

This step is mandatory. It runs `lake update`, downloads Mathlib's prebuilt artifacts, and builds both the `Shannon` library and the `Book` library.

Common commands:

```bash
lake build Shannon
lake build Book
lake test
lake lint
make check
make book
make serve
```

- `lake build Book` is a compile-only check for the companion book sources.
- `make book` renders the HTML book into `./_site/html-multi/`.
- `make serve` builds the book and serves it locally at `http://localhost:8000/`.
- `make check` runs markdown lint, spelling, Lean lint, build, and tests.

CI lives in `.github/workflows/ci.yml`.

## Companion Book

The repository includes a Verso companion book, `Shannon 1948: A Formalization Companion`, that grows alongside the Lean development.

The current book includes an introduction, a chapter on the axiomatic entropy characterization, a chapter on the Section 6 properties, a chapter on the logarithm law and base choice, and a bibliography.

Book chapters must not `import Shannon` or any `Shannon.*` module directly. The `generate-book` executable links every transitive C object on its argv, and on macOS that can push the link command past `ARG_MAX`. Chapters that need rendered Lean snippets should use highlight artifacts rather than a direct import.

## Notes on Axioms

Shannon's symmetry principle ("depends only on probabilities, not labels") is represented explicitly as `ShannonEntropyAxioms.relabelInvariant`.

This makes permutation and relabeling steps explicit in Lean proofs.

## AI Statement

This formalization is being completed with substantial assistance from Opus 4.6 + 4.7 and GPT 5.4, through [`claude`](https://claude.com/claude-code) and [`opencode`](https://opencode.ai), and [GitHub Copilot](https://github.com/features/copilot).

## Reference

- Claude E. Shannon, _A Mathematical Theory of Communication_ (1948).
  The repository includes `references/shannon1948.pdf` for study context.

## License

[The original paper](./references/shannon1948.pdf), _A Mathematical Theory of Communication_, is copyright 1948 Claude Shannon.

This formalization project is a fork of [SamuelSchlesinger/shannon-1948-formalization](https://github.com/SamuelSchlesinger/shannon-1948-formalization), copyright 2026 Samuel Schlesinger, licensed under [the MIT license](./LICENSES/MIT.txt).

Modifications and additions are copyright 2026 Christopher Boone. Newly added Lean code is licensed under [Apache 2.0](./LICENSES/Apache-2.0.txt); Lean code from the forked project is still under [MIT](./LICENSES/MIT.txt); substantially modified Lean code is dual licensed under [MIT](./LICENSES/MIT.txt) and [Apache 2.0](./LICENSES/Apache-2.0.txt). Prose and mathematical exposition are licensed under [CC BY 4.0](./LICENSES/CC-BY-4.0.txt).

See `NOTICE`, `LICENSES/`, and per-file SPDX metadata for the file-level provenance and license breakdown.
