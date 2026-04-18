import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Axiomatic Entropy" =>
%%%
tag := "axiomatic-entropy"
%%%

This chapter walks through Shannon's characterization of the entropy functional on finite alphabets, the content of Appendix 2 of _A Mathematical Theory of Communication_.
Shannon postulates that any "measure of how much choice is involved in the selection of the event" must satisfy three structural axioms; he then shows those axioms force the functional to be `-K ∑ p_i log p_i` for some positive constant `K`.
The Lean development mirrors Shannon's three-phase argument in `Shannon/Entropy/Uniform.lean`, `Shannon/Entropy/Rational.lean`, `Shannon/Entropy/Approx.lean`, and `Shannon/Entropy/Final.lean`.

# The Three Axioms

Shannon's three assumptions describe a functional `H(p_1, ..., p_n)` of finite probability distributions:

- *Continuity.* `H` is continuous in the probabilities `p_i`.
- *Monotonicity on uniforms.* If all outcomes are equally likely, `A(n) := H(1/n, ..., 1/n)` should be a monotonically increasing function of `n` (more options = more uncertainty).
- *Grouping (recursivity).* A two-stage choice composes additively: if we decompose a choice of one of `n` outcomes into a first choice of a group and then a choice within the group, the total uncertainty is the uncertainty of the group choice plus the group-weighted average of the within-group uncertainties.

In the Lean development these are bundled as `ShannonEntropyAxioms` in `Shannon/Entropy/Core.lean`, with fields `continuous`, `uniformMonotone`, `relabelInvariant` (a formal "names of outcomes do not matter" clause that Shannon treats implicitly), and `grouping`.

# Equiprobable Case

The first phase restricts attention to uniform distributions and writes `A(n)` for the uncertainty at alphabet size `n`.
Shannon observes that a uniform on `s^n` outcomes decomposes by grouping into `n` sequential uniform choices of size `s`, so `A(s^n) = n · A(s)`.
The Lean counterparts are `Apos_mul` (additivity on alphabet-size products) and `Apos_pow` (the `n`-fold iterate) in `Shannon/Entropy/Uniform.lean`.

Shannon then pins down `A` by a ratio-squeeze: for any `s, t > 1` and any `n`, pick the unique `m` with `s^m ≤ t^n < s^(m+1)`; monotonicity of `A` on uniform alphabet sizes forces `A(t)/A(s)` within `1/n` of `log t / log s`, and letting `n → ∞` gives `A(t)/A(s) = log_s t`.
Concretely, both `A(t)/A(s)` and `log_s t` sit in the same closed interval `[m/n, (m+1)/n]` of width `1/n`, which is what delivers the `1/n` bound and pins the ratio in the limit.
The Lean counterparts are `Apos_ratio_logb_close` feeding `Apos_ratio_eq_logb`, which combine in `Apos_eq_K_mul_log` to give `Apos H n = K H * log n` with `K H := Apos H 2 / log 2`.

# Rational Case

The second phase lifts the formula to any rational distribution `p_i = n_i / N`.
Shannon refines a uniform on `N` outcomes into `|α|` blocks of sizes `n_1, ..., n_{|α|}`, so that picking one of the `N` outcomes is the two-stage choice of picking a block with probability `p_i` and then picking uniformly within the block.
Applying the grouping axiom, relabel invariance, and the Phase 1 logarithmic formula `A(k) = K log k` rearranges into `H p = -K ∑ p_i log p_i` for every rational `p`.

The Lean counterparts are `grouping_on_rational_counts` (the rearrangement) feeding `entropyNat_of_rational_counts` in `Shannon/Entropy/Rational.lean`.
Shannon motivates the construction with a `(1/2, 1/3, 1/6)` tree: first a fair coin for `{true, false}`, then a `(2/3, 1/3)` split on the `false` branch.
The Lean counterparts are `workedP`, `workedQ`, `workedCompose`, and `worked_grouping_identity`.

# Continuity Extension

The third phase uses density of the rationals in the probability simplex.
Any real-probability `p` is the limit of rational approximants `p^(N)` with denominator near `N`; the continuity axiom on `H` and the elementary continuity of `-∑ p_i log p_i` lift the rational formula to all distributions.

The Lean counterparts are `approxProb p N` (built from floor-count masses) and `tendsto_approxProb p` in `Shannon/Entropy/Approx.lean`, together with the continuity bridge `continuous_entropyNat` in `Shannon/Entropy/Uniform.lean`.

# Theorem 2

Combining the three phases gives Shannon's *Theorem 2*: every functional `H` satisfying the axioms equals `-K ∑ p_i log p_i` for some positive `K`.
The Lean statement is `entropyNat_unique` in `Shannon/Entropy/Final.lean`; its base-parametric restatement is `entropyBase_unique`, which makes the constant's dependence on the logarithm base explicit.
The transcription entry for Theorem 2 lives in `references/shannon1948-transcription.md` under the `## Formalization Cross-References` section.
