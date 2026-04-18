import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Properties of Entropy" =>
%%%
tag := "properties-of-entropy"
%%%

This chapter walks through the six properties of entropy Shannon lists in Section 6 of _A Mathematical Theory of Communication_ (pp. 11-12).
These are consequences of the entropy formula `H = -K ∑ p_i log p_i` established in the previous chapter.
The analytical workhorse is the *Gibbs inequality* (`∑ p_i log(q_i / p_i) ≤ 0` when `q` covers the support of `p`), proved in `Shannon/Entropy/Gibbs.lean` from `log x ≤ x - 1`.

# Property 1: Nonnegativity

Shannon states that `H ≥ 0`, with equality exactly when one outcome has probability one and all others are zero.
The Lean statement is `entropyNat_eq_zero_iff` in `Shannon/Entropy/Properties.lean`: `entropyNat p = 0 ↔ IsDeterministic p`.
The forward direction expresses `entropyNat` as a sum of nonnegative `Real.negMulLog p_i` terms and observes that each term vanishes only at `p_i ∈ {0, 1}`; combined with `∑ p_i = 1`, exactly one coordinate is `1`.
The nonnegativity bound itself is `entropyNat_nonneg` in `Shannon/Entropy/Gibbs.lean`.

# Property 2: Maximum at Uniformity

Shannon states that `H` attains its maximum at the uniform distribution, where `H = log n`.
The Lean statement is `entropyNat_eq_log_card_iff` in `Shannon/Entropy/Properties.lean`: `entropyNat p = log |α| ↔ ∀ a, p a = 1 / |α|`.
The proof uses strict concavity of `Real.negMulLog` (strict Jensen): any deviation from uniformity strictly decreases the sum, so equality forces the uniform.
The upper bound itself (without the equality characterization) is `entropyNat_le_log_card` in `Shannon/Entropy/Gibbs.lean`, obtained by applying the Gibbs inequality against the uniform `q`.

# Property 3: Subadditivity

Shannon states that for a joint distribution `p(x, y)`, `H(X, Y) ≤ H(X) + H(Y)`, with equality when `X` and `Y` are independent.
The Lean statement is `entropyNat_joint_le_add` in `Shannon/Entropy/Properties.lean`.
The proof applies the Gibbs inequality with `q = prodDist (marginalFst p) (marginalSnd p)`, the product of marginals; the Gibbs sum telescopes to `H(X, Y) - H(X) - H(Y) ≤ 0`.
The independent-case equality is witnessed by `entropyNat_prodDist` in `Shannon/Entropy/Joint.lean` (`H(X × Y) = H(X) + H(Y)` when `p = prodDist p_X p_Y`).

# Property 4: Schur-Concavity

Shannon states that averaging two probabilities decreases uncertainty: if `p'_i = ∑ A_{ij} p_j` for a doubly stochastic matrix `A`, then `H(p') ≥ H(p)`.
The Lean statement is `entropyNat_doublyStochastic_le` in `Shannon/Entropy/Properties.lean`.
The proof applies Jensen's inequality for `Real.negMulLog` row-by-row with weights `A_{ij}`, then sums over rows and uses column-stochasticity (`∑_i A_{ij} = 1`) to collapse the left-hand side.

# Property 5: Chain Rule

Shannon defines the conditional entropy of `Y` given `X` as `H_X(Y) := -∑_{i, j} p(i, j) log p_i(j)` with `p_i(j) := p(i, j) / p_X(i)`, and states the chain rule `H(X, Y) = H(X) + H_X(Y)`.
The Lean statement is `chain_rule` in `Shannon/Entropy/Joint.lean`; the correspondence between the Lean single-sum definition `condEntropy` and Shannon's double-sum form is made explicit by `condEntropy_eq_shannon_form` in the same module.
The chain-rule proof expands `H(X)` over the product type by distributing the marginal weight, then combines termwise using `log(p / m) = log p - log m`.

# Property 6: Conditioning Reduces Entropy

Shannon states that conditioning on `X` never increases entropy: `H_X(Y) ≤ H(Y)`, with equality when `X` and `Y` are independent.
The Lean statement is `condEntropy_le_entropyNat` in `Shannon/Entropy/Properties.lean`.
The proof combines Property 5 (chain rule) with Property 3 (subadditivity): `H(X) + H_X(Y) = H(X, Y) ≤ H(X) + H(Y)`, cancel `H(X)` on the left.
The complementary `condEntropy_nonneg` shows the conditional entropy is itself nonnegative.
