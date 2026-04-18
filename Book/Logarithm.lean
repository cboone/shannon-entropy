import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Logarithm Base and the Scale Constant" =>
%%%
tag := "logarithm-base"
%%%

Shannon's proof of Theorem 2 delivers the entropy formula up to a positive multiplicative constant.
This chapter explains what that constant is, how it changes with the logarithm base, and how the present formalization reflects the choice in its public API.

# The Scale Constant `K`

The argument in Appendix 2 fixes the `s = 2` anchor when normalizing the characterization: with `A(n) := H(1/n, ..., 1/n)` and the ratio lemma `A(t) / A(s) = log_s t` for every `s, t > 1`, specializing `s := 2` yields `A(n) = (A(2) / log 2) · log n`.
The factor `A(2) / log 2` is positive whenever `A(2) > 0`, which holds as soon as `H` is strictly greater on the `n = 2` uniform than on the degenerate `n = 1` distribution (which has entropy `0`).

The Lean counterpart is `K` in `Shannon/Entropy/Uniform.lean`: `K H := Apos H 2 / Real.log 2`, with positivity proved by `K_pos`.
The scale constant survives into the final uniqueness theorem `entropyNat_unique` as the coefficient in `H p = -K H * ∑ p_i log p_i`.

# Base Choice

The constant is "base-dependent" in the sense that rewriting `log` in a new base absorbs a multiplicative factor.
Changing to a base `b > 1`, the identity `Real.log x = Real.log b · Real.logb b x` converts `H p = -K ∑ p_i log p_i` into `H p = -(K · log b) * ∑ p_i logb b p_i`, so the "new" constant is `K · log b`.

Two choices of base are standard in the information-theory literature:

- *Natural log (nats).* With base `e` the constant is just `K`, and the entropy is measured in _nats_. This is the internal working unit of this formalization: `entropyNat` in `Shannon/Entropy/Uniform.lean`.
- *Base 2 (bits).* With base `2` the constant becomes `K · log 2`, and the entropy is measured in _bits_. This is the unit Shannon uses for communication-theoretic statements throughout the rest of the 1948 paper. The public API for this formalization exposes it as `entropyBits` in `Shannon/Entropy/Bits.lean`.

The Lean counterparts of the base-parametric and base-2 forms of Theorem 2 are:

- `entropyBase_unique` in `Shannon/Entropy/Final.lean`, the base-parametric restatement that makes the scaling explicit.
- `entropyBits_unique` in `Shannon/Entropy/Bits.lean`, the base-2 specialization with existential constant, and `entropyBits_unique_eq`, the tighter form that names the constant as `K H · Real.log 2`.

# Going Forward

Phase C and later phases of this formalization work in bits.
Statements aimed at Shannon's communication-theoretic results (the Asymptotic Equipartition Property, typical sets, channel capacity) will be stated in terms of `entropyBits` rather than `entropyNat`.
The natural-log `entropyNat` remains available as an internal workhorse, and the bridge lemmas `entropyBits_eq_entropyNat_div_log_two` and `entropyNat_eq_entropyBits_mul_log_two` let proofs cross between the two units as needed.
