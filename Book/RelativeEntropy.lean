/-
SPDX-FileCopyrightText: 2026 Christopher Boone
SPDX-License-Identifier: CC-BY-4.0
-/

import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Relative Entropy" =>
%%%
tag := "relative-entropy"
%%%

This chapter covers the finite-alphabet relative-entropy package in `Shannon/Entropy/RelativeEntropy.lean` and the information-form data processing inequality in `Shannon/Entropy/MutualInfo.lean`.
The main point is that Phase C repackages the Gibbs-inequality machinery into the standard textbook primitives `D(p ‖ q)`, log-sum, and information monotonicity.

# Relative Entropy (KL Divergence)

The definition `relEntropy p q := ∑ a, p a * log (p a / q a)` is the finite-alphabet Kullback-Leibler divergence.
The support predicate `Supports q p` records the standard requirement that `q` vanish nowhere on the support of `p`.
Phase C also provides the base-2 wrapper `relEntropyBits`, but the proofs are organized in nats and only converted to bits at the public boundary.

# Gibbs' Inequality Restated

The theorem `relEntropy_nonneg` is Gibbs' inequality in KL form: `D(p ‖ q) ≥ 0` whenever `q` covers the support of `p`.
The equality statement `relEntropy_eq_zero_iff` identifies the rigid case: relative entropy vanishes exactly when `p` and `q` agree pointwise.
This is the formal bridge that lets `mutualInfo_eq_zero_iff_independent` in `Shannon/Entropy/MutualInfo.lean` reduce independence to a zero-KL statement.

# Log-Sum Inequality

The theorem `log_sum_inequality` is the finite log-sum inequality in the form most convenient for later information-theoretic proofs.
Its statement is deliberately total, including the degenerate case where the left-hand total mass vanishes.
That detail matters in Lean because the data processing proof applies the inequality fiberwise, and some fibers can have total mass `0`.

# Data Processing Inequality (Information Form)

The helper `kernelPushforward` pushes a joint law `(X, Y)` forward through a finite kernel `Y → Z` to form the induced joint law `(X, Z)`.
The theorem `mutualInfo_kernelPushforward_le` then states the information-form data processing inequality `I(X; Z) ≤ I(X; Y)`.
This is not yet Shannon's transducer-form Theorem 7 from the paper; that stronger source-model statement is deferred to Phase E.
