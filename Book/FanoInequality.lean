/-
SPDX-FileCopyrightText: 2026 Christopher Boone
SPDX-License-Identifier: CC-BY-4.0
-/

import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Fano's Inequality" =>
%%%
tag := "fano-inequality"
%%%

This chapter explains the estimator setting formalized in `Shannon/Entropy/Fano.lean`.
Phase C's endpoint is a base-2 version of Fano's inequality, which converts decoder error probability into an upper bound on conditional entropy.

# The Estimator Setting

Start with a joint distribution `p` on `(X, Y)` and an estimator `f : β → α` that predicts the first coordinate from the second.
The definition `errorProb p f` is the probability that the estimate is wrong.
The helper `rowErrorProb` records the same error row-by-row after conditioning on a fixed `Y = y`.

# Binary Entropy in Bits

The bound uses the binary-entropy wrapper `binEntropyBits`, formalized in `Shannon/Entropy/BinaryEntropy.lean`.
It is a thin base-2 wrapper over Mathlib's `Real.binEntropy`, with public lemmas at `0`, `1`, and `1/2`, together with symmetry and the standard bounds `0 ≤ h₂(p) ≤ 1`.

# Fano's Inequality

The theorem `fanoInequality` states that `condEntropyBits (swapJoint p)` is at most `binEntropyBits Pe + Pe * log₂(|α| - 1)`, where `Pe := errorProb p f`.
The proof first rewrites `H(X | Y)` as a weighted sum of row entropies, then bounds each row by a `q`-ary entropy expression at the distinguished decoder output, and finally averages those bounds with Jensen's inequality for `Real.qaryEntropy`.
In the special case `|α| = 2`, the logarithmic correction term vanishes, so the bound collapses to the binary-entropy term alone.

# Forward Pointer to Phase E

Phase C proves the estimator inequality for finite alphabets.
Phase E will return to Shannon's source-model setting and the paper's transducer-form data processing statement, where these same finite-alphabet primitives become the local entropy estimates inside longer source arguments.
