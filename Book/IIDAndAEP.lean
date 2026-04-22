/-
SPDX-FileCopyrightText: 2026 Christopher Boone
SPDX-License-Identifier: CC-BY-4.0
-/

import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "I.i.d. Sources and the AEP" =>
%%%
tag := "iid-and-aep"
%%%

This chapter explains the i.i.d. special case of Shannon's Theorems 3 and 4 as formalized in `Shannon/Entropy/IID.lean` and `Shannon/Entropy/AEP.lean`.
Phase D stays in the memoryless setting, where the same one-symbol law is used independently at every coordinate and the entropy rate is exactly the single-letter entropy `entropyBits p`.

# I.i.d. Sources and the Product Distribution

The definition `iidDist p N` packages the law of an `N`-symbol block drawn independently from `p`.
On a word `x : Fin N → α`, its mass is `∏ i, p (x i)`, so block probabilities factor coordinate by coordinate.
The entropy identity `iidDist_entropyBits` then recovers the familiar relation `H(X^N) = N H(X)` directly in bits.

# Per-Symbol Log-Probability and the Typical Set

The helper `logProbBits p a := -Real.logb 2 (p a)` is the one-symbol self-information in bits.
For a block `x`, the empirical average `(1 / N) * ∑ i, logProbBits p (x i)` measures how many bits per symbol are needed to describe that particular word under the model `p`.

The finite typical set `typicalSet p N ε` keeps exactly the words whose empirical per-symbol log-probability lies within `ε` of `entropyBits p`.
It also imposes the support condition `∀ i, 0 < p (x i)`, which excludes impossible symbols when `p` has zero atoms.

For `x ∈ typicalSet p N ε`, the pointwise bounds `iidDist_ge_of_mem_typicalSet` and `iidDist_le_of_mem_typicalSet` say that every typical word has probability between `2 ^ (-N * (entropyBits p + ε))` and `2 ^ (-N * (entropyBits p - ε))`.
This is the precise Lean version of Shannon's heuristic that long typical words all have approximately the same probability, namely `2 ^ (-N H)`.

# Theorem 3: The I.i.d. AEP

The theorem `aep_iid` proves the asymptotic equipartition property in the i.i.d. case.
Given `ε > 0` and `δ > 0`, there is a block length `N₀` such that for every `N ≥ N₀`, the typical set has `iidDist p N`-mass at least `1 - δ`.
The proof uses a finite Chebyshev estimate on the sample mean of `logProbBits p`, together with the identity `sum_mul_logProbBits` that identifies its expectation with `entropyBits p`.

# Theorem 4: Counting the Typical Set

The theorem `typicalSet_iidDist_card_le` gives the upper bound `|typicalSet p N ε| ≤ 2 ^ (N * (entropyBits p + ε))`.
The theorem `typicalSet_iidDist_card_ge` gives the matching lower bound up to the factor `1 - δ` for all sufficiently large `N`.
Together they formalize Shannon's statement that the number of reasonably probable words grows like `2 ^ (N H)`.

The definition `minCover` and the theorem `tendsto_logb_minCover_iid` make this quantitative in Shannon's original "how many words are needed to accumulate probability `q`?" form.
For each fixed `0 < q < 1`, the per-symbol logarithmic growth rate of that minimum cover tends to `entropyBits p`.

# A Numerical Example

Take `p = (0.3, 0.7)`, block length `N = 10`, and `ε = 0.1`.
A word with six occurrences of the `0.7` symbol and four occurrences of the `0.3` symbol has probability `0.7 ^ 6 * 0.3 ^ 4`, so its negative base-2 log-probability is about `10.3`, or about `1.03` bits per symbol.
Since the binary entropy at `0.3` is about `0.881`, this word sits above the entropy rate by roughly `0.15` bits per symbol and is therefore outside the `ε = 0.1` shell.
Typical words for this parameter are closer to the seven-to-three split predicted by the source law.

# Toward Finite-State Sources

The i.i.d. case is the cleanest place to set up the product law, the shell definition, and the `2 ^ (N H)` counting estimates.
Phase E returns to Shannon's full finite-state source model, where the same ideas reappear with entropy rate replacing single-letter entropy.
The chapter `Mutual Information` already explains why a rate interpretation is natural once one moves beyond a single symbol, and Phase E will extend that point of view to stationary finite-state sources.
