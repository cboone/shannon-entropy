---
title: A Mathematical Theory of Communication
authors: Claude E. Shannon
bibtex_key: shannon1948
year: 1948
venue: Bell System Technical Journal, Vol. 27, pp. 379-423, 623-656
pdf: ../references/shannon1948.pdf
transcription_scope: framework-only
---

## Notation

Shannon's original notation uses uppercase for entropy ($H$) and lowercase for probabilities ($p_i$). Modern convention (Cover and Thomas) uses $H(X)$ to denote the entropy of random variable $X$. This transcription follows Shannon's notation for faithfulness, with modern equivalents noted.

| Paper | Meaning | Modern equivalent |
| --- | --- | --- |
| $H(p_1, \ldots, p_n)$ | Entropy of a distribution | $H(X)$ |
| $H_x(y)$ | Conditional entropy of $y$ given $x$ | $H(Y \mid X)$ |
| $H(x, y)$ | Joint entropy | $H(X, Y)$ |
| $p_i$ | Probability of the $i$-th outcome | -- |
| $p_i(j)$ | Transition probability from state $i$ to $j$ | -- |
| $P_i$ | Stationary probability of state $i$ | -- |
| $G_N$ | Per-symbol entropy of $N$-symbol blocks | -- |
| $F_N$ | Conditional entropy of the $N$-th symbol given the preceding $N-1$ | -- |
| $K$ | Positive constant (choice of logarithm base) | -- |

## Scope

This 55-page paper defines the foundations of information theory. This transcription extracts only the results directly relevant to the formalization: the axiomatic definition of entropy (Theorem 2), key properties of $H$, the Asymptotic Equipartition Property (Theorem 3), the typical set characterization (Theorem 4), the per-symbol entropy convergence (Theorems 5-6), and the data processing inequality (Theorem 7). Proofs are omitted (they are standard textbook material).

## Axiomatic Definition of Entropy

### Shannon's Three Axioms

Shannon poses the question: given a set of possible events with probabilities $p_1, p_2, \ldots, p_n$, can we find a measure $H(p_1, p_2, \ldots, p_n)$ of "choice" or "uncertainty"? He requires three properties (Section 6):

1. $H$ should be continuous in the $p_i$.
2. If all the $p_i$ are equal, $p_i = 1/n$, then $H$ should be a monotonic increasing function of $n$. With equally likely events there is more choice, or uncertainty, when there are more possible events.
3. If a choice be broken down into two successive choices, the original $H$ should be the weighted sum of the individual values of $H$. For example: $H(1/2, 1/3, 1/6) = H(1/2, 1/2) + (1/2) \cdot H(2/3, 1/3)$.

### Theorem 2 (Uniqueness of entropy)

::: {.theorem}
**Theorem 2** (Thm. 2). The only $H$ satisfying the three above assumptions is of the form:

$$H = -K \sum_{i=1}^{n} p_i \log p_i$$

where $K$ is a positive constant.
:::

The choice of $K$ corresponds to the choice of logarithm base. With $K = 1$ and $\log = \log_2$, $H$ is measured in bits. With natural logarithms, $H$ is in nats.

## Properties of Entropy

The following properties are established in Section 6 (pp. 11-12):

::: {.proposition}
**Property 1** (Non-negativity). $H = 0$ if and only if all $p_i$ but one are zero, with that one being unity. Otherwise $H > 0$.
:::

::: {.proposition}
**Property 2** (Maximum at uniformity). For a given $n$, $H$ is a maximum and equal to $\log n$ when all $p_i$ are equal ($p_i = 1/n$).
:::

::: {.proposition}
**Property 3** (Subadditivity). For any two events $x$ and $y$,

$$H(x, y) \leq H(x) + H(y)$$

with equality if and only if the events are independent ($p(i, j) = p(i) \cdot p(j)$).
:::

::: {.proposition}
**Property 4** (Averaging increases entropy). Any change toward equalization of the probabilities $p_1, p_2, \ldots, p_n$ increases $H$. More generally, if $p_i' = \sum_j a_{ij} p_j$ where $\sum_i a_{ij} = \sum_j a_{ij} = 1$ and all $a_{ij} \geq 0$ (a doubly stochastic matrix), then $H$ increases (except when the transformation is a permutation).
:::

::: {.proposition}
**Property 5** (Chain rule). The conditional entropy of $y$ given $x$ is defined as

$$H_x(y) = -\sum_{i, j} p(i, j) \log p_i(j),$$

where $p_i(j) = p(i, j) / \sum_k p(i, k) = p(i, j)/p(i)$. Substituting gives $H_x(y) = H(x, y) - H(x)$, or equivalently

$$H(x, y) = H(x) + H_x(y).$$

The uncertainty of the joint event $x, y$ is the uncertainty of $x$ plus the uncertainty of $y$ when $x$ is known.
:::

::: {.proposition}
**Property 6** (Conditioning reduces entropy). Combining Properties 3 and 5 gives $H(x) + H(y) \geq H(x, y) = H(x) + H_x(y)$, hence

$$H(y) \geq H_x(y).$$

The uncertainty of $y$ is never increased by knowledge of $x$. It will be decreased unless $x$ and $y$ are independent events, in which case it is not changed.
:::

## Asymptotic Equipartition Property

### Theorem 3 (AEP)

::: {.theorem}
**Theorem 3** (Thm. 3). Given any $\epsilon > 0$ and $\delta > 0$, we can find an $N_0$ such that the sequences of any length $N \geq N_0$ fall into two classes:

1. A set whose total probability is less than $\epsilon$.
2. The remainder, all of whose members have probabilities satisfying the inequality

$$\biggl\lvert\frac{\log p^{-1}}{N} - H\biggr\rvert < \delta.$$
:::

In other words, we are almost certain to have $\frac{\log p^{-1}}{N}$ close to $H$ when $N$ is large. This is the Asymptotic Equipartition Property: for long sequences from an ergodic source, the per-symbol log-probability converges to the entropy rate $H$.

### Theorem 4 (Typical set size)

::: {.theorem}
**Theorem 4** (Thm. 4). $\lim_{N \to \infty} \frac{\log n(q)}{N} = H$ when $q$ does not equal 0 or 1, where $n(q)$ is the number of sequences of length $N$ that must be taken (starting from the most probable) to accumulate a total probability $q$.
:::

If $\log$ is base 2 (so that $H$ is measured in bits), this means $n(q) \approx 2^{HN}$ for large $N$; more generally, if $\log = \log_b$, then $n(q) \approx b^{HN}$. Thus the number of "reasonably probable" sequences grows exponentially at rate $H$, independent of the probability threshold $q$. In Shannon's base-2 formulation, he notes that "for most purposes to treat the long sequences as though there were just $2^{HN}$ of them, each with a probability $2^{-HN}$."

## Per-Symbol Entropy Convergence

### Theorem 5

::: {.theorem}
**Theorem 5** (Thm. 5). Let $p(B_i)$ be the probability of a sequence $B_i$ of symbols from the source. Let

$$G_N = -\frac{1}{N} \sum_i p(B_i) \log p(B_i)$$

where the sum is over all sequences $B_i$ containing $N$ symbols. Then $G_N$ is a monotonic decreasing function of $N$ and

$$\lim_{N \to \infty} G_N = H.$$
:::

### Theorem 6

::: {.theorem}
**Theorem 6** (Thm. 6). Let $F_N = -\sum_{i,j} p(B_i, S_j) \log p_{B_i}(S_j)$ where the sum is over all blocks $B_i$ of $N - 1$ symbols and all symbols $S_j$. Then $F_N$ is a monotone decreasing function of $N$,

$$F_N = N G_N - (N - 1) G_{N-1},$$

$$G_N = \frac{1}{N} \sum_{n=1}^{N} F_n,$$

$$F_N \leq G_N,$$

and $\lim_{N \to \infty} F_N = H$.
:::

$F_N$ is the conditional entropy of the next symbol given the preceding $N - 1$ symbols. $G_N$ is the per-symbol entropy of blocks of $N$ symbols. Both converge to $H$, with $F_N$ being the better (tighter) approximation at each $N$.

### Theorem 7 (Data processing inequality)

::: {.theorem}
**Theorem 7** (Thm. 7). The output of a finite state transducer driven by a finite state statistical source is a finite state statistical source, with entropy (per unit time) less than or equal to that of the input. If the transducer is non-singular they are equal.
:::

This is an early form of the data processing inequality: deterministic processing cannot increase entropy.

## Formalization Cross-References

- **Theorem 2** (uniqueness of entropy): `entropyNat_unique`, `entropyBase_unique` in `Shannon/Entropy/Final.lean`
- **Theorem 2** (base 2 specialization): `entropyBits_unique` in `Shannon/Entropy/Bits.lean`
- **Property 1** (non-negativity, deterministic iff): `entropyNat_eq_zero_iff` in `Shannon/Entropy/Properties.lean`
- **Property 2** (maximum at uniformity): `entropyNat_eq_log_card_iff` in `Shannon/Entropy/Properties.lean`
- **Property 3** (subadditivity): `entropyNat_joint_le_add` in `Shannon/Entropy/Properties.lean`
- **Property 4** (doubly stochastic): `entropyNat_doublyStochastic_le` in `Shannon/Entropy/Properties.lean`
- **Property 5** (chain rule): `chain_rule` in `Shannon/Entropy/Joint.lean`, with the summation form given by `condEntropy_eq_shannon_form`
- **Property 6** (conditioning reduces entropy): `condEntropy_le_entropyNat` in `Shannon/Entropy/Properties.lean`
- **Theorem 3** (AEP, i.i.d. case): `aep_iid` in `Shannon/Entropy/AEP.lean`. Phase E upgrades this to stationary finite-state sources; the i.i.d. statement is the Phase D special case.
- **Theorem 4** (typical set size, i.i.d. case): `typicalSet_iidDist_card_le`, `typicalSet_iidDist_card_ge`, `minCover`, and `tendsto_logb_minCover_iid` in `Shannon/Entropy/AEP.lean`. Phase E upgrades this to the stationary finite-state-source setting.
- **Relative entropy (Kullback-Leibler divergence)**: `relEntropy`, `relEntropy_nonneg`, `relEntropy_eq_zero_iff` in `Shannon/Entropy/RelativeEntropy.lean`
- **Mutual information**: `mutualInfo`, `mutualInfo_nonneg`, `mutualInfo_eq_zero_iff_independent`, `mutualInfo_symm`, `mutualInfo_self`, `mutualInfo_le_entropyFst`, and `mutualInfo_le_entropySnd` in `Shannon/Entropy/MutualInfo.lean`
- **Data processing inequality (information form)**: `mutualInfo_kernelPushforward_le` in `Shannon/Entropy/MutualInfo.lean`. Forward pointer: Shannon's transducer form (Theorem 7 in the paper) is deferred to Phase E and is a distinct statement, not a restatement of the information-form DPI.
- **Fano's inequality**: `fanoInequality` in `Shannon/Entropy/Fano.lean`
- **Converse** (entropyNat satisfies axioms): `entropyNat_shannonAxioms` in `Shannon/Entropy/Converse.lean`
