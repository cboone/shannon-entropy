---
title: A Mathematical Theory of Communication
authors: Claude E. Shannon
bibtex_key: shannon1948
year: 1948
venue: Bell System Technical Journal
doi: 10.1002/j.1538-7305.1948.tb01338.x
---

## Summary

Shannon establishes the mathematical foundations of information theory, defining entropy as the measure of uncertainty (or information content) of a random variable. The paper introduces channel capacity, the source coding theorem, and the noisy channel coding theorem, providing the theoretical ceiling for lossless data compression and reliable communication.

## Key Concepts

- **Shannon entropy** is defined as $H = -\sum p_i \log_2 p_i$ for a discrete random variable with probability distribution $\{p_i\}$. It measures the average information (in bits) produced per symbol from the source.
- The **logarithmic measure** (base 2) is chosen for practical and mathematical convenience: it corresponds to binary digits (bits), varies linearly with engineering parameters like bandwidth, and simplifies limiting operations.
- A **discrete source of information** is modeled as a stochastic process that generates a sequence of symbols according to conditional probabilities. Markov chains of various orders approximate natural language with increasing fidelity.
- **Channel capacity** $C = \lim(\log N(T) / T)$ gives the maximum rate at which information can be reliably transmitted through a noisy channel.

## Methodology

- Shannon models communication systems with five components: information source, transmitter, channel, receiver, and destination. Noise enters at the channel.
- Entropy is derived axiomatically from three requirements: continuity, monotonicity for uniform distributions, and a composition (grouping) property.
- The source coding theorem proves that a source with entropy H can be encoded with arbitrarily small error at rates approaching H bits per symbol, but not below.
- Stochastic sources are approximated through n-gram models of increasing order, demonstrating how statistical structure reduces entropy below the naive $\log_2(\text{alphabet\_size})$ estimate.

## Main Findings

- For a uniform distribution over N outcomes, entropy equals $\log_2 N$. Any non-uniform distribution has strictly lower entropy.
- English text has an entropy rate far below $\log_2 26 = 4.7$ bits/letter because of statistical dependencies (digram, trigram, and higher-order structure). Shannon estimated roughly 1.0 to 1.5 bits per letter for English.
- The existence of redundancy (statistical structure) in a source allows compression and, conversely, makes the source more predictable to an attacker who exploits that structure.
