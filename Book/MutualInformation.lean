import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Mutual Information" =>
%%%
tag := "mutual-information"
%%%

This chapter introduces the information-theoretic primitives added in Phase C that sit immediately beyond Shannon's Section 6 properties.
The central quantity is mutual information, written `mutualInfo` in nats and `mutualInfoBits` in bits, formalized in `Shannon/Entropy/MutualInfo.lean`.

# Definition

For a joint distribution `p` on `(X, Y)`, mutual information is the gap between the sum of the marginal entropies and the joint entropy: `I(X; Y) = H(X) + H(Y) - H(X, Y)`.
The Lean definition is `mutualInfo p := entropyNat (marginalFst p) + entropyNat (marginalSnd p) - entropyNat p`.
The same module also defines `mutualInfoBits` and `condEntropyBits`, so the communication-theoretic statements later in the development can be written directly in base 2.

# Nonnegativity and Independence

The first structural fact is `mutualInfo_nonneg`: information shared between `X` and `Y` is never negative.
The sharper statement is `mutualInfo_eq_zero_iff_independent`, which identifies the zero case with independence of the joint law.
The proof route is standard: `mutualInfo_eq_relEntropy_prodMarginals` rewrites `I(X; Y)` as a relative entropy against the product of marginals, then `relEntropy_eq_zero_iff` in `Shannon/Entropy/RelativeEntropy.lean` finishes the argument.

# Chain Rule and Conditioning

The identities `mutualInfo_eq_entropyFst_sub_condEntropy_swap` and `mutualInfo_eq_entropySnd_sub_condEntropy` are the two familiar chain-rule forms `I(X; Y) = H(X) - H(X | Y)` and `I(X; Y) = H(Y) - H(Y | X)`.
In the Lean API the first form uses `swapJoint` because `condEntropy` conditions on the first coordinate of a pair.
These identities are the bridge from the entropy facts in `Shannon/Entropy/Joint.lean` and `Shannon/Entropy/Properties.lean` to the later communication-theoretic inequalities.

# Self-Information and Bounds

The helper `diagonalDist` packages the joint law of `(X, X)`.
With it, `mutualInfo_self` proves `I(X; X) = H(X)`, while `mutualInfo_le_entropyFst` and `mutualInfo_le_entropySnd` show that shared information cannot exceed either marginal entropy.
The symmetry statement `mutualInfo_symm` and the base-2 counterparts `mutualInfoBits_symm`, `mutualInfoBits_self`, `mutualInfoBits_le_entropyBitsFst`, and `mutualInfoBits_le_entropyBitsSnd` complete the public surface used by the rest of Phase C.
