import Shannon.Entropy.Properties
import Shannon.Entropy.Converse
import Shannon.Entropy.Bits

/-!
# Shannon.Entropy

Facade module for the Shannon entropy formalization.

Import this file to access the full development:
- Characterization theorems (Appendix 2): `entropyNat_unique`, `entropyBase_unique`
- Converse: `entropyNat_shannonAxioms` (entropy satisfies the axioms)
- Section 6 properties: nonnegativity, maximum at uniform, subadditivity,
  conditioning reduces entropy, chain rule, product additivity
- base-2 API: `entropyBits`, `entropyBits_unique`

## Module chain

`Core → Uniform → Rational → Approx → Final → Gibbs → Joint → Properties`
                                                    ↘ Converse
                                                    ↘ Bits
-/
