/-
SPDX-FileCopyrightText: 2026 Samuel Schlesinger
SPDX-FileCopyrightText: 2026 Christopher Boone
SPDX-License-Identifier: MIT
-/

import Shannon.Entropy.Properties
import Shannon.Entropy.Converse
import Shannon.Entropy.Bits
import Shannon.Entropy.RelativeEntropy
import Shannon.Entropy.MutualInfo
import Shannon.Entropy.BinaryEntropy
import Shannon.Entropy.Fano

/-!
# Shannon.Entropy

Facade module for the Shannon entropy formalization.

Import this file to access the full development:
- Characterization theorems (Appendix 2): `entropyNat_unique`, `entropyBase_unique`
- Converse: `entropyNat_shannonAxioms` (entropy satisfies the axioms)
- Section 6 properties: nonnegativity, maximum at uniform, subadditivity,
  conditioning reduces entropy, chain rule, product additivity
- base-2 API: `entropyBits`, `mutualInfoBits`, `condEntropyBits`, `relEntropyBits`, `binEntropyBits`, `fanoInequality`

## Module chain

The entropy library is a DAG. The path from `Core` to `Fano` splits after `Gibbs` into a Phase A/B spine and a Phase C layer; every Phase C module sits above `Joint` in the DAG.

Phase A/B spine:

- `Core → Uniform → Rational → Approx → Final → Gibbs → Joint`
- `Gibbs → Converse`
- `Joint → Properties`
- `Joint → Bits → RelativeEntropy`

Phase C layer:

- `{Properties, RelativeEntropy, Converse} → MutualInfo → FanoHelpers → Fano`
- `Converse → FanoHelpers`
- `BinaryEntropy → Fano` (Mathlib-only; no in-house dependency)
-/
