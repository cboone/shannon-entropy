/-
SPDX-FileCopyrightText: 2026 Christopher Boone
SPDX-License-Identifier: CC-BY-4.0
-/

import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Introduction" =>
%%%
tag := "introduction"
%%%

This repository formalizes Shannon's finite-alphabet entropy characterization theorem from Appendix 2 of _A Mathematical Theory of Communication_ and the Section 6 properties that currently depend on it.

The project is maintained in the `cboone/shannon-entropy` fork of Samuel Schlesinger's original `shannon-1948-formalization` repository.
The current completed scope is Appendix 2 together with Section 6 Properties 1 through 6.
Planned later phases extend the formalization to Shannon's Theorems 3 through 7 and expand this book in parallel.

# Reading Order

Readers who want the formal proof first should start with these modules:

- `Shannon/Entropy/Core.lean`
- `Shannon/Entropy/Uniform.lean`
- `Shannon/Entropy/Rational.lean`
- `Shannon/Entropy/Approx.lean`
- `Shannon/Entropy/Final.lean`
- `Shannon/Entropy/Gibbs.lean`
- `Shannon/Entropy/Joint.lean`
- `Shannon/Entropy/Properties.lean`
- `Shannon/Entropy/Converse.lean`
- `Shannon/Entropy/Bits.lean`

Readers who want the narrative companion should read the following book chapters in order, alongside `references/shannon1948-transcription.md` and the Lean modules above:

- Axiomatic Entropy (Shannon's Appendix 2 characterization and its Lean counterparts)
- Properties of Entropy (Shannon's Section 6 Properties 1-6)
- Logarithm Base and the Scale Constant (the `K` constant and the bits / nats distinction)

# Working In This Repo

Fresh clones and fresh worktrees should start with:

```
bin/bootstrap-worktree
```

That command runs `lake update`, downloads prebuilt dependency artifacts, and builds both the `Shannon` and `Book` libraries.

For day-to-day iteration:

```
make book
make serve
```

Use `lake build Book` when a compile-only check is enough and you do not need rendered HTML.
