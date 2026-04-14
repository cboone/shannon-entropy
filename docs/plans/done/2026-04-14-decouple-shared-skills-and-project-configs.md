# 2026-04-14 Decouple shared skills, memories, and CLAUDE.mds

## Context

The user has a skill stack (`write-lean-code`, `write-pandoc-markdown`, `write-math`, `write-latex`) whose real files live under `/Users/ctm/Development/strength-model/skills/` and whose globally advertised copies at `~/.claude/skills/*` are symlinks into that repo. As long as strength-model was the only active Lean project, that was fine. Now shannon-entropy is actively maintained by the user too, so every strength-model-specific path (`proofs/StrengthModel/`, `StrengthModelTest/`, `bin/bootstrap-proofs-worktree`, `make check-proofs`, the `StrengthModel` namespace rule, the "`proofs/.lake/packages/shannon-entropy/` is not a reference" caveat) baked into the skills actively misleads work in shannon-entropy.

Memories have the same kind of entanglement: the strength-model memory directory holds feedback memories that are really cross-project Lean workflow rules, and one memory (`feedback_proofs_shannon_vendored.md`) was written under the old assumption that shannon-entropy's vendored form is "some random person on the internet." Shannon-entropy's own memory directory is almost empty and doesn't yet mirror the Lean conventions that apply here.

Goal: separate the three layers cleanly.

- **Global skills** (symlinked from strength-model): only generic Lean/Pandoc/math/LaTeX guidance. No project names, no project paths.
- **Global CLAUDE.md** (`~/.claude/CLAUDE.md`): the cross-project meta-rules about how to use the skills (priority hierarchy, always-invoke rule). These apply to every project.
- **Project CLAUDE.mds** and **project memories**: project-specific paths, namespace conventions, test layout, vendored-dependency caveats, and project-local overrides of Mathlib defaults.

Skill files stay physically in strength-model per user preference; the symlinks are fine once the content itself is degenericized.

## End-state layout

```
~/.claude/CLAUDE.md                          # + new Lean workflow meta-rules section
~/.claude/skills/write-lean-code -> strength-model/skills/write-lean-code/    (unchanged symlink)
~/.claude/skills/write-pandoc-markdown -> ...                                 (unchanged)
~/.claude/skills/write-math -> ...                                            (unchanged)
~/.claude/skills/write-latex -> ...                                           (unchanged)

strength-model/skills/write-lean-code/       # generic Lean guidance only
strength-model/skills/write-pandoc-markdown/ # generic Pandoc guidance only
strength-model/skills/write-math/            # near-generic today; small touches
strength-model/skills/write-latex/           # near-generic today; small touches

strength-model/CLAUDE.md                     # absorbs project-specific bits pulled out of skills
strength-model/.../memory/                   # trimmed: workflow meta-rules move to global CLAUDE.md

shannon-entropy/CLAUDE.md                    # gains parallel sections for its paths/namespaces
shannon-entropy/.../memory/                  # gains minimal pointer memory; fork-status already present
```

## Changes by file

### A. Generic skill files (strip project specifics)

#### `strength-model/skills/write-lean-code/SKILL.md`

- Remove lines 27–32 (Workflow): replace with generic "run the project's documented bootstrap script before any direct `lake build`; verify Mathlib came from prebuilt cache, not a local source compile; run the project's test suite / linter after changes; keep tests in lockstep with proof code per the project's mirroring convention if one exists."
- Remove lines 36–44 (Project-Local Caveats) entirely. Replace with a short "Project-Local Caveats" stub: "Each project using this skill should document its own bootstrap script, test-mirroring convention, namespace rules, and any vendored Lean dependencies that must be excluded from style searches. See the invoking project's CLAUDE.md."
- Keep lines 22–25 (Core Principles), 46–60 (Reference Navigation), 62–72 (Sources).

#### `strength-model/skills/write-lean-code/references/essential/checklist.md`

- Remove lines 7–9 (Project-Local Build Policy block hardcoding `bin/bootstrap-proofs-worktree`).
- Remove lines 13–18 (Test Suite Maintenance block hardcoding `StrengthModelTest/` + `make check-proofs`).
- Remove lines 20–27 (Namespace Conventions block listing `StrengthModel` foundational vs paper-specific modules).
- Replace each removed block with a single generic line pointing to "see the project's CLAUDE.md."
- Keep all generic Lean/Mathlib checklist items (naming, formatting, proof style, comments, Mathlib API discovery, API design) unchanged.

#### `strength-model/skills/write-lean-code/references/comprehensive/general-programming.md`

- Line 336: drop the `bin/bootstrap-proofs-worktree` sentence; keep the generic "do not compile Mathlib from source when a prebuilt cache is available" spirit but phrase it project-agnostically.

#### `strength-model/skills/write-lean-code/references/comprehensive/mathlib-api-discovery.md`

- Lines 70, 98, 274–275: replace `proofs/.lake/packages/mathlib/` with `<project's Mathlib package path>` or a generic example; drop "This map covers the Mathlib areas used in `proofs/StrengthModel/`" in favor of "adjust the module map to the Mathlib areas your project actually depends on."
- Line 86: generalize "exclude `proofs/.lake/packages/shannon-entropy/`" to "exclude any vendored Lean dependencies the project flags in its CLAUDE.md."

#### `strength-model/skills/write-pandoc-markdown/` (biggest refactor)

Largest bleed. Generalize these reference files so they describe the pattern, not strength-model's implementation of it. Every path like `papers/shared/templates/ieee.latex`, `../shared/bibliography.bib`, `papers/shared/macros.tex`, `papers/shared/tikz-styles.tex`, every named paper (1-sok, 2a-formal-model, etc.), and every `make 1-sok`-style Makefile example becomes a generic placeholder.

- `SKILL.md:69` — drop "strength-model project conventions" from Sources.
- `references/build-pipeline.md` — rewrite lines 3, 40, 86, 130, 141, 153, 156, 288–291 to use abstract names like `templates/<venue>.latex`, `shared/bibliography.bib`, `<paper-id>` instead of `1-sok`. Keep the two-stage Pandoc → latexmk explanation; it's universally useful.
- `references/cross-references.md:57,75,93,286` — generalize cleveref guidance; drop references to `papers/shared/macros.tex`.
- `references/math-and-citations.md:210` — generalize `--natbib` guidance and `../shared/bibliography.bib`.
- `references/yaml-frontmatter.md:104,129,402–427` — replace the full strength-model SoK frontmatter example with a synthetic minimal example. Drop hard-coded author/nocite.
- `references/raw-latex-blocks.md:173,193,259` — describe the pattern ("project-wide macros file, project-wide tikz styles file") without citing strength-model filenames.

Effort: highest in the plan. Worth doing because this skill is also globally symlinked.

#### `strength-model/skills/write-math/`

- Near-generic already. Only change: verify SKILL.md Sources / introductions don't mention "strength-model" or venue-ladder strategy tied to strength-model. Trim any submission-strategy language from `references/citations-and-references.md` and `references/revision-and-process.md` that reads as generic but was written with the strength-model submission ladder in mind.

#### `strength-model/skills/write-latex/`

- Near-generic. Only touchup: the `macros-and-cross-refs.md:39` "unless project convention" aside can stay as-is; no hard references to strength-model paths found.

### B. Global CLAUDE.md (`~/.claude/CLAUDE.md`)

Add (or fold into the existing Skills section near line 93) a new subsection "Lean workflow":

- Always invoke the `write-lean-code` skill first before any Lean edit, read-for-review, or discussion.
- Convention priority when sources conflict: **user preferences (this file, project CLAUDE.md, explicit instructions) > Mathlib > general Lean community**.
- When you discover a project-local override of a Mathlib default, record it in the project's CLAUDE.md (not in memory) unless it's too specific to matter more than once.
- Line-length override: this user does not enforce Mathlib's ~100-char line limit across any Lean project.
- No-hardwrap override: comments and docstrings (`/-- -/`, `/-! -/`, `/- -/`, `--`) are single long lines per paragraph; blank lines separate paragraphs. This applies to every Lean project the user works on.

These are the genuinely cross-project rules currently trapped in `strength-model/.../memory/feedback_mathlib_conventions.md`.

### C. strength-model/CLAUDE.md

Keep most of it. Two adjustments:

- The Proofs (Lean formalization) section already documents strength-model's bootstrap, test mirroring, and namespace rules. No change needed; it's already the right home for these — the skill was just duplicating it.
- Add a brief "Lean style overrides for this project" line near that section pointing to the global CLAUDE.md rules. (Optional: only if it helps readability.)
- Line 64 already documents the "shannon-entropy is vendored, not a style reference" caveat. Soften wording to acknowledge that shannon-entropy is now an actively maintained user project whose form inside `proofs/.lake/packages/` is still pinned build artifact — the exclusion rule stands, but the reason is structural (it's a dependency boundary), not quality.

### D. shannon-entropy/CLAUDE.md

Parallel the strength-model structure for the shannon-entropy paths that already exist in this file:

- The Fresh Clone / Worktree Bootstrap section already documents `bin/bootstrap-worktree`. Good.
- The Module Layout and Lean Conventions sections already exist. Good.
- Add a small "Namespace Conventions" bullet under Lean Conventions: everything lives under `Shannon.Entropy.*`; no second-tier nesting. This mirrors the kind of note strength-model has and fills the gap the skill used to cover.
- Add a "Skill invocation" note: write-lean-code is generic per global CLAUDE.md; this file is authoritative for project-specific Lean layout.
- Add a Vendored dependencies note: shannon-entropy itself vendors no Lean code beyond Mathlib. (Symmetric to strength-model's shannon-entropy caveat, but here the answer is simply "there isn't one.")

### E. strength-model memory

Current files:

- `feedback_mathlib_conventions.md`: move its cross-project content (invoke skill first, priority hierarchy, line-length + no-hardwrap overrides) into global CLAUDE.md (section B above). What remains strength-model-specific in this memory is minimal; trim to a one-line pointer "see global CLAUDE.md for Lean workflow; see strength-model/CLAUDE.md for project-specific Lean rules." Or delete the memory entirely and update `MEMORY.md` to drop the entry.
- `feedback_proofs_shannon_vendored.md`: rewrite. Drop the "some random person on the internet" characterization. Rephrase as: "`proofs/.lake/packages/shannon-entropy/` is a pinned build artifact of the user's own `cboone/shannon-entropy` fork; it's still not a style reference here because it's a dependency boundary, not because of provenance. Style changes to shannon-entropy happen in that repo, not this one." Keep the "exclude from grep for conventions" rule.
- Other memories (`feedback_citation_keys.md`, `feedback_paper_scaffold_convention.md`, `feedback_planning_skill_active.md`, `project_collaborators.md`, `project_2026_04_13_program_reorganization.md`, `user_role.md`): no changes.

Update strength-model's `MEMORY.md` index to reflect the trims.

### F. shannon-entropy memory

Current state: `MEMORY.md` has one entry (`project_overview.md`). Add:

- `feedback_lean_workflow.md` — a short pointer memory: "Lean workflow rules live in global CLAUDE.md; project-specific Lean layout (namespace, bootstrap, test mirror, upstream/fork flow) lives in shannon-entropy/CLAUDE.md. Memory does not duplicate either." This exists mainly so a future session notices the pointer and doesn't drift into recreating the same content.
- Optionally: `feedback_upstream_pr_flow.md` — records the "selected improvements pushed upstream to SamuelSchlesinger/shannon-1948-formalization" flow, because this is the kind of cross-session fact that isn't derivable from code alone. Keep it short.

Update `MEMORY.md` index accordingly.

## Critical files to modify

- `/Users/ctm/Development/strength-model/skills/write-lean-code/SKILL.md`
- `/Users/ctm/Development/strength-model/skills/write-lean-code/references/essential/checklist.md`
- `/Users/ctm/Development/strength-model/skills/write-lean-code/references/comprehensive/general-programming.md`
- `/Users/ctm/Development/strength-model/skills/write-lean-code/references/comprehensive/mathlib-api-discovery.md`
- `/Users/ctm/Development/strength-model/skills/write-pandoc-markdown/SKILL.md` and `references/{build-pipeline,cross-references,math-and-citations,yaml-frontmatter,raw-latex-blocks}.md`
- `/Users/ctm/Development/strength-model/skills/write-math/SKILL.md` (small)
- `/Users/ctm/Development/strength-model/skills/write-latex/` (minor if anything)
- `/Users/ctm/.claude/CLAUDE.md`
- `/Users/ctm/Development/strength-model/CLAUDE.md`
- `/Users/ctm/Development/shannon-entropy/CLAUDE.md` (same file as `AGENTS.md` via symlink per this repo's pattern; verify which is canonical before editing)
- `/Users/ctm/.claude/projects/-Users-ctm-Development-strength-model/memory/feedback_mathlib_conventions.md` (trim or remove)
- `/Users/ctm/.claude/projects/-Users-ctm-Development-strength-model/memory/feedback_proofs_shannon_vendored.md` (rewrite)
- `/Users/ctm/.claude/projects/-Users-ctm-Development-strength-model/memory/MEMORY.md` (update index)
- `/Users/ctm/.claude/projects/-Users-ctm-Development-shannon-entropy/memory/` — add 1–2 pointer memories; update `MEMORY.md`

## Execution order

1. Degenericize `write-lean-code` skill files (A subitems for that skill).
2. Add cross-project Lean workflow section to global `~/.claude/CLAUDE.md` (B).
3. Update shannon-entropy `CLAUDE.md` with its parallel namespace/skill notes (D).
4. Verify strength-model `CLAUDE.md` still covers everything the skill no longer does; add pointer line if needed (C).
5. Trim/rewrite strength-model memory files (E) + update its `MEMORY.md`.
6. Add pointer memories to shannon-entropy + update its `MEMORY.md` (F).
7. Degenericize `write-pandoc-markdown` (largest skill refactor; do after the Lean-side cleanup so the smaller pieces are already settled).
8. Light touches on `write-math` and `write-latex` (small).

Each step is independently committable. Commits live in the strength-model repo (for skills + its CLAUDE.md + its memory updates, though memory edits are outside git), in shannon-entropy (for its CLAUDE.md and memory edits, also outside git), and nowhere for `~/.claude/CLAUDE.md` (it's bare-repo managed; user handles commits there per their dotfiles setup).

## Verification

After each step:

1. `grep -rn "StrengthModel\|bin/bootstrap-proofs-worktree\|check-proofs\|proofs/StrengthModel" /Users/ctm/Development/strength-model/skills/` should return zero hits in the degenericized skills (write-lean-code first, then write-pandoc-markdown).
2. `grep -rn "shannon-entropy" /Users/ctm/Development/strength-model/skills/` should return zero hits.
3. From shannon-entropy: simulate invoking the skill by re-reading `~/.claude/skills/write-lean-code/SKILL.md` and confirming no instruction refers to paths that do not exist here. Sanity-check that the generic "see the project's CLAUDE.md" pointer lands on the shannon-entropy CLAUDE.md content added in step 3.
4. From strength-model: run `make check-proofs` (or `cd proofs && lake build StrengthModel && lake test`) to confirm that moving skill content into CLAUDE.md didn't break any actual workflow a script depends on. (It shouldn't; skills are documentation, not executable.)
5. Read the updated `~/.claude/CLAUDE.md` Lean section aloud against a fresh invocation scenario: does it answer "what skill do I invoke first, how do I break ties between user/Mathlib/Lean conventions, what are the user's standing overrides" without naming a project? If yes, it's in the right place.
6. In each project's memory `MEMORY.md`, confirm every line pointer resolves to a file that still exists with matching frontmatter.

End-to-end test: start a fresh shannon-entropy session and ask Claude to add a new lemma. It should invoke `write-lean-code`, then read `shannon-entropy/CLAUDE.md` for project paths, and never reference `StrengthModelTest/` or `bin/bootstrap-proofs-worktree`. Symmetrically in strength-model, it should reference `StrengthModelTest/` from the project CLAUDE.md, not from the skill.
