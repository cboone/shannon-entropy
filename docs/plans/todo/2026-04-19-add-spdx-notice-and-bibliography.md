# 2026-04-19 Add SPDX coverage, NOTICE, and bibliography metadata

## Context

The repo now has an explicit split-license story at the top level, but the file-level provenance and notice infrastructure are still missing. There is no `NOTICE` file yet, no established SPDX / REUSE coverage mechanism, no `docs/references.bib`, and the new mathematical prose cites sources informally rather than through a small canonical bibliography.

This work needs to preserve the fork relationship carefully. Original upstream files that remain untouched should stay untouched. Original upstream files that have been substantially modified should carry an Apache-style modification notice and a dual-license SPDX expression. New code and new prose added in this fork should be labeled directly according to the licensing policy already described in the repo.

`README.md` is intentionally out of scope for this branch because it will be completely rewritten in another workstream. Do not edit it here.

## Goals

1. Add a top-level `NOTICE` file summarizing provenance and the file-class license map.
2. Make the repo pass `reuse lint`.
3. Add SPDX coverage without editing untouched upstream source files in place.
4. Add SPDX dual notices and modification notices to substantially modified upstream files.
5. Add `docs/references.bib` with the canonical bibliographic entries currently cited in the repo.
6. Add short references sections to touched mathematical docstrings and narrative files where the source attribution materially helps the reader.

## Coverage rules

### A. New Lean code and tests written in this fork

- License as `Apache-2.0`.
- Add inline Lean comment headers with `SPDX-FileCopyrightText` and `SPDX-License-Identifier`.

### B. Original upstream Lean files left untouched in content

- Do not edit the file body.
- Cover them with adjacent `.license` sidecars.
- Preserve upstream provenance as MIT-only.

Current expected set unless new evidence appears during implementation:

- `Shannon.lean`
- `Shannon/Entropy/Core.lean`
- `Shannon/Entropy/Converse.lean`
- `Shannon/Entropy/Gibbs.lean`

### C. Original upstream Lean files substantially modified in this fork

- Add inline Lean headers.
- Use both copyright lines:
  - `2026 Samuel Schlesinger`
  - `2026 Christopher Boone`
- Use the SPDX license expression `MIT OR Apache-2.0`.
- Add a brief Apache-style modification notice stating the file is derived from the upstream project and has been substantially modified in this fork.

Current expected set:

- `Shannon/Entropy.lean`
- `Shannon/Entropy/Uniform.lean`
- `Shannon/Entropy/Rational.lean`
- `Shannon/Entropy/Approx.lean`
- `Shannon/Entropy/Final.lean`
- `Shannon/Entropy/Joint.lean`
- `Shannon/Entropy/Properties.lean`

### D. New prose and mathematical exposition written in this fork

- License as `CC-BY-4.0`.
- Add inline SPDX comments for Markdown and Lean prose files created in this fork.
- This bucket includes book chapters, most docs, and repo-authored Markdown written fresh here.

### E. Special provenance files

- `CODE_OF_CONDUCT.md`: preserve the Contributor Covenant attribution and license (`CC-BY-SA-4.0`) via SPDX metadata.
- `references/shannon1948.pdf`: add a sidecar with a `LicenseRef-` identifier describing bundled reference material that is not relicensed by this project.
- `references/shannon1948-transcription.md`: review as source-derived reference material. Prefer the same special handling if the file substantially reproduces Shannon's text.
- Generated or format-constrained files such as `lean-toolchain`, `lake-manifest.json`, and `.gitkeep` files should use sidecars rather than intrusive inline edits.

## Concrete file work

### 1. License inventory normalization

- Rename `LICENSES/APACHE-2.0.txt` to `LICENSES/Apache-2.0.txt` so the file name matches the SPDX identifier expected by `reuse`.
- Keep `LICENSES/MIT.txt` and `LICENSES/CC-BY-4.0.txt` as-is.
- Add any needed `LicenseRef-...` text file under `LICENSES/` for bundled reference material.

### 2. NOTICE

Create `NOTICE` with:

- Upstream fork provenance.
- Copyright ownership split.
- File-class license summary.
- A note that the bundled Shannon reference material is not relicensed by the project.
- A pointer to the specific license texts in `LICENSES/`.

### 3. SPDX coverage implementation strategy

- Prefer inline headers for files that are new in this fork or already being edited.
- Prefer `.license` sidecars for untouched upstream files, binary files, and awkward plain-text formats.
- Keep comments short and consistent by file type.

### 4. Bibliography

Create `docs/references.bib` with at least these entries:

- `Shannon1948`
- `CoverThomas2006`
- `MacKay2003`

No other clearly referenced mathematical works were found during the initial audit.

### 5. Mathematical citations

Add short `## References` sections only where they are useful and already within touched files. Target files:

- `Shannon/Entropy/Uniform.lean`
- `Shannon/Entropy/Rational.lean`
- `Shannon/Entropy/Approx.lean`
- `Shannon/Entropy/Final.lean`
- `Shannon/Entropy/Joint.lean`
- `Shannon/Entropy/Properties.lean`
- `Shannon/Entropy/Bits.lean`
- `Book/AxiomaticEntropy.lean`
- `Book/Properties.lean`
- `Book/Logarithm.lean`
- `Book/Bibliography.lean`

Keep citations tight. Module docstrings and major public theorem docstrings are in scope; helper lemmas are not.

## Verification

Run, in order:

```bash
reuse lint
make lint-markdown
lake build Shannon
lake build Book
lake test
```

If all pass, run:

```bash
make check
```

## Commit plan

Make small signed commits at logical boundaries:

1. Plan only.
2. License inventory normalization and `NOTICE`.
3. SPDX coverage for code and tooling.
4. SPDX coverage for prose and special-case reference files.
5. Bibliography and citation additions.
6. Final verification fixes, if needed.
