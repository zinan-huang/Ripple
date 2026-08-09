# Changelog

This file records notable public-facing changes to Ripple. See
`MAINTENANCE.md` for entry criteria, version namespaces, and the release
procedure.

## [Unreleased]

### Added

- Added an opt-in `SturmCRT` Lake target for rebuilding the complete
  251-prime certificate without putting the multi-hour computation on the
  default build path.

### Changed

- Evaluate the Sturm/CRT recurrence with bounded natural-number residues,
  precompute denominator modular inverses once per recurrence table, and check
  each defining modular equation while its row is generated in a single pass.
  A Lean proof shows that every successful bounded-residue check implies the
  existing integer `ModEq` certificate.
- Folded the former `Fast` shared-computation wrapper into `sturmCRTCheckAll`
  as the single canonical CRT checker, removing the duplicate suffix without
  discarding its sharing optimization.

### Fixed

- Removed the redundant API-documentation deployment from Lean CI. The
  repository continues to use its existing branch-based GitHub Pages site,
  while code pushes now report the Lean build result directly.

### Removed

### Verification

- A source-invalidated `lake build SturmCRT` on `uisai2` completed all 3755
  jobs in 9497 seconds (2h 38m 17s), versus the recorded 342m 48.341s for the
  historical route: 53.83% less wall time, or a 2.166x speedup.
- On `uisai2`, the checked-generator path verified the full Sturm bound for
  `p = 999999929` in 1115.42 seconds of user CPU time (1491.32 seconds elapsed
  at 75% CPU, 4,070,080 KiB peak RSS).

### Documentation

- Documented the dedicated command for rebuilding the optional Sturm/CRT
  certificate separately from the ordinary `Ripple` and `Tri` libraries.

## [r2026.08] - 2026-08-05

### Added

- Added `Tri` as a second Lean library containing the active formalization of
  Condon–Hajiaghayi–Kirkpatrick–Mañuch's tri-molecular approximate-majority
  analysis.
- Added the corrected paper-facing capstones
  `Tri.Byzantine.theorem4_entry` and `Tri.Multi.theorem5`, together with the
  supporting numbered lemmas and probabilistic infrastructure.
- Added an English errata-and-counterexamples document with printed
  publication pages and one-based Springer PDF pages.
- Added an automated GitHub Release workflow for annotated `r*` tags.

### Changed

- Registered the `Ripple.lean` import closure and all of `Tri` as default Lake
  build targets, while retaining the multi-hour compute-from-scratch Sturm/CRT
  certificates in the explicit exhaustive `Ripple` target.
- Moved the Technical Report to historical documentation because this release
  contains a substantial formalization pillar that postdates
  `arXiv:2607.13531v2`.
- Avoided running the full Lean CI workflow for Markdown-only changes and
  Technical Report publication artifacts.

### Fixed

- Recorded that Theorem 4's `n^γ` preservation clause is false as printed and
  exposed only the corrected reached-by-deadline entry theorem.
- Restored and pinned the stable repository Technical Report PDF to the exact
  `arXiv:2607.13531v2` revision.
- Updated the AAE statement to record that v2 removed an earlier incorrect
  criticism of the published proof.

### Removed

- Excluded private work logs, model transcripts, task specifications,
  scratch files, generated objects, and six orphaned experimental Lean
  modules from the public snapshot.

### Verification

- The `Tri` audit reports zero `sorry`, `admit`, `unsafe`, custom axiom
  declarations, and `native_decide` uses.
- Every audited `Tri` declaration depends only on `propext`,
  `Classical.choice`, and `Quot.sound`, or on no axioms.

### Documentation

- Added a public `Tri` guide and linked the checked errata PDF and LaTeX
  source.
- Distinguished the live repository from the fixed 21 July 2026 Technical
  Report snapshot and linked changelog and release records for later work.
