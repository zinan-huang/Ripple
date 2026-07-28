# Changelog

This file records notable public-facing changes to Ripple. See
`MAINTENANCE.md` for entry criteria, version namespaces, and the release
procedure.

## [Unreleased]

### Added

- Restored the stable repository Technical Report PDF path with the exact
  `arXiv:2607.13531v2` file.

### Changed

- Avoided running the full Lean CI workflow for Markdown-only pushes and pull
  requests.
- Avoided running the full Lean CI workflow for Technical Report publication
  artifacts under `paper/`.

### Fixed

### Removed

### Verification

### Documentation

- Pinned Technical Report links and citation guidance to the corrected
  `arXiv:2607.13531v2` revision.
- Updated the AAE errata statement to record that v2 completed the report
  correction and superseded v1.
- Clarified that the Technical Report is a fixed research snapshot while the
  repository continues to evolve.
- Separated Ripple release versions from Lean compatibility tags and added
  public maintenance guidance for future releases.
- Removed the remaining direct v1 report link from current public
  documentation.
