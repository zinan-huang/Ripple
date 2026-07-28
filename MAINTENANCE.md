# Ripple Public Maintenance and Publication Policy

This file is normative for human maintainers and LLM agents working on the
public Ripple repository. Read it completely before importing development
changes, editing Technical Report links, or updating `CHANGELOG.md`,
`RELEASE_NOTES.md`, tags, or GitHub Releases.

## Repository role and history boundary

`zinan-huang/Ripple` is a curated public publication repository. Ongoing
development occurs in a separate private canonical repository. GitHub
visibility is a repository-level property, so a private development branch
must not be placed in this public repository.

- Treat the existing public `main` ancestry as the only valid base for public
  updates.
- Never merge or push a private development branch into the public lineage.
  A push publishes all history reachable from the pushed branch, not just its
  current file tree.
- Import only files or patches that are completely suitable for publication.
- Before every push, inspect the complete diff for internal notes,
  credentials, generated artifacts, large files, and non-public terminology.
- Never force-push without explicit authorization.

## Technical Report policy

The Technical Report is a versioned research publication, not a live manual
for the repository. It describes a historical project snapshot and is not
expected to change whenever the code gains a theorem, proof, refactor, or new
formalization thread.

The current report is:

- Ho-Lin Chen and Xiang Huang, *Ripple: An Open, AI-Formalized Lean 4
  Framework for Computing with CRNs*.
- Exact version: `arXiv:2607.13531v2`.
- Revision date: 2026-07-21.
- URL: <https://arxiv.org/abs/2607.13531v2>.

No exact repository commit was recorded for v2. Do not invent one
retroactively. For every future report revision, audit a public repository
commit first and record that exact commit or an annotated `report-vN` tag in
both the report and this file.

### Preventing report staleness from misleading readers

The public README must distinguish the report from the live repository:

1. Display the exact report version and revision date.
2. State that the report is a snapshot and that the repository continues to
   evolve.
3. Link to `CHANGELOG.md` and GitHub Releases for post-report changes.
4. While the report accurately describes the current public release, it may
   remain prominent near the top of the README.
5. Once a public release contains material results not covered by the report,
   move the report link to a `Publications` or `Documentation` section and
   label it explicitly as a historical snapshot.
6. Do not revise the report for ordinary code growth. Submit a new report
   version only for a substantive scientific revision, a correction, or a
   deliberately chosen new archival snapshot.

A post-report change is material if it adds or removes a headline theorem or
formalization pillar, changes the trust footprint, corrects a claim made in
the report, materially changes the public API or build requirements, or makes
the report's overview substantially incomplete. Helper lemmas, proof
refactors that preserve the public theorem, performance work, and other
implementation-only changes do not by themselves make the report materially
stale.

New code belongs in the changelog and release notes. An error in a published
report belongs in an erratum and, when appropriate, a new report revision. Do
not use an erratum to announce later repository features.

The README describes the current public head and must be verified against that
head. It must not copy claims from the report under the assumption that they
remain current.

## Documentation roles

Each document has one job:

| Document | Role | Update cadence |
|---|---|---|
| `MAINTENANCE.md` | Normative public maintenance and publication policy | Whenever shared maintenance policy changes |
| `README.md` | Current public status, entry points, trust footprint, and report-snapshot notice | Every public release and whenever a public claim changes |
| `CHANGELOG.md` | Concise public-facing changes since the last Ripple release | Continuously under `Unreleased`; finalized at release time |
| `RELEASE_NOTES.md` | Long-form, frozen explanations of tagged Ripple releases | Once per substantial Ripple release |
| GitHub Release | Published snapshot summary tied to a Ripple release tag | Once per Ripple release; edit only to correct errors |
| Technical Report | Scholarly narrative for an audited historical snapshot | Only for substantive report revisions |

Internal work logs, checkpoints, and session notes are not substitutes for a
public changelog and must not be published as current release documentation.

## Version namespaces

Keep the three version streams visibly distinct:

| Namespace | Example | Meaning |
|---|---|---|
| Report revision | `arXiv:2607.13531v2` | Version of the Technical Report |
| Ripple release | `r2026.07`, `r2026.07.1` | Curated public repository snapshot |
| Lean compatibility tag | `v4.30.0` | Commit using a particular Lean toolchain |

Use calendar versions prefixed with `r` for Ripple releases. Do not call a
repository release simply `v2`, which could be confused with the report, and
do not use Lean's version number as Ripple's project version.

The `lean-release-tag` workflow may create Lean compatibility tags. Keep
`do-release: false` so those tags do not automatically become Ripple GitHub
Releases. Existing historical tags need not be rewritten; label any existing
Lean-version Release as a toolchain compatibility snapshot.

## Changelog policy

`CHANGELOG.md` uses this compact structure:

```markdown
## [Unreleased]

### Added
### Changed
### Fixed
### Removed
### Verification
### Documentation
```

Add an entry for:

- a new public theorem, formalization pillar, or supported use case;
- a change to a public definition, theorem name, module path, or build
  requirement;
- a correction to a theorem statement, proof route, public claim, or
  attribution;
- a change in `sorry`, named-axiom, `native_decide`, generated-certificate, or
  other trust-footprint status;
- a removed or materially rewritten public feature; or
- a documentation change that affects how readers interpret or cite Ripple.

Do not add an entry for:

- every helper lemma or proof-search checkpoint;
- mechanical formatting or routine refactors with no public effect;
- agent names, model names, session narration, or internal task identifiers;
  or
- experiments and notes not included in the public snapshot.

Write entries from the reader's perspective. Prefer one result-level bullet
over a list of implementation commits. Git history already records commit
details.

## Release procedure

For a curated public release:

1. Fetch the current public `main` and identify the previous Ripple release
   tag.
2. Select the intended public scope.
3. Run the canonical full build and targeted checks required by the changed
   pillars.
4. Audit `sorry`, named axioms, `#print axioms` results, `native_decide`,
   generated certificates, and other trust assumptions.
5. Update the README to describe the actual release head. Reassess whether
   the Technical Report is still current enough to remain prominent.
6. Promote `Unreleased` in `CHANGELOG.md` to
   `rYYYY.MM[.N] — YYYY-MM-DD`, then create a fresh `Unreleased` section.
7. Add or update a long-form section in `RELEASE_NOTES.md` only when the
   release needs more explanation than the changelog.
8. Inspect the complete public diff for accidental internal material.
9. Commit and push the public lineage without force.
10. Create an annotated `rYYYY.MM[.N]` tag and a GitHub Release whose summary
    matches the finalized changelog section.
11. Record the release tag or commit as the base for the next synchronization.

README edits, changelog finalization, tagging, and the GitHub Release are one
publication operation. Do not leave them in contradictory states.

## Mandatory checks for LLM agents

Before any maintenance or publication action, an LLM agent must:

- confirm that it is operating on the public lineage;
- read this file completely;
- verify all report, tag, commit, theorem, build, and trust-footprint claims
  from the repository or a primary source;
- keep report revisions separate from repository releases and Lean tags;
- preserve the sanitized public ancestry;
- avoid publishing internal notes or terminology; and
- stop rather than guess if the intended public scope or publication boundary
  cannot be derived safely.
