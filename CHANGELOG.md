# Changelog

This file records notable public-facing changes to Ripple. See
`MAINTENANCE.md` for entry criteria, version namespaces, and the release
procedure.

## [Unreleased]

### Added
### Changed
### Fixed
### Removed
### Verification
### Documentation

## [r2026.11] — 2026-11-08

This release restates Ripple's computability predicates to match the source
papers, re-proves the results built on them, adds the bounded surrogate
compilation theorems of the bounded analog complexity paper, removes every
`native_decide`, and renames and reorganizes the library. Code that imports
Ripple needs the rename map `docs/refactor/RENAMES.tsv`. Long-form notes are
in `RELEASE_NOTES.md`; a correction to the Technical Report is in
`paper/ERRATA.md`.

### Added

- Bounded surrogate compilation from the bounded analog complexity paper
  [BAC]: Construction 3.1, Proposition 3.2, Theorems 3.3 and 3.4, Lemmas 4.1
  and 4.3, and Theorems 4.5 and 4.6. One time change `dt/dτ = 1/P(y)` with
  the joint clock `P = 1 + Σᵢ yᵢ^N` and the surrogates `y^a/P` (`|a| ≤ N`)
  turns a ℚ-PIVP whose output converges to `α` into a bounded ℚ-PIVP that
  computes `α`: `bounded_compilation`, `bounded_compilation_certified` and
  `isGPACComputable_iff_isCRNComputable`. A finite blow-up time is computable
  (`isCRNComputable_blowupTime`), and a solution that blows up keeps its
  output limit (`bounded_compilation_of_blowup`). The arc-length bounds are
  `PolyPIVP.arcLength_le_of_bounded` and `PolyPIVP.abs_sub_init_le_arcLength`.
  With polynomial time and length the compiled modulus is polynomial
  (`bounded_compilation_polyTime`, `bounded_compilation_polyTime_certified`);
  the product clock `Πᵢ (1 + yᵢ^N)` gives compiled dimension `1 + d(N+1)`
  (`bounded_compilation_productClock_polyTime_certified`). New modules
  `Ripple/Core/TimeChange.lean`, `ArcLength.lean`, `SurrogateCompilation.lean`,
  `SurrogateCompilationBlowup.lean` and `ProductClockCompilation.lean`;
  `SurrogateCompilationExamples.lean` instantiates the theorems on unbounded
  inputs (`arctan`, a Gaussian, and the `tan` pole). The paper proofs, with
  the repairs of the printed proofs, are in `docs/refactor/BC.md`.
- A faithful large-population-protocol layer following Definitions 5, 6 and
  9 of the large-population protocol paper [LPP]: deterministic computations
  (`LPPComputation`, `IsLPPComputable`) and probabilistic ones
  (`PLPPComputation`, `IsPLPPComputable`), with
  - the compiler from certified CRN computations to protocols, the [LPP] Main
    Theorem in the GPAC-to-LPP direction (`isPLPPComputable_of_certified`,
    `isLPPComputable_of_certified`, `bounded_crn_is_lpp_computable`,
    `bounded_crn_is_plpp_computable`), and its converse (`lpp_to_gpac`,
    `plpp_to_gpac`);
  - [LPP] Theorem 17, a PLPP with rational probabilities is simulated by a
    deterministic LPP (`IsPLPPComputable.isLPPComputable`,
    `isLPPComputable_iff_isPLPPComputable`);
  - [LPP] Lemma 10, unimolecular protocols compute exactly the rationals
    (`isLPUPComputable_iff_rat`); Lemma 11, products (`IsPLPPComputable.mul`,
    `lpp_product`); Corollary 18, algebraic numbers in `[0, 1]`
    (`algebraic_lpp_computable`, `algebraic_plpp_computable`); and the
    Corollary 19 numbers `π/4`, `1/e`, `ln 2`, Catalan's constant and the
    Dottie number (`pi_quarter_is_lpp_computable`, `inv_e_is_lpp_computable`,
    `ln2_is_lpp_computable`, `catalan_is_lpp_computable`,
    `exists_dottie_lpp`); Ehrenfest urns as protocols
    (`IsEhrenfestComputable.isLPPComputable`).

  The steps of the compiler that the paper does not spell out, and the proof
  of Theorem 17 for the continuum-of-equilibria definition, are in
  `docs/refactor/S1-LPP-PAPER.md` and `docs/refactor/S1-THM17.md`.
- The real-time GPAC class `R_RTGPAC` of the real-time equivalence paper
  [RTCRN2] (`IsRTGPACComputable`: zero initial values, integer coefficients,
  error at most `2^{-t}` for `t ≥ 1`) and its equality with
  `IsRealTimeComputable` (`isRealTimeComputable_iff_rtgpac`).
- The Φ₄₁ Sturm certificate halved through the Fricke involution: modules
  `Phi41Fricke` (the transformation law under `S` and
  `levelGamma0_41_sturm_weight_1008_of_S`), `Phi41FrickeSturm`, and
  `Phi41SymmCheck` (the `X ↔ Y` symmetry of Φ₄₁). The proof is written out in
  `docs/refactor/FRICKE.md`.
- Class number one for discriminant −163 over all reduced forms
  (`eq_of_isReducedPositiveFormOfDiscriminant_neg163`, in
  `CMEvaluation163`).

### Changed

- **Computability predicates (breaking).** `IsCRNComputable`,
  `IsRealTimeComputable` and `IsPolyTimeComputable` now require a
  `CertifiedBoundedTimeComputable` witness: a bounded PIVP with a ℚ-polynomial
  vector field and a ℚ initial value with a time modulus, as in Definitions
  2.1 and 2.3 of [BAC]. In r2026.08 they were defined over the semantic
  record, whose field was an arbitrary function and whose initial value was
  an arbitrary real, so each held for every real number. `IsLPPComputable`
  is now the deterministic clause of [LPP] Definition 9, with
  `IsPLPPComputable` beside it; in r2026.08 it was a structure with an
  unrestricted vector field and held for every `ν ∈ [0, 1]`. The semantic
  record `BoundedTimeComputable` is renamed `SemanticBTC` and is
  infrastructure only. The results stated with these predicates are restated
  and re-proved: closure of the real-time class under the field operations
  (`realtime_field_add`, `_mul`, `_neg`, `_sub`, `_inv`, `_div`) and of the
  CRN-computable class under sums and products (`crn_computable_add`,
  `crn_computable_mul`); `e`, `π`, `ln 2`, Euler's `γ` and Catalan's constant
  real-time (`euler_is_realtime`, `pi_is_realtime`, `ln2_is_realtime`,
  `euler_gamma_is_realtime`, `catalan_is_realtime`); and the LPP results
  listed under Added. `paper/ERRATA.md` records what this means for the
  Technical Report.
- **Names and module paths (breaking).** Declaration, namespace and module
  names now state what a result is; names that recorded how or when a result
  was produced (`_unconditional`, `_v2`, `Discharge`, `Capstone`, step
  numbers, ...) are renamed, and `Aprey` is spelled `Apery`. About 2,400
  declarations, 610 modules and 120 namespaces that existed in r2026.08 are
  renamed; `docs/refactor/RENAMES.tsv` maps each old name to its new one.
  `Ripple/PopulationProtocol/Majority/` is flattened: `ExactMajority`,
  `SSEM`, `PopProto` and `PopProtoCommon` live directly under
  `Ripple/PopulationProtocol/`, with namespaces under
  `Ripple.PopulationProtocol`. `Ripple.Frobenius` is
  `Ripple.Number.Frobenius`; `Tri.Lazy` is `Ripple.Probability.LazyStep`.
  Where a conditional and an unconditional form shared a stem, the plain name
  is now the unconditional statement: `bounded_crn_is_lpp_computable` (formerly
  `bounded_crn_is_lpp_computable_unconditional`), `Tri.Multi.lemma12`
  (formerly `lemma12_unconditional`; the conditional form is
  `lemma12_of_speciesGrowth`) and `modular_poly_41_vanishes_on_diagonal_cm163`.
- **Trust footprint.** Ripple no longer uses `native_decide` (66 uses in 37
  files at the refactor baseline; 0 now). The level-41 Sturm certificate for
  Φ₄₁ is checked by the Lean kernel through a Kronecker-packed big-integer
  computation (`SturmPacked`, `SturmPackedEval`). With the Fricke involution
  the kernel checks the first 1765 coefficients of the cleared Φ₄₁ form
  instead of 3529; `SturmPackedEval` takes about 20 seconds and 2.5 GB. The
  3529-coefficient statements `phi41Level41SturmCoefficientCertificate_proof`
  and `phi41Level41RecurrenceCoeffArrayFirstZero_sturmBound` keep their types
  and now follow from the vanishing of the form; they moved from
  `ModularPolynomialSturmCertificate` to `Phi41FrickeSturm`. The 26
  `native_decide` checks of `LPP/ExampleGammaCompiled.lean` are replaced by
  structural proofs and small kernel decisions. The CM-163 evaluation and the
  other modular-forms statements keep their types.
- **Proof budgets.** File-level `maxHeartbeats` raises (20 before) and scoped
  raises above four times the default (745 before) are gone; each remaining
  raise is at most four times the default and records its measured
  heartbeat count.
- **Build envelope.** Twenty-six `import Mathlib` lines are narrowed to the
  modules actually used, which lowers the per-module import floor from about
  6.4 GiB to 1.9–3.5 GiB, and the heaviest modules are restructured. A
  from-scratch build fits in 16 GB of memory: see Verification.
- Build targets: the default Lake build checks the `Ripple.lean` import
  closure (549 modules) and all of `Tri`; the exhaustive `Ripple` target
  compiles all 1028 Ripple modules, including the kernel-checked Sturm
  certificate, the CM-163 evaluation, both Turing-completeness developments
  and the number modules outside the default closure. The opt-in `SturmCRT`
  target is gone (see Removed).

### Fixed

- `bounded_compilation` is a theorem again, now with a proof that uses its
  premise. In r2026.08 its proof went through the placeholder
  `realtime_const`, which proved every real real-time computable, and did not
  use the hypothesis.
- ExactMajority phase-entry initialization: Phase-3 Clock agents receive
  their settling counter, Phase-5 Reserve agents clear their sample, and
  Phase-4 advancement executes the destination Init; the dependent invariant
  and phase-progress proofs are restored.
- Five standalone modules outside the default build failed to compile at
  r2026.08 (`LPP.ExampleGamma`, `LPP.CasselsElementary`,
  `Number.Frobenius.AperyGeneratingFunction`, SSEM `EvenCRS`, and
  PopProtoCommon `AbsorbedKernel`), so the exhaustive `lake build Ripple`
  target did not complete; they compile now.
- Docstrings of the CM-163 class-number lemmas that cover only forms with
  `a = 1` now say so; the statement for all reduced forms is added above.
- The `Tri` errata no longer cite two declarations of a superseded proof
  route that was removed, and use the renamed `Tri.Multi.lemma12`.
- Removed the redundant API-documentation deployment from Lean CI; code
  pushes report the Lean build result directly.

### Removed

- `realtime_const`, which is false for the faithful predicate; the true
  statement is `realtime_rat_const`.
- `IsCertifiedCRNComputable`, `IsCertifiedRealTimeComputable` and the other
  `IsCertified*` predicates, now merged into the predicates above.
- The real-coefficient LPP routes `stage1_quadraticization`,
  `stage2_to_lpp_*`, `tpp_to_lpp*`, and the interior and sharp-bound
  variants of `bounded_crn_is_lpp_computable` and `algebraic_lpp_*`, whose
  conclusions used the former `IsLPPComputable`; the duplicates
  `lpp_computable_mul` (duplicate of `lpp_product`) and
  `closure_exponentiation` (duplicate of `closure_exponentiation_via_exp_log`);
  `bounded_compilation_rat`, whose premise was unused;
  and `time_length_equivalence`, whose conclusion restated its two
  hypotheses (the length bound is `PolyPIVP.arcLength_le_of_bounded`).
- The `native_decide` Sturm/CRT route: the exact recurrence-array check, the
  251-prime CRT reconstruction (`SturmCertificateCRT`, its 32 batches,
  `SturmCRTModNat`, `SturmCRTPrimeList`, `SturmCRTData3533`) and the opt-in
  `SturmCRT` Lake target, including the bounded-residue evaluation added to
  that route after r2026.08.
- Modules that no stated result uses: 23 superseded proof-route modules of
  the tri-molecular formalization, the deterministic-state race-law route of
  the stochastic CRN simulation (`PropensityRace`, `MultiStepRace`,
  `ClockErrorModel`), the placeholder `Ripple.Number.Apery` (the ζ(3)
  construction is `Ripple.Number.AperyFermi`), and the retired
  `_deprecated/` directory and scratch files.
- 255 forwarding wrappers whose statement equals their target, and 39
  declarations whose statement was `True`.

### Verification

- The source contains no `sorry`, `admit`, `axiom` declaration or
  `native_decide`.
- `#print axioms` on each restated or added headline declaration reports only
  `propext`, `Classical.choice` and `Quot.sound`.
- From a clean tree with Mathlib from the cache, the refactored library
  (1464 modules, measured before the predicate and compilation work above
  was added) built in a 16 GB memory limit on one CPU node in 49.9 minutes
  with 8 compile threads and in 29.2 minutes with 16, with no out-of-memory
  kill. Every probed module stays within 3.87 GiB of its import floor; the
  largest peak is 7.15 GiB (`LPP.EhrenfestUrn`).
- Canonical build of the release tree on one NERSC Perlmutter CPU node, with
  Mathlib from a prebuilt cache and Ripple and `Tri` compiled from scratch
  with 64 compile threads: `lake build Ripple RippleDefault Tri` completed
  successfully (5480 jobs; 1028 Ripple and 447 `Tri` modules) in about 34
  minutes of build time, split over two 30-minute jobs (the second resumed
  incrementally), with no error and no `sorry`. `#print axioms` on 63
  headline declarations named under Added and in `paper/ERRATA.md` reports only
  `propext`, `Classical.choice` and `Quot.sound`.

### Documentation

- The README describes the release head. The Technical Report
  (`arXiv:2607.13531v2`) moves to a Publications section as a historical
  snapshot, and `paper/ERRATA.md` corrects its statements about LPP
  computability and records four further claims that the cited
  declarations do not establish (the almost-sure and CLT versions of Kurtz's
  theorem, the bounded-error stochastic simulation of Soloveichik et al., the
  state count of the Doty et al. protocol, and the time and space bounds of
  the Kanaya et al. protocol).
- The README's descriptions of the Kurtz, Turing-completeness, majority,
  zero-initialization, ζ(3) and Cassels results are checked against the
  release and now state what each headline declaration proves, including its
  hypotheses; the r2026.08 README overstated several of them. The [LPP]
  title in the bibliography is corrected.
- Paper notes for the new proofs (`docs/refactor/BC.md`, `FRICKE.md`,
  `S1-LPP-PAPER.md`, `S1-THM17.md`, and the definition notes in `S1.md`),
  cited by section from the Lean docstrings, and the rename map
  `docs/refactor/RENAMES.tsv`.
- `OPEN_PROBLEMS.md` follows the new statuses: bounded surrogate compilation
  is formalized; exponentiation closure ([BAC] Theorem 6.1) and real-time
  ζ(3) remain conditional.
- The `Tri` errata PDF is rebuilt from its updated LaTeX source.

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
