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

## [r2026.11.8] — 2026-11-14

A maintenance release: identifiers and comments renamed to use "genuine", the Doty et al.
errata note without an author line, and the Tri errata rebuilt from the current source. No
mathematics changes; no module is added or removed.

### Changed
- Identifiers renamed to use "genuine" (old → new pattern in `docs/refactor/RENAMES.tsv`).
  Renamed public declarations:
  - `Tri.Byzantine.GenuineXConsensus` (definition);
  - `Ripple.PopulationProtocol.ExactMajority.Phase7ClassMassDrain.phase7GenuineDrain` (definition);
  - the structure field `genuine` of `Phase1ReadySurvival.Phase1DrainReady`,
    `Phase1SymmetricDrain.Phase1AdaptiveReady`, `Phase678ReadySurvival.Phase7DrainReady`,
    `Phase678ReadySurvival.Phase8DrainReady`, `Phase7BandDefs.Phase7StageReady` and
    `LateBiasedResourceCreditPath.PhaseSevenBandConsumer` (all under `Ripple.PopulationProtocol.ExactMajority`);
  - the structure field `to_genuine` of `Phase678ReadySurvival.Phase6PostToPhase7Ready`,
    `Phase678ReadySurvival.Phase7PostToPhase8Ready` and `Phase6To7Bands.Phase6To7BandEntry`.
  Comments, docstrings, `docs/refactor/RENAMES.tsv` and `WORK_LOG.md` use the same wording.
  Statements and proofs are unchanged.
- [`docs/doty/ERRATA.pdf`](docs/doty/ERRATA.pdf) (and its source) has no author line.
- `MAINTENANCE.md` step 9: the public release commit is an ordinary `git commit` with the
  repository hooks.

### Fixed
- [`docs/tri/Errata_and_Counterexamples.pdf`](docs/tri/Errata_and_Counterexamples.pdf) was
  built from an August 2026 version of `docs/tri/ERRATA.tex`. It is rebuilt from the current
  source, which corrects the creation-tolerance diagnosis and its table (the Chernoff exponent
  is of the claimed order at the lower end of the range and loses it only as `Δ` grows
  relative to `√(γ n lg n)`), the parity explanations for Corollary 2 and Lemma 6 and the
  `min`/`max` entry, adds the reversed ratio step of Lemma 6, and cites the proved Lemma 11
  mode bounds.

### Verification
- Canonical build of the release tree on one NERSC Perlmutter CPU node (job 61278629):
  `Ripple`, `RippleDefault` and `Tri` from scratch, 10880 jobs, build completed, no error, no
  `sorry`; all 1950 Ripple modules and 451 `Tri` modules built. No `sorry`, no named `axiom`
  and no `native_decide` in the source. `#print axioms` of the 41 headline declarations of
  r2026.11.7, including `exact_majority_theorem_three_one` and
  `exact_majority_stabilization_time`, prints only `propext`, `Classical.choice` and
  `Quot.sound`.

### Documentation
- README, `RELEASE_NOTES.md` and `OPEN_PROBLEMS.md` updated for this release.

## [r2026.11.7] — 2026-11-14

Theorem 3.1 of Doty et al. becomes one theorem about one protocol, with smaller constants; the
PP-to-NAP construction (from population protocols to non-autocatalytic protocols) is proved
general and formalized; the bounded analog complexity material gains the statements of its
journal version. The paper errata found while formalizing Doty et al. are published. Two
public declarations and one public module are renamed (see Changed). The release adds 38
modules.

### Added
- Doty et al. (FOCS 2021) Theorem 3.1 for one protocol
  (`TheoremThreeOne.exact_majority_theorem_three_one`,
  `Ripple/PopulationProtocol/ExactMajority/Probability/TheoremThreeOne.lean`). For every
  `n ≥ 5·2^(2^23)`, the compact protocol `NonuniformMajorityCompact (⌈log₂ n⌉) 256` has at
  most `23 136 960 (⌈log₂ n⌉ + 1)` states, stably computes majority on valid inputs of size
  `n`, and its own stabilization time `T` (in interactions, under the uniform random scheduler
  on the ordered-pair log) satisfies `P(T > 16300 n (⌈log₂ n⌉ + 1)) ≤ 110/n²` and
  `E T ≤ 470 235 n ln n`. Earlier releases proved the state count for the compact protocol and
  the time bound for the flat protocol `NonuniformMajority`; the new theorem runs the compact
  transition directly on the scheduled labels, shows that this run is the encoding of the
  flat run on every log, and bounds its stabilization time by the flat endpoint time `τ_D`.
- `Ripple/PopulationProtocol/ExactMajority/Probability/Calibration.lean`: one scalar
  calibration module for the population threshold and the clock and late-phase constants.
- The PP-to-NAP construction (`Ripple/LPP/NAP*.lean`, 31 modules), at the level of the
  mean-field ODE:
  - protocol-level non-autocatalysis (`NAPProtocol.IsNAP`, `balanceField_conservative`) and an
    explicit 141-reaction NAP for the cubed CF'24 example whose balance field equals the cubed
    field on the Veronese image (`cf24Cubing_isNAP`, `cf24Cubing_eq_napField_on_cubed`);
  - the transportation (supply/demand) construction and the criterion for cubing a syntactic
    quartic protocol `f`: a non-negative NAP realising the cubed field exists when
    `[y³k] f_y ≤ 0` and `[y³k] f_k + 2 [y⁴] f_y ≤ 0` for all species `y ≠ k`
    (`NAPTransport.exists_nap_realizing_of_C1C2`); conversely, a non-negative NAP realisation
    has non-positive demand for `β` at every monomial all of whose splittings contain `β`
    (`realizes_nonpos_of_unique_pair`);
  - the pipeline (slack trick, r²-trick, cubing) for every syntactic quadratic PP
    (`pp_to_nap_ode_of_init`): for every species `j₀` and `λ ∈ (0, 1)` there is a non-negative
    NAP such that from every simplex point with `x_{j₀}(0) > 0` its unique solution is the
    Veronese image of the time-changed PP trajectory, with an explicit clock `τ → ∞`, the same
    readout limit and, when `x_{j₀}` has a positive limit, the exponential rate transferred;
    the shrunk-set version `pp_to_nap_ode_of_init_set`;
  - the cheaper squaring variant as an equivalence (`exists_nap_realizing_sq_iff`,
    `squaring_iff`) and its 10-species CF'24 instance (`cf24_squaring`, `cf24_sq_of_init`);
  - normal stability with exchange reactions: at every equilibrium of the simplex, interior
    (`normal_stability_interior`) or on the boundary (`normal_stability_boundary`), there is
    `K₀` such that for every exchange rate `K > K₀` the spectrum of the NAP at the lifted
    equilibrium is the spectrum of the quartic protocol plus eigenvalues of negative real part
    (`hurwitz_simplex_iff_boundary`; non-vacuity `boundary_hypotheses_nonvacuous`);
  - `{0, 1}` readouts: a marked set of cubic species whose mass is the cube of the original
    marked mass (`pp_to_nap_marked_cube_of_init_set`), the obstruction that no fixed
    `{0, 1}` subset of the cubic species reads the original marked mass on the whole simplex
    (`MarkedObstruction.no_marked_readout_on_simplex`), and three layer copies that read the
    original number with the original clock (`LayerCopy.pp_to_nap_layer_copy_of_init`,
    with the exact exponent in `LayerCopy.pp_to_nap_layer_copy_exact`).
- Bounded analog complexity, statements of the journal version (`Ripple/Core/`): unique
  maximal forward solutions of polynomial IVPs and blow-up at a finite endpoint
  (`MaximalPIVP.exists_maximal`, `MaximalSolution.unique`), the complete time change from a
  maximal solution, and computability of a finite maximal lifetime
  (`MaximalPIVP.isCRNComputable_maximalTime_certified`); the exact clock modulus retained in
  the polynomial-time certificate (`bounded_compilation_polyTime_clock_certified`,
  `BACJournalStrong.lean`); selective dual rail with one retained output species
  (`SelectiveDualRail.exists_solution`, `rpow_selective`); general subset compilation with
  evolving retained coordinates (`SubsetCompilation.subsetCompile_of_maximal_limits`); and the
  power trajectory, the BFK cyclic protocol, the shifted clock and the product clock
  (`BACJournalRemarks.lean`, e.g. `powCurve_global_unique`).
- [`docs/doty/ERRATA.pdf`](docs/doty/ERRATA.pdf) (source `ERRATA.tex`): errata for Doty et al.,
  arXiv:2106.10201v2, found during the formalization, written for the authors.

### Changed
- Renamed, because the paper has six authors and names should describe the result
  (old → new in `docs/refactor/RENAMES.tsv`):
  - module `Ripple.PopulationProtocol.ExactMajority.Probability.DotyStabilizationTime` →
    `…Probability.StabilizationTime`;
  - `DotyStabilizationTime.doty_stabilization_time` →
    `StabilizationTime.exact_majority_stabilization_time`;
  - `TimeTheorem.DotyTimeClaim` → `TimeTheorem.StabilizationTimeClaim`;
  - `TimeTheorem.dotyTimeClaim_of_estimates` → `TimeTheorem.stabilizationTimeClaim_of_estimates`.
- `exact_majority_stabilization_time` (formerly `doty_stabilization_time`) holds with smaller
  constants: population threshold `5·2^(2^41)` → `5·2^(2^23)`, high-probability horizon
  `23000 n (⌈log₂ n⌉ + 1)` → `16300 n (⌈log₂ n⌉ + 1)` interactions (failure probability still
  `110/n²`), expectation `24 807 000 n ln n` → `470 235 n ln n`; the uniform recovery budget
  from a reachable configuration drops from `30700 n³ (⌈log₂ n⌉ + 1)` to
  `700 n³ (⌈log₂ n⌉ + 1)`. Every probability statement keeps its form; only numerical
  premises weaken.
- Comments in `Ripple/PopulationProtocol/ExactMajority/` say "Doty et al." where they said
  "Doty".

### Fixed
- Two docstrings (`PaperRegime.lean`, `UsefulMainFloor.lean`) listed Xu instead of
  Stachowiak among the authors of Doty et al.; the README reference list and the r2026.11.6
  release notes listed Viglietta instead of Stachowiak. The README is corrected; the frozen
  r2026.11.6 release notes are not edited, and this entry records the correction.
- Errata for the paper of Doty et al. are added to [`paper/ERRATA.md`](paper/ERRATA.md): two
  printed statements are false as stated (Lemma 5.3 for large gaps; the lower bound of
  Theorem 6.9 for small clock fractions), neither affects Theorem 3.1; the others are proof
  gaps with true statements and typographical or pseudocode slips.

### Removed
- `Ripple/PopulationProtocol/ExactMajority/Probability/DotyStabilizationTime.lean` (renamed;
  see Changed).

### Verification
- Canonical build of the release tree on one NERSC Perlmutter CPU node (job 61266330):
  `Ripple`, `RippleDefault` and `Tri` from scratch, 10880 jobs, build completed, no error, no
  `sorry`; all 1950 Ripple modules and 451 `Tri` modules built. No `sorry`, no named `axiom`
  and no `native_decide` in the source. `#print axioms` of 41 headline declarations, including
  `exact_majority_theorem_three_one`, `exact_majority_stabilization_time`,
  `exists_nap_realizing_of_C1C2`, `pp_to_nap_ode_of_init`, `normal_stability_boundary`,
  `LayerCopy.pp_to_nap_layer_copy_of_init`, `isCRNComputable_maximalTime_certified`,
  `SubsetCompilation.subsetCompile_of_maximal_limits` and the 24 headlines of r2026.11.6
  (`doty_stabilization_time` under its new name), prints only `propext`, `Classical.choice`
  and `Quot.sound`.

### Documentation
- README, `RELEASE_NOTES.md`, `OPEN_PROBLEMS.md` (§4.5 answered; §6.4 updated) and
  `paper/ERRATA.md` updated for this release.

## [r2026.11.6] — 2026-11-14

A substantial release with two new pillars. The O(log n) stabilization time of the
exact-majority protocol of Doty et al. (Theorem 3.1) is proved, in expectation and with high
probability, without hypotheses; with the O(log n) state count of r2026.11.4, Theorem 3.1 is
now formalized in full. Kurtz's 1978 strong approximation theorems are proved under the
paper's hypotheses: Lemma 3.1 (the Poisson–Brownian coupling), Theorem 3.3(a) (the
`O(log N / N)` diffusion approximation) and Theorem 4.4 (the `O(log N / √N)` Gaussian
approximation, with the covariance of the Gaussian limit). Underneath them is a new
stochastic-calculus library (`Ripple/Stochastic/`). The release adds 744 modules.

### Added
- Doty et al. (FOCS 2021) Theorem 3.1, stabilization time
  (`DotyStabilizationTime.doty_stabilization_time : TimeTheorem.DotyTimeClaim`,
  `Ripple/PopulationProtocol/ExactMajority/Probability/DotyStabilizationTime.lean`; no
  hypotheses). For the formalized protocol `NonuniformMajority` with `L = ⌈log₂ n⌉` and
  `K = 256`, for every population size `n ≥ 5·2^(2^41)` and every valid input configuration
  of size `n`, the number `τ_D` of interactions until the configuration first reaches a stable
  endpoint with the correct majority output (`StableDone`; `stable_output_of_majorityStableEndpoint`)
  satisfies `P(τ_D > 23000 n (⌈log₂ n⌉ + 1)) ≤ 110/n²` and `E τ_D ≤ 24 807 000 n ln n`, that
  is, O(log n) parallel time with high probability and in expectation. The population
  threshold is explicit but astronomically large; the constants are those of the
  formalization (timer `50(L+1)`, `K = 256`), not the paper's unspecified `c_k`. The proof runs
  under the original uniform random scheduler on the ordered-pair log and composes phase
  estimates proved in Lean: Phases 0–2 entry (`phase_zero_two_entry_estimate`, `2/n²`), the
  asynchronous Phase-3 clock from the first Phase-3 seed (`asynchronous_clock_estimate`,
  `8/n⁵`), Phase-3 averaging (`averaging_estimate`, `3/n²`), the late phases on the small-gap
  branch (`smallGap_late_estimate`, `100/n²`, Lemmas 10–14 of the paper), the strong-gap and tie
  continuations (`strong_continuation_estimate`, `tie_continuation_estimate`), and a
  recovery bound from every reachable configuration for the expectation
  (`reachable_recovery_estimate`).
- Kurtz (1978), Lemma 3.1 (`KurtzLemmaThreeOne.kurtz_lemma_three_one`,
  `Ripple/Kurtz/StrongApprox/KurtzLemmaThreeOne.lean`): on one probability space, a standard
  Brownian motion `W` (continuous paths, Brownian on every dyadic horizon) and a unit Poisson
  process `Y` (unit jumps a.s., independent Poisson increments on every finite grid) such that
  `K = sup_{t ≥ 0} |Y(t) − t − W(t)| / (log t ∨ 2)` is finite a.s. and has an exponential
  moment `E exp(λK) < ∞` for an explicit `λ > 0`. The coupling is the dyadic
  Komlós–Major–Tusnády construction for the Poisson process, built from Binomial–normal and
  Poisson–normal quantile couplings (Serov–Zubkov intersection inequalities), with the
  finite-horizon form `continuousTime_arbitraryFiniteHorizonKMT` and the coarse-block strong
  invariance principle `discrete_sip`.
- Kurtz (1978), Theorem 3.3(a) (`KurtzTheoremThreeThree.kurtz_theorem_three_three_a`, and
  `kurtz_theorem_three_three_a_identicalLaw` for the printed form): on the product of
  independent Lemma 3.1 spaces, one per channel, continuous solutions `Z_N` of the diffusion
  equation (1.6) exist for every sample, and for every such family there is one measurable
  `β^T ≥ 0` with an exponential moment such that, almost surely,
  `‖X_N(t) − Z_N(t)‖ ≤ β^T log N / N` for all `N ≥ 2` and `t ≤ T` at once. Hypotheses: (3.1),
  (3.2), (3.19), measurable `f^N`, finitely many channels; arbitrary (random) initial states;
  no path-regularity premise.
- Kurtz (1978), Theorem 4.4 (`kurtz_theorem_four_four`,
  `Ripple/Kurtz/StrongApprox/KurtzTheoremFourFour.lean`) from the paper's Section 4 hypotheses
  only (the record `SectionFourPaperData`: (3.1), (3.2), the summed square-root condition,
  bounded first and second coordinate partials of the drift, finitely many channels): on one
  coupling space, the chains (1.3) for every `N ≥ 2` with the original rates, the fluid limit
  `X`, strong solutions of (1.7), one centered Gaussian process `V` solving its linear
  equation, and for every `T` measurable `γ_N^T ≥ 0` with a uniform exponential moment such
  that, almost surely, `‖√N (X_N(t) − X(t)) − V(t)‖ ≤ γ_N^T log N / √N` for all `N ≥ 2` and
  `t ≤ T` at once. `kurtz_theorem_four_four_covariance` adds the covariance
  `Cov(⟨a, V t⟩, ⟨b, V u⟩) = ∫_0^{t∧u} ⟨a, Φ(t,s) Σ(X s) Φ(u,s)ᵀ b⟩ ds` with `Φ` the fundamental
  matrix of `DF(X(·))` and `Σ(x) = Σ_l f_l(x) v_l v_lᵀ`. Non-vacuity:
  `kurtz_theorem_four_four_paper_witness` instantiates the hypotheses with a state-dependent
  rate (two channels, rates `2 + sin x` and `2`).
- A stochastic-calculus library (`Ripple/Stochastic/`): the L² Itô integral for a Brownian
  motion adapted to a general filtration (`FilteredItoIntegralCLM`, isometry
  `itoIntegralCLM_T_norm`), its continuous version on every horizon and on the half-line
  (`ContinuousItoConstruction`, `AllTimeIto`), stopping, and Doob's maximal inequalities
  (`MeasureTheory.maximal_ineq_Lp` in discrete time; `Doob.lintegral_iSup_sq_le_of_martingale`,
  `E sup_{t≤T} |M_t|² ≤ 4 E |M_T|²` for right-continuous martingales).
- Also in `Ripple/Stochastic/`: the exponential maximal inequality
  `P(sup_{t≤T} M_t ≥ r, ⟨M⟩_T ≤ q) ≤ exp(−r²/(2q))` for continuous `M` whose stochastic
  exponential is a supermartingale (`ContinuousExponentialMaximal.continuous_exponential_maximal`),
  and the exponential martingale proved for limits of bounded elementary Itô integrals
  (`stochastic_exponential_of_bounded_approximation`); strong existence and pathwise
  uniqueness for SDEs with bounded Lipschitz coefficients driven by finitely many Brownian
  motions, on every horizon and on `[0, ∞)` (`StrongSDEGlobal.exists_all_time_solution`,
  `all_time_pathwise_unique`); and Knight's theorem on time changes of continuous martingales
  into independent Brownian motions, in the form used by Theorem 4.4
  (`Knight*` modules, `knightTimeChangeData_nonempty`). The L² Itô integral of formal-mathfin,
  and Brownian motion, Kolmogorov–Chentsov and the Kolmogorov extension theorem of Degenne et
  al., are ported (see `NOTICE`).
- SCWB Turing-machine simulation on the canonical CTMC
  (`Ripple/sCRNUniversality/CTMGlobalNonexplosion.lean`): the clocked CTM network is
  nonexplosive from every finite state (`ctm_noExplosion`), and before the `K`-th clock tick its
  timed mass-action law agrees with the canonical record law of a finite Q-matrix CTMC of
  `Ripple/CTMC/`, with elapsed time equal to the first exit time
  (`ctm_identification_up_to_target`, from `CTMCIdentification.lean`).

### Changed
- CF'24 example: the four readout theorems that assumed `Cf24SaddleExcludedBasinEntry` are
  restated under the corrected hypothesis `Cf24CornerExcludedBasinEntry` (interior, not
  converging to the saddle or to the vertex `(0, 0, 1)`):
  `cf24_step5_readout_of_cornerExcludedBasinEntry`, `cf24_lambda_lifted_…`, `cf24_r2_lifted_…`,
  `cf24_nap20_lifted_readout_of_cornerExcludedBasinEntry` (old names in
  `docs/refactor/RENAMES.tsv`).
- `Ripple/PopulationProtocol/ExactMajority/Probability/ClockDepletionCoupling.lean` no longer
  declares a global discrete σ-algebra instance on `Λ × Λ`, which overrode Mathlib's product
  σ-algebra; `pairTouches_measure_le` now takes `[MeasurableSpace Λ] [DiscreteMeasurableSpace Λ]`.

### Fixed
- The hypothesis `Cf24SaddleExcludedBasinEntry` of the CF'24 readout theorems (in releases up
  to r2026.11.5) is false, so those theorems were vacuous: the vertex `(0, 0, 1)` is a hyperbolic
  sink whose open basin contains interior initial conditions with readout limit `1`
  (`cf24_saddleExcludedBasinEntry_false`, `cf24_corner_readout_tendsto_one`; for example
  `(1/200, 1/200, 99/100)`), `Ripple/LPP/CF24Interior.lean`. The corrected statement (every
  interior trajectory converges to the target equilibrium, the vertex or the saddle) is proved
  on paper in `docs/audit/CF24-INTERIOR.md` by Poincaré–Bendixson with the Dulac function
  `a^(−4/3)`; its two elementary ingredients are in Lean (`cf24_dulac`,
  `cf24_source_repelling`), the planar topology is not.
- Kurtz (1978), remarks on the printed proof of Theorem 4.4, found while formalizing it (paper
  arguments, not formalized): the compensator of the exponential martingale in (4.4) is
  `λ²t/2`, not `λ²t`; and (4.8) cannot hold "for every λ" (a two-channel model with jumps
  `±1` and rates `(2 + tanh x)²/2` violates it for every `λ ≥ 1/(2T)`). The proof of
  Theorem 4.4 needs (4.8) for some `λ > 0` only, which the formalization proves.

### Verification
- Canonical build of the release tree on one NERSC Perlmutter CPU node: `Ripple`,
  `RippleDefault` and `Tri` from scratch (job 61262710), then, after an explicit-binder fix in
  `Ripple/Stochastic/StoppedContinuousIto.lean`, an incremental rebuild of that module and its 17
  dependents (job 61264748): 10842 jobs, build completed, no error, no `sorry`. No `sorry`, no
  named `axiom` and no `native_decide` in the source. `#print axioms` of 24 headline
  declarations, including `doty_stabilization_time`, `kurtz_lemma_three_one`,
  `kurtz_theorem_three_three_a`, `kurtz_theorem_four_four`,
  `kurtz_theorem_four_four_covariance`, `kurtz_theorem_four_four_paper_witness`,
  `cf24_saddleExcludedBasinEntry_false` and `ctm_identification_up_to_target`, prints only
  `propext`, `Classical.choice` and `Quot.sound`.

### Documentation
- `README.md`, `OPEN_PROBLEMS.md` §6.2–6.5 and `paper/ERRATA.md` describe the Doty et al.
  time bound and Kurtz's strong approximation as proved; `RELEASE_NOTES.md` explains both
  pillars. `docs/audit/CF24-INTERIOR.md` is the paper proof of the CF'24 phase portrait.
  `NOTICE` records the ported stochastic-calculus files.

## [r2026.11.5] — 2026-11-11

An incremental release. Theorem 4.1 of Soloveichik, Cook, Winfree and Bruck,
the simulation of Turing machines over unboundedly many steps and unbounded
space, is proved for an explicit network. Theorems 3.1, 3.2, 4.1 and 4.2 of
that paper are now all proved in Lean.

### Added
- SCWB Theorem 4.1 (`ClockedCTM.Unbounded.scwb_theorem_4_1`,
  `Ripple/sCRNUniversality/ClockedCTM/UnboundedClockOccupation.lean`): for a binary Turing
  machine `M` with blank `false`, the network `xctmOf M` depends only on `M`; for every space
  bound `s ≥ 1` and `δ ∈ (0, 1]` the initial count `i₀ = accuracyIndex (2s + 2) δ`
  (at most `2s + 4 + 37/√δ`) of the accuracy species makes the probability that the run fails
  to visit a clean encoding of every configuration of the machine's unbounded run at most
  `1344/(i₀ − 1)² ≤ δ`, for every input of length at most `s`; and `TMTimeClaim M` bounds the
  expected physical time to TM step `t` given no error by
  `552 (s_t + 1) t (37/√δ + 2s + 4 + 6(s_t + 1) t)^5/((1 − δ) ρ κ)` on the chain with
  exponential holding times (`s_t` the tape length at step `t`, `δ < 1`, `t` before the machine
  halts). The network and the
  proof are those of `docs/audit/FIX3-SCWB-T41.md`.
- The general forms for every extensible clocked CTM, `errorClaim C : ErrorClaim C` and
  `timeClaim C : TimeClaim C`, and the TM forms `tm_failure_bound` and `tmTimeClaim`, with the
  layers that prove them: the raw-law window analysis and the occupation comparison of Lemma 8.3
  (`UnboundedWindow.lean`, `UnboundedOccupation.lean`), the time reducers (`UnboundedTime.lean`),
  the work-duration, restart and terminal-clock layer (`UnboundedRestart.lean`), the Markov
  restart of the raw jump law after a deterministic cut (`rawLaw_restartLabels`) with the
  remaining work-phase bounds (`UnboundedMarkov.lean`), and the actual clock occupation with the
  active-window volume bound (`UnboundedClockOccupation.lean`).

### Fixed
- Two readings of the Theorem 4.1 analysis are false and are refuted in Lean with explicit
  witnesses: an occupation bound over all states that includes terminal clock waiting
  (`terminalClockWork_not_all_occupation_le_meanDuration`; terminal clock time is charged
  separately, Lemma 14.4), and the exact restoration ratio during ordinary restoration
  (`ordinary_restore_ratio_strict_between`: the reachable ratio lies strictly between 38 and 39).

### Verification
- Canonical build of the release tree on one NERSC Perlmutter CPU node: `Ripple`, `RippleDefault` and `Tri` from scratch,
  10098 jobs, no error, no `sorry`; the ten new headline declarations above print only `propext`,
  `Classical.choice` and `Quot.sound` under `#print axioms`, and every declaration of
  `UnboundedClockOccupation.lean` prints a subset of these three.

### Documentation
- `README.md`, `OPEN_PROBLEMS.md` §6.2 and `paper/ERRATA.md` (status entries for r2026.11.4 and
  r2026.11.5) describe Theorem 4.1 as proved. The error bound is stated on the embedded jump
  chain; its identification with the Q-matrix CTMC of `Ripple/CTMC/` remains open.

## [r2026.11.4] — 2026-11-10

An incremental release. Kurtz's finite-dimensional central limit theorem and
his law of large numbers with an exponential tail are proved; the state count
of Doty et al. Theorem 3.1 is now O(log n); the SCWB Theorems 3.1 and 3.2 now
include completion and hold on the continuous-time chain with exponential
holding times; a phase-9 defect in the formalized exact-majority protocol is
repaired; and several headline statements are restated in their explicit,
stronger forms. A first, partial formalization of SCWB Theorem 4.1 is
included; its probabilistic part is stated, not yet proved.

### Added
- Kurtz (1971), finite-dimensional central limit theorem for density-dependent CTMCs
  (`Kurtz.kurtz_finite_dimensional_clt`, `Ripple/Kurtz/FluctuationCLT.lean`): under the model
  hypotheses (conservative jumps, boundary compatibility on the simplex, `C¹` drift, bounded
  mean-field solution) and `√N (X_N(0) − x(0)) → v₀`, the vector `√N (X_N(t_j) − x(t_j))_j`
  converges in law to the Gaussian with the linearized mean and covariance; the covariance is
  positive semidefinite. Non-vacuity probe `docs/audit/probes/ProbeKurtzCLT.lean`.
- Kurtz's law of large numbers with an explicit exponential tail, uniform on `[0, T]`
  (`Kurtz.kurtz_finite_horizon_exp_tail`: `P(sup_{t≤T} ‖X̄_N(t) − x(t)‖ > ε) ≤ 2d·e·exp(−cNε²)`
  for `ε ≤ ε₀` and `‖x₀/N − x(0)‖ < ε/K`, with `K = 2e^{LT}`, `c = 1/(4TΛJ²K²)`, `ε₀ = 2TΛJK`),
  the martingale tail `Kurtz.frozen_martingale_exp_tail` and the `√(log N/N)` rate
  `Kurtz.kurtz_finite_horizon_log_rate`, from the record-index exponential martingale of a finite
  CTMC (`QMatrix.integral_mul_cexp_expSum_succ`, `martingale_exp_realExpSum`, Ville's inequality
  `ville_realExpSum`). Paper proofs: `docs/audit/FIX-KURTZ2-FINAL.md`.
- Doty et al. Theorem 3.1, state count: the compact state type `Compact.CompactState L K`
  (one live Θ(L) field per role and phase) with the induced protocol
  `Compact.NonuniformMajorityCompact`, stable correctness transported from the flat theorem
  (`Compact.compact_stable_majority_correct`, `…_clog`) through a state simulation
  (`StateSimulation.stablyComputes`), and `Compact.card_compactState_le : card ≤ 73920 ((K + 53)(L + 1) + 4)`,
  i.e. `≤ 73920 (98 ⌈log₂ n⌉ + 102)` at the paper's parameters (`Compact.compact_state_count_clog`).
  The O(log n) stabilization time remains open (`OPEN_PROBLEMS.md` 6.4).
- SCWB on the continuous-time chain (`Ripple/sCRNUniversality/CTMCBridge.lean`): the law of the
  mass-action CTMC with independent unit exponential clocks (`timedLaw`), whose expected elapsed
  time equals the expected holding-time functional used before (`lintegral_registerElapsed`), no
  explosion before the target (`register_noExplosion_before`), and SCWB Theorems 3.1 and 3.2 on
  that space with their original constants (`scwb_theorem_3_1_timed`, `scwb_theorem_3_1_ctmc_stop`,
  `scwb_theorem_3_2_timed`, `scwb_theorem_3_2_ctm_timed`).
- SCWB Theorem 4.1 (unbounded space), partial: an explicit network for the paper's construction
  (`docs/audit/FIX3-SCWB-T41.md`), the deterministic layer (extensible clocked Turing machines,
  `ClockedCTM/ExtensibleCTM.lean`: tracking, extension count, space bound, halting), the theorem
  stated as propositions (`ClockedCTM/Unbounded.lean`: `ErrorClaim`, `TimeClaim`, `TMTimeClaim`),
  the deterministic implication "no error and progress imply correct simulation"
  (`tmSimulatesAll_of_noError_progress`), and a conditional error assembly
  (`ClockedCTM/UnboundedError.lean`: `errorClaim_of_estimates` from named one-window estimates).
  Two statements are refuted with explicit witnesses: the exact restoration ratio claimed in an
  earlier note (`ordinary_restore_ratio_counterexample`) and unconditional tick progress
  (a reachable starvation trap, `TMStarvationWitness`). The probabilistic estimates are open.
- Tri-molecular approximate majority (Condon, Hajiaghayi, Kirkpatrick and Maňuch 2020):
  Lemma 6 for rates chosen from the full past (`lemma6_paper_adapted`, `Tri/PaperLemma6Adapted.lean`);
  the phase-0 witness `phase0Hyp_210`; Theorem 1(a) with explicit constants
  (`theorem1a_explicit`: for `n ≥ 2^420`, `γ ≥ 1`, `6γ log₂ n ≤ n`, the non-consensus mass after
  `258 γ n log₂ n` interactions is at most `n^{−γ/200}`); Lemma 6 with both error terms kept
  (`lemma6_paper_two_term`); Lemma 11 counters and stopped-potential bounds
  (`Tri/PaperLemma11Modes.lean`, `Tri/PaperLemma11ModeBounds.lean`; the final mode probabilities
  are stated as propositions, not yet proved).
- Explicit forms of earlier results: Euler's constant certificate (`euler_certifiedBoundedTimeComputable`),
  LPP/PLPP to GPAC with the source computation and dimension `n + 1` retained
  (`lpp_to_gpac_explicit`, `plpp_to_gpac_explicit`), the boundary values 0 and 1 in the
  unimolecular class (`lpup_computable_boundary_cases`), constant-rate dual rail with its trajectory
  data (`constantAnnihilation_bounded_explicit`), exact state counts of the P_EM protocol
  (`card_PEMFinState_eq`, `card_PEMPaperFin_eq`), and the unrounded Kanaya et al. Theorem 4 window
  and time constants (`P_EM_paper_window_exact`, `P_EM_paper_window_exact_rational`).

### Changed
- The success events of SCWB Theorems 3.1 and 3.2 now include completion:
  `Clocked.scwb_theorem_3_1` and `theorem_3_1_general` bound `P(¬ Simulates)`, where `Simulates`
  says that every state along the run encodes the right configuration and that `t` machine
  reactions fire or the machine halts (`Clocked.Completes`); `ClockedCTM.scwb_theorem_3_2_ctm`
  bounds `P(¬ Simulates)` with tick `4 t` drawn (`ClockedCTM.Reaches`), and
  `scwb_theorem_3_2_of_Θsum`, `scwb_theorem_3_2` bound `P(¬ TmSimulates)`: tick `4 N` drawn, every
  tick before it correct, and at that tick the state encodes the TM configuration after `t` steps.
  The probability and expected-time bounds are unchanged. Completion is almost sure on correct
  runs because their populations are bounded and the expected time is finite
  (`Clocked.law_simOK_not_completes`, `ClockedCTM.law_simOK_not_reaches`). The former
  safety-only bounds remain as `Clocked.law_not_simOK_le`, `ClockedCTM.sched_error_le`.

### Fixed
- Doty et al. protocol, phase-9 Init: the formalized `phaseInit` read the frozen `smallBias` in
  phase 9 (a copy of the phase-2 branch), so the fast path could not report after phase 2 and no
  O(log n) time bound held; it now reads the sign of the current dyadic bias of a Main agent
  (paper §3.4, Phase 9 = Phase 2). The deterministic correctness chain is re-established through
  the mass ledger `ExactMajority.reachable_ledger_bounds` (`loSum c ≤ initialGap init ≤ hiSum c`
  on reachable configurations without phase-10 agents) and the phase-9 opinion provenance
  `reachable_phase9Support`; `stable_majority_correct` and its variants keep their statements.

### Removed

### Verification
- Canonical build of the release tree on one NERSC Perlmutter CPU node: `Ripple`, `RippleDefault` and `Tri` from scratch,
  10093 jobs, no error, no `sorry`; the new headline declarations above print only `propext`,
  `Classical.choice` and `Quot.sound` under `#print axioms`.

### Documentation
- `rawLaw` is the embedded jump chain of the mass-action CTMC and `expTime` its expected
  holding-time functional `E[Σ_n 1/totalPropensity(Z_n)]` before the target; the continuous-time
  chain with exponential holding times is now `timedLaw` (see Added).
- New paper notes: `docs/audit/FIX-KURTZ2-FINAL.md` (Kurtz exponential tail and CLT) and
  `docs/audit/FIX3-SCWB-T41.md` (SCWB Theorem 4.1 network and proof outline).

## [r2026.11.3] — 2026-11-09

An incremental release. Ramanujan's 1914 series for 1/π is now proved
without hypotheses, the time part of Kanaya et al. Theorem 4 is proved for
the papers' parameters, and Theorem 3.2 of Soloveichik, Cook, Winfree and
Bruck is proved for a repaired network. The two SCWB theorems carry a caveat
found by a statement audit (see Verification). Long-form notes are in
`RELEASE_NOTES.md`.

### Added

- Ramanujan's 1914 series
  `1/π = (2√2/9801) Σ (4k)!/(k!)⁴ (1103 + 26390k)/396^{4k}` with no premise
  (`Ramanujan1914.ramanujan_one_over_pi`). The CM evaluation
  `1103 F(99⁻⁴)² + 26390·99⁻⁴·(F²)′(99⁻⁴) = 9801/(2√2π)`,
  `F = ₂F₁(1/8, 3/8; 1; ·)`, is `Modular.ramanujanCM58_evaluation`:
  - the Hauptmodul of `Γ₀(2)+` takes the value `x₂(i√58/2) = 1/99⁴`
    (`Modular.hauptT58_tau58`, `x2_tau58`: the only root of `Ψ₂₉(X, X)` above
    `1.1·10¹⁰`, by a kernel-checked sign certificate, plus real `E₄` bounds);
  - the degree-29 modular equation `Ψ₂₉(T(29τ), T(τ)) = 0`
    (`Modular.psi29_modular_equation`) is certified by the vanishing of a
    cleared weight-480 form on `Γ₀(58)` (`psi29ClearedForm_eq_zero`): a
    kernel-checked evaluation of its first 3601 coefficients, a Sturm bound on
    `Γ₀(N)` from a bound on the index (`Modular.gamma0_eq_zero_of_coeff`), and
    coefficient bounds by weighted-sum majorants;
  - the second-order expansion of `Ψ₂₉(T(−29/(2z)), T(z)) ≡ 0` at the fixed
    point gives the CM relation (`Modular.masser58`,
    `ramanujan58_cm_relation`, generic `second_order_of_eqOn_zero`);
  - the level-2 Kummer identity `2E₂(2τ) − E₂(τ) = F(x₂(τ))²` near `i√58/2`
    (`Modular.Z_sq_eq_gauss`) comes from Milla's `E₄ = ₂F₁(1/12, 5/12; 1; 1/J)⁴`
    and two hypergeometric transformations proved by uniqueness of analytic
    solutions (`Hypergeometric.gauss2F1_quadratic`, `gauss2F1_cubic_pow_four`,
    `gauss2F1_quarter_unique`); level-2 layer `Modular.level2Z`,
    `level2_E4_sum`, `level2_E6`, `level2_E6_two`, `hauptT58_fricke2`,
    `psi29_mu58_equation`.

  The version with the CM evaluation as premise is
  `ramanujan_one_over_pi_of_cm58`. Paper notes: `docs/audit/CHUD-PAPER.md`
  §4, with the `Ψ₂₉` scripts under `docs/audit/evidence/chud/lvl58/`.
- Kanaya et al. Theorem 4, time part, for the paper instance of P_EM
  (`trank = 40`, `Emax = 208 n`, `Dmax = 32 n`): `P_EM_paper_thm4_time` — for
  `n ≥ 1608` and every configuration of the finite instance, expected
  parallel time to silence `≤ 5215 n`, and silence within
  `4172 n² ⌈log₂ n⌉` interactions except with probability `≤ 1/n`;
  `kanayaThm4Time` is the existential form and
  `kanayaThm4Time_explicit_of_window` states the constants in the type. It
  is assembled from the uniform window `P_EM_paper_window`
  (`P[silent within 1043 n²] ≥ 1/5`, `kanayaThm4Time_of_window`), which is
  composed of stage bounds (`kanayaThm4Time_of_stages`, `epoch1_of_stages`,
  `epoch2_of_stages`):
  - Burman et al. Lemma 3.3 (dormancy after full propagation,
    `P_EM_paper_dormancy_bound`, `n ≥ 1600`);
  - stage A from every good configuration (`stageA`, `≥ 0.86` within
    `t₁ + 241 n²`); stages B1, B2 (`stageB1`, `stageB2`, `stageB2M`; leaders
    never disappear, `exists_leader_step`); stage B1 of epoch 2 (`stageB1Z`);
    tree ranking, Burman et al. Lemmas 3.3–3.4 in corrected form
    (`stageB34`, `stageB34M`); the ranked stages, sorting by additive drift
    and the countdown (`stageA'`, `stageB56`, `stageB56M`, `stageC`,
    `stageE`);
  - Definition 1 with probability one for the finite instances
    (`P_EM_paper_fin_kanayaDefinition1`, `P_EM_fin_kanayaDefinition1`,
    `P_EM_paper_fin_silent_almostSurely`), from
    `Probability.reachesGoalAlmostSurely_of_fintype`; transfer of time bounds
    through a state simulation (`StateSimulation.probNotHitBy_encC`,
    `expectedHittingTime_encC`) and composition of windows
    (`probNotHitBy_compose_le`, `Probability.probNotHitBy_window_le_drift`).

  Paper proofs: `docs/audit/FIX2-BURMAN.md`, `FIX2-P2.md`, `FIX2-P3.md`;
  statement audit `docs/audit/KANAYA-THM4-AUDIT.md` (faithful, with the
  standard i.i.d. uniform scheduler); non-vacuity probe
  `docs/audit/probes/ProbeKanayaThm4.lean`.
- Soloveichik–Cook–Winfree–Bruck (2008), Theorem 3.2, for a repaired Fig. 3.2
  network (the network as drawn fails; three local repairs,
  `docs/audit/FIX3-SCWB-T32.md`): `ClockedCTM.scwb_theorem_3_2`. For a binary
  Turing machine `M` (blank `false`) and clock length `L + 1`, the network
  `net (ctmOf M) L` and `#A*` are fixed first; then for every `δ ∈ (0, 1]`,
  input configuration and step bound `t` within tape bound `Lc` there is a
  count of `A` with error `≤ δ` and, with CTM tape length `s = 2 Lc`,
  expected time
  `≤ 2880 (3/2)^L v s² t² (1 + (s−1) ln 3)/(k 3^s δ) ≤ 3168 (3/2)^L v s³ t²/(k 3^s δ)`.
  For comparison, the repaired paper analysis obtains
  `2746 (3/2)^{l−1} v s³ t²/(k 3^s δ)`; SCWB's printed Theorem 3.2 states only
  `O(v (s+Δ)^{7/2} t^{5/2}/(k 3^{2s+Δ} δ^{3/2}))`. The sharper bound is
  `scwb_theorem_3_2_of_Θsum`, and `Θsum_le_log` gives its
  `O((1 + ln m)/m)` asymptotics. CTM level: `ClockedCTM.scwb_theorem_3_2_ctm`;
  Lemma A.9 (TM → CTM) is proved (`ctm_tracks`). Non-vacuity probe
  `docs/audit/probes/ProbeSCWB32.lean`.

### Changed

- `Ramanujan1914.ramanujan_one_over_pi` has no premise; the former
  conditional statement is `ramanujan_one_over_pi_of_cm58`.
- The `maxHeartbeats 800000` override on `ClockedCTM.win34c_fire` is removed
  (the proof is split).

### Verification

- The source contains no `sorry`, `admit`, `axiom` declaration or
  `native_decide`.
- Canonical build of the release tree on one NERSC Perlmutter CPU node, with
  Mathlib from a prebuilt cache and Ripple and `Tri` compiled from scratch
  with 64 compile threads: `lake build Ripple RippleDefault Tri` completed
  successfully (5588 jobs; 1124 Ripple and 447 `Tri` modules) in about 34
  minutes of build time, split over two jobs (the second resumed
  incrementally), with no error and no `sorry`. `#print axioms` on 176
  declarations (the headline declarations of earlier releases that remain
  and those added or restated here) reports only `propext`,
  `Classical.choice` and `Quot.sound` (one of them,
  `exists_leader_step`, uses only `propext` and `Quot.sound`).
- A type-only triage of 170 headline theorems (no conclusion reducing to
  `True`, no premise definitionally equal to the conclusion, no equation
  whose sides are definitionally equal) found no pattern in 169; for
  `Modular.hauptT58_fricke2`, `hauptT58 (fricke2 τ) = hauptT58 τ`, the
  definitional-equality test of the two sides did not finish within its
  limit.
- Statement audits: `docs/audit/KANAYA-THM4-AUDIT.md` finds
  `P_EM_paper_thm4_time` faithful with caveats.
  `docs/audit/SCWB-T31-T32-AUDIT.md` finds that in SCWB Theorems 3.1 and 3.2
  (`scwb_theorem_3_1`, `scwb_theorem_3_2`) the success events `SimOK` and
  `TmOK` are safety predicates: no wrong step before the target, without the
  assertion that the target step is reached. The paper's "completes the
  computation" is therefore not yet part of the Lean statements; the repair
  is in progress. The audit also notes that the probabilities are those of
  the jump chain and that the expected time is the expected sum of mean
  holding times along it, not yet connected in Lean to a continuous-time
  process.

### Documentation

- Paper notes published under `docs/audit/`: `CHUD-PAPER.md` §4 (level 58),
  `FIX3-SCWB-T32.md`, `FIX2-P2.md`, `FIX2-P3.md`, the two statement audits,
  the `Ψ₂₉` scripts and the two non-vacuity probes; `FIX2-BURMAN.md` and
  `FIX3-SCWB.md` updated.
- `README.md`, `OPEN_PROBLEMS.md` and `paper/ERRATA.md` record the new status
  of the Ramanujan series, Kanaya Theorem 4 and SCWB Theorem 3.2, and the
  safety-only caveat of SCWB 3.1 and 3.2.

## [r2026.11.2] — 2026-11-09

An incremental release. The Chudnovsky formula is now proved without
hypotheses, Theorem 3.1 of Soloveichik, Cook, Winfree and Bruck is proved,
and the Kanaya et al. protocol gets an O(n)-state instance. Long-form notes
are in `RELEASE_NOTES.md`.

### Added

- The value `s₂(τ₁₆₃) = 77265280/90856689` of
  `s₂ = (E₄/E₆)(E₂ − 3/(π Im τ))` at `τ₁₆₃ = (1 + √−163)/2`
  (`Modular.s2_heegnerTau163`), derived from the certified modular equation
  `Φ₄₁` by a third-order expansion at its node (`Modular.Phi41TaylorData`:
  kernel-checked partials of `Φ₄₁` at `(j₀, j₀)`; `Modular.Phi41Node`:
  `third_order_of_eqOn_zero` and `Φ₄₁(j(z), j(1 − 41/z)) = 0`;
  `Modular.E2StarCM163`). Paper notes: `docs/audit/CHUD-PAPER.md`.
- `Ripple/Number/Milla/`: Milla's proof of the Chudnovsky main theorem
  (`Milla.hauptformel`), ported from Lean Pool (`LeanPool/Chudnovsky`,
  Xuanji Li, Apache-2.0). The ported files keep their copyright and license
  headers; `NOTICE` records the origin and the changes.
- Soloveichik–Cook–Winfree–Bruck (2008), Theorem 3.1:
  `Clocked.scwb_theorem_3_1`. For every register machine `M` the network
  `net M 1` (Fig. 3.1, fixed by `M`) is given first; then for every
  `δ ∈ (0, 1]`, input and step bound `t ≥ 1` there is an initial count `a`
  of `A` such that under the mass-action jump chain the first `t` steps are
  simulated correctly with probability at least `1 − δ`, in expected time at
  most `6 v t² / (k δ)`. The general clock length is
  `Clocked.theorem_3_1_general` (error `≤ t / (1 + a + ⋯ + a^L)`, time
  `≤ 2t(1 + a + ⋯ + a^L)`). The clock module in occupation-measure form
  (`Stochastic.ClockOccupation`: flux identity, cone invariance, tick and
  time bounds) and the one-step Markov property of the mass-action jump
  chain on prefix events (`MassAction.rawLaw_prefix_next`) are its inputs.
  Paper proofs: `docs/audit/FIX3-SCWB.md`.
- Kanaya et al. (2025), Theorem 4, state count: `P_EM_fin_silent_SSEM_states`
  shows that the Lean P_EM, run on a finite role-indexed state type with at
  most `394 n` states, is silent self-stabilizing exact majority for `n ≥ 4`
  (`SSEM.Convergence.FiniteStatePEM`, with the simulation transport
  `StateSimulation.solvesSilentSSEM`).
- P_EM with the parameters of Kanaya et al. and Burman et al. (constant
  `trank`, `Rmax = ⌈60 ln n⌉`, `Emax = e·n`, `Dmax = d·n`): its finite
  version is silent SSEM for `n ≥ 4` (`P_EM_paper_fin_solves_silent_SSEM`)
  with `O(n)` states (`card_PEMPaperFin_le`). The time part of Theorem 4 is
  stated for this instance (`KanayaThm4Time`) and not proved
  (`SSEM.UpperBound.PaperInstance`).
- Burman et al. (PODC 2021), Lemma 3.2 (propagation of a reset) for P_EM
  with the papers' parameters: from any configuration with a Resetting agent
  whose resetcount is at least `⌈60 ln n⌉`, the configuration after
  `⌈4 n ln n⌉` interactions is fully propagating except with probability at
  most `2/n` (`P_EM_paper_propagation`). The proof uses two potentials on a
  scheduler-prefix representation of the chain with a product-measure
  supermartingale lemma (`Probability.probNotHitBy_le_prefixMass`,
  `Probability.schedulerPrefix_expect_le_pow`). Paper notes:
  `docs/audit/FIX2-BURMAN.md`.
- `Kurtz.kurtz_finite_horizon_of_close`: Kurtz's law of large numbers on
  `[0, T]`, uniform over deterministic simplex initial states within a
  distance `γ` of `x(0)`.

### Changed

- `Chudnovsky1989.chudnovsky_one_over_pi` is unconditional: the series
  identity `640320^{3/2}/(12π) = Σ (−1)^k (6k)!/((3k)!(k!)³)
  (13591409 + 545140134 k)/640320^{3k}` with no premise, from Milla's main
  theorem at `τ₁₆₃` with `j(τ₁₆₃) = −640320³` and the value of `s₂(τ₁₆₃)`.
  The former conditional version is `chudnovsky_one_over_pi_of_cm163`.
- `Ramanujan1914.ramanujan_one_over_pi` keeps its premise, now labelled as a
  true but unproved evaluation (`OPEN_PROBLEMS.md` §6.6).
- `Kurtz.kurtz_finite_horizon` takes the initial condition of Kurtz 1970,
  Theorem 3.1: the initial state of the population-`N` chain has a law on the
  simplex whose densities converge in probability to `x(0)`, and the
  conclusion is convergence in probability of `sup_{t ≤ T} ‖X̄^N(t) − x(t)‖`
  to 0 under the mixed path law. Before, the initial state was deterministic
  within `1/N` of `x(0)`. Two regularity premises on the limit solution are
  removed.
- `zero_init_no_collapse` states the eventual lower bound
  `∃ c > 0, ∃ T, ∀ t ≥ T, c ≤ sol.trajectory t i` (liminf at least `c`)
  instead of a cofinal one, which did not exclude liminf 0;
  `zero_of_limit_is_trivial` uses it directly.

### Removed

- `Modular.RamanujanLambda58Statement` (`thetaLambda (i√58/2) = 1/99²`) was
  false and is deleted with its consumers `.sq`, `.isRoot`, `.of_isRoot`,
  `.pullback_isRoot`. The docstrings of `ramanujanLambda58Target`,
  `ramanujanJ58Target` and `cm58LegendreLambda` now say that these numbers
  are not `λ(i√58/2)` and `j(i√58/2)`.
- `zero_init_eventually_bounded_below` (added in r2026.11.1): its statement
  is now that of `zero_init_no_collapse`.

### Verification

- The source contains no `sorry`, `admit`, `axiom` declaration or
  `native_decide`.
- Canonical build of the release tree on one NERSC Perlmutter CPU node, with
  Mathlib from a prebuilt cache and Ripple and `Tri` compiled from scratch
  with 64 compile threads: `lake build Ripple RippleDefault Tri` completed
  successfully (5525 jobs; 1063 Ripple and 447 `Tri` modules) in about 39
  minutes of build time, split over two jobs (the second resumed
  incrementally), with no error and no `sorry`. `#print axioms` on 122
  headline declarations (those of earlier releases that remain and those
  added or restated here) reports only `propext`, `Classical.choice` and
  `Quot.sound`.

### Documentation

- `NOTICE` records the third-party code under `Ripple/Number/Milla/`.
- Paper notes cited from the source: `docs/audit/CHUD-PAPER.md` (the CM
  value `s₂(τ₁₆₃)`), `docs/audit/FIX3-SCWB.md` (SCWB Theorems 3.1, 3.2,
  4.1), `docs/audit/FIX2-BURMAN.md` (the time bound of P_EM and Burman et
  al. Lemma 3.2), with the checker scripts under
  `docs/audit/evidence/chud/`.
- `paper/ERRATA.md`, `README.md` and `OPEN_PROBLEMS.md` record the status
  changes above (SCWB Theorem 3.1, the Kanaya state count, Kurtz's initial
  condition, the Chudnovsky formula).

## [r2026.11.1] — 2026-11-08

An incremental release. It proves ζ(3) real-time computable, formalizes
Sections 2 to 7 of the journal version of the bounded analog complexity
paper [BAC], and removes or renames statements whose names claimed more than
their proofs give. Long-form notes are in `RELEASE_NOTES.md`; the erratum
`paper/ERRATA.md` now records which report claims are established.

### Added

- Apéry's constant is real-time computable:
  `Ripple.Number.apery_is_realtime : IsRealTimeComputable (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3))`.
  The witness is the five-variable Fermi–Dirac system `fermiPolyPIVP` with
  ℚ-polynomial field and initial value `(1, 0, 0, 1/2, 0)`, and modulus
  `μ(r) = 2r + 6` (`fermi_certifiedBoundedTimeComputable`); also
  `apery_isRTGPACComputable`.
- [BAC] journal version, Sections 2 to 7:
  - Theorem 4.6 for the definition of Bournez, Graça and Pouly: a number
    or a function on a compact set that is poly-length-computable in their
    sense is computed by a bounded ℚ-PIVP in polynomial time
    (`isPolyTimeComputable_of_isBGPPolyLengthComputable`,
    `isPolyTimeComputableOn_of_isBGPPolyLengthComputableOn`, through the
    shifted-clock compilation `PolyPIVPFamily.shiftedCompile_computesOn`;
    modules `Ripple/Core/BGPPolyLength.lean`,
    `Ripple/Core/ShiftedClockCompilation.lean`).
  - Theorem 6.1, closure under `α^β` for `α > 0` (`isCRNComputable_rpow`,
    `rpow_certified`), and Theorem 6.4 for the polynomial classes
    (`isPolyTimeComputable_rpow`), with a repaired construction and a
    corrected modulus (`Ripple/Core/PowerClosure.lean`).
  - Section 7, the CRN readout with the modulus relation: a bounded ℚ-PIVP
    computing `α > 0` with modulus `μ` gives a mass-action CRN with zero
    initial values and modulus at most `max(μ(r + k), 0) + (4/α + 4α) r + C`
    (`crn_of_certified`, `Ripple/Core/CRNReadout.lean`); polynomial-time
    GPAC and polynomial-time CRN agree for `α > 0` (`isPolyTimeCRNComputable_iff`;
    for linear moduli the GPAC-to-CRN direction of the real-time equivalence
    paper [RTCRN2], `IsRealTimeComputable.isPolyTimeCRNComputable_one`).
  - The [LPP] Main Theorem in the GPAC-to-LPP direction without a CRN-shape
    premise: every `IsCRNComputable` number in `[0, 1]` is LPP-computable
    (`IsCRNComputable.isLPPComputable`); in particular Euler's constant
    (`Ripple.Number.euler_gamma_is_lpp_computable`, [LPP] Corollary 19).
  - Section 5, constructible time moduli with exact moduli: `(r+1)^n − 1`
    (`Constructible.polyFamily_certified`), `(r+1) log(r+1)` through a
    Lambert function built in Lean (`Constructible.lambert_certified`), and
    the tower `E_{k+1}(r)` (`Constructible.tower_certified`,
    `tower_modulus_bounds`) (`Ripple/Core/Constructible.lean`).

  The repairs of the draft's proofs are in `docs/refactor/BAC2-PAPER.md`.
- Albenque and Gerin, Theorem 5, in every degree and without premises: for
  each `d ≥ 1` an Ehrenfest-computable root of an irreducible integer
  polynomial of degree `d` (`isEhrenfestComputable_algebraic_of_degree`,
  `Ripple/LPP/EhrenfestAlgebraicDegrees.lean`), through an elementary proof
  of Cassels' divisibility theorem (`cassels_upper_divisor_nat_elementary`).
- Silent self-stabilizing exact majority (Kanaya et al., arXiv:2503.17652v1):
  `SilentProtocol`, `SolvesSilentSSEM` and `KanayaDefinition1` (Definition 1
  with the uniform random scheduler), with `silentProtocol_of_almostSure` and
  `solvesSSEM_of_kanayaDefinition1`; `P_EM_solves_silent_SSEM_linear`, the
  qualitative part of Theorem 4 (`P_EM` is silent SSEM for `n ≥ 4`); and
  Theorem 3 in full for `n ≥ 2` (`time_lower_bound_tail`,
  `time_lower_bound_expected`, `time_lower_bound_whp`), with the non-vacuity
  witness `twoAgentProtocol_solvesSilentSSEM`.
- Soloveichik–Cook–Winfree–Bruck Theorem 4.2 as an algorithm: the
  coverability instances `Decidability.petriCoverabilityDecidable`,
  `networkCoverabilityDecidable` and their species versions are computable
  (they were `noncomputable`).
- The CF'24 worked example of the PP-to-NAP construction from the canonical
  initial condition `(1, 0, 0)`, without hypotheses: `CF24.cf24_readout_canonical`
  (`z_11 + z_01/2 → (3 − √5)/6`) and its λ-trick, r²-trick and NAP-20 lifts
  (`Ripple/LPP/CF24Canonical.lean`; proof on paper in
  `docs/audit/FIX1-CF24.md`).
- Kurtz's law of large numbers on `[0, T]` (Kurtz 1970, Theorem 3.1) for
  canonical density-dependent CTMCs: `Kurtz.kurtz_finite_horizon`
  (`Ripple/Kurtz/FiniteHorizon.lean`), with Doob's L² maximal inequality and
  the quadratic-variation bound proved.
- `zero_init_eventually_bounded_below`, the eventual (liminf) form of the
  zero-initialization no-collapse theorem.

### Changed

- `time_lower_bound_omega_n_expected` (Kanaya Theorem 3): the constant
  `c = 1/4` now precedes the protocol and `n` (it was `1/n²`), and the
  silence premise is the reachability form (the former premise was
  unsatisfiable together with self-stabilization for `n ≥ 2`).
- `space_lower_bound` (Kanaya Theorem 2): the premise that the transition
  function ignores the input is gone; the premises are silence and
  self-stabilization.
- Renamed, same statements: `RegisterMachine.rmNetwork_simulation_correct` to
  `rmNetwork_reaches_successor` (one-instruction reachability, not SCWB
  Theorem 3.1); `Kurtz.kurtz_mean_field_convergence` to
  `tendsto_sup_err_of_gronwall_markov`; `Kurtz.kurtz_convergence_for_density_dep_ctmc`
  to `kurtz_convergence_of_event_inclusion` (an unused Lipschitz premise
  dropped). The Kurtz statements assume the estimate that makes the
  convergence a squeeze, so the names no longer present them as Kurtz's
  theorem.

### Removed

- `PEM_expected_parallel_time_linear_param` and
  `PEM_consensus_window_success_prob_vacuous_timer_const` (their premise is
  false: the timer is unbounded), `silent_config_AB_distinct`,
  `RandomStabilizesSSEM`. The time and state bounds of Kanaya Theorem 4 are
  open (`OPEN_PROBLEMS.md` §6.1).
- Soloveichik–Cook–Winfree–Bruck: the 22 `PaperTheorems.exists_*` wrappers
  (their conclusion holds for every pair of states through the network
  `∅ ⇄ X`); the 14 `PaperTheorems.statePairTransfer_*` wrappers (the network
  does not depend on the machine, so they are not simulation statements; the
  `CTM` lemmas remain); `scwb_stochastic_bound` and
  `Stochastic.scwb_rawLaw_concrete_bound` (per-step error bound 1);
  `scwb_stochastic_bound_of_enabled_of_clock` and
  `Stochastic.scwb_rawLaw_bound_of_enabled_of_clock` (premise unsatisfiable
  for two or more steps); `statePairTransferEpsilonBound`,
  `scheduleSourceClock`, `statePairTransfer_clock_propensity_bound`.
  Theorems 3.1, 3.2 and 4.1 are open (`OPEN_PROBLEMS.md` §6.2).
- `cf24_step5_readout_of_basinEntry` and
  `cf24_{lambda,r2,nap20}_lifted_readout_of_basinEntry`: their hypothesis
  `Cf24BasinEntry` is false (`cf24_basinEntry_false`). The statement for
  every interior initial condition is open (`OPEN_PROBLEMS.md` §6.3).
- `Kurtz.kurtz_strong_approximation` (its premise is its conclusion),
  `Kurtz.kurtz_clt_second_moment` (fixed `N`, carried second-moment bound)
  and the module `Ripple/Kurtz/MeanFieldLogHorizon.lean`. Kurtz's central
  limit theorem and strong approximation are open (`OPEN_PROBLEMS.md` §6.5).
- `closure_exponentiation_via_exp_log`, conditional on closure under `exp`
  and `log`, superseded by `isCRNComputable_rpow`.

### Verification

- The source contains no `sorry`, `admit`, `axiom` declaration or
  `native_decide`.
- Canonical build of the release tree on one NERSC Perlmutter CPU node, with
  Mathlib from a prebuilt cache and Ripple and `Tri` compiled from scratch
  with 64 compile threads: `lake build Ripple RippleDefault Tri` completed
  successfully (5490 jobs; 1038 Ripple and 447 `Tri` modules) in about 33
  minutes of build time, split over two 30-minute jobs (the second resumed
  incrementally), with no error and no `sorry`. `#print axioms` on 104
  headline declarations (those of `r2026.11` that remain and those added or
  restated here) reports only `propext`, `Classical.choice` and
  `Quot.sound`.

### Documentation

- `OPEN_PROBLEMS.md` gains a section on the cited-paper results that are not
  formalized (Kanaya Theorem 4 bounds, SCWB Theorems 3.1, 3.2 and 4.1, the
  CF'24 limit from interior initial conditions, the Doty et al. state count
  and time, Kurtz's CLT and strong approximation).
- `paper/ERRATA.md` marks which of the report claims in its second section
  are now established and which remain open.
- `docs/refactor/STATEMENT-CHANGES.tsv` and `RENAMES.tsv` list the changes
  above.

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
