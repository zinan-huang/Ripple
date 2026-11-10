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
