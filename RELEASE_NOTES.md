# Ripple Release Notes

This file contains long-form, frozen notes for tagged Ripple releases.
Ongoing public-facing changes belong in [`CHANGELOG.md`](CHANGELOG.md);
Technical Report handling, version namespaces, and the release procedure are
defined in [`MAINTENANCE.md`](MAINTENANCE.md).

## r2026.11.8 — 2026-11-14 (identifier renames; errata documents refreshed)

A maintenance release with no change to the mathematics. Identifiers and comments are
renamed to use "genuine"; the renamed public declarations are
`Tri.Byzantine.GenuineXConsensus`, `Phase7ClassMassDrain.phase7GenuineDrain`, the structure
field `genuine` of six ready/consumer records of the exact-majority time proof
(`Phase1DrainReady`, `Phase1AdaptiveReady`, `Phase7DrainReady`, `Phase8DrainReady`,
`Phase7StageReady`, `PhaseSevenBandConsumer`) and the field `to_genuine` of
`Phase6PostToPhase7Ready`, `Phase7PostToPhase8Ready` and `Phase6To7BandEntry`; the full list
is in `CHANGELOG.md`. Statements and proofs are unchanged.

The errata note for Doty et al. ([`docs/doty/ERRATA.pdf`](docs/doty/ERRATA.pdf)) no longer has
an author line. The Tri errata
([`docs/tri/Errata_and_Counterexamples.pdf`](docs/tri/Errata_and_Counterexamples.pdf)) are
rebuilt from the current LaTeX source; the tracked PDF dated from August 2026 and did not
contain the later corrections (the creation-tolerance diagnosis and table, the Corollary 2 and
Lemma 6 parity explanations, the reversed Lemma 6 ratio step, the Lemma 11 mode bounds).

### Verification

Canonical build of the release tree on one NERSC Perlmutter CPU node (job
61278629): `Ripple`, `RippleDefault` and `Tri` from scratch, 10880 jobs, no error,
no `sorry`, all 1950 Ripple and 451 `Tri` modules. The source contains no `sorry`,
no named `axiom` and no `native_decide`. The 41 headline declarations of
r2026.11.7, among them `exact_majority_theorem_three_one` and
`exact_majority_stabilization_time`, print only `propext`, `Classical.choice` and
`Quot.sound` under `#print axioms`.

## r2026.11.7 — 2026-11-14 (Doty et al. Theorem 3.1 for one protocol; PP to NAP; paper errata)

Three things are new. Theorem 3.1 of Doty, Eftekhari, Gąsieniec, Severson,
Stachowiak and Uznański (FOCS 2021) is now one Lean theorem about one protocol,
with smaller constants. The construction that turns a population protocol into a
non-autocatalytic protocol (PP to NAP) is proved general and formalized at the
level of the mean-field ODE. The bounded analog complexity material gains the
statements of its journal version. The errata found in the paper of Doty et al.
are published in [`docs/doty/ERRATA.pdf`](docs/doty/ERRATA.pdf). The release adds
38 modules and renames two public declarations and one public module; the old
names are in `docs/refactor/RENAMES.tsv`.

### Doty et al. Theorem 3.1 for one protocol

`TheoremThreeOne.exact_majority_theorem_three_one` states the three parts of
Theorem 3.1 for the compact protocol `NonuniformMajorityCompact (⌈log₂ n⌉) 256`.
For every population size `n ≥ 5·2^(2^23)`:

- the protocol has at most `23 136 960 (⌈log₂ n⌉ + 1)` states;
- it stably computes majority on valid inputs of size `n`;
- its own stabilization time `T`, in interactions under the uniform random
  scheduler on the ordered-pair log, satisfies
  `P(T > 16300 n (⌈log₂ n⌉ + 1)) ≤ 110/n²` and `E T ≤ 470 235 n ln n`.

Earlier releases proved the state count for the compact protocol (r2026.11.4)
and the time bound for the flat protocol `NonuniformMajority` (r2026.11.6). The
new theorem runs the compact transition directly on the scheduled labels of the
interaction log, shows that this run is the encoding of the flat run on every
log, and bounds its stabilization time by the flat endpoint time.

The time bound itself is now
`StabilizationTime.exact_majority_stabilization_time`
(formerly `DotyStabilizationTime.doty_stabilization_time`; the paper has six
authors, and the names now describe the result). Its constants are smaller: the
population threshold drops from `5·2^(2^41)` to `5·2^(2^23)`, the high-probability
horizon from `23000 n (⌈log₂ n⌉ + 1)` to `16300 n (⌈log₂ n⌉ + 1)` interactions,
and the expectation bound from `24 807 000 n ln n` to `470 235 n ln n`. The
probability statements keep their form; only numerical premises weaken, and the
scalar calibration is collected in one module (`Probability/Calibration.lean`).
The threshold is still astronomically large.

### Errata for Doty et al.

Formalizing Theorem 3.1 turned up the items in
[`docs/doty/ERRATA.pdf`](docs/doty/ERRATA.pdf) (LaTeX source alongside),
summarized in `paper/ERRATA.md`. Theorem 3.1 holds. Two printed statements are
false as stated: the first case of Lemma 5.3 for large gaps (every input with
`|g| > |M|`, including the unanimous input, reaches the Phase-10 backup, so the
expected-time argument needs the backup to be fast for large gaps, which it is),
and the lower bound of Theorem 6.9 for small clock fractions (a conversion factor
`1/c²` should be about `1/c`; the choice of `k = 45` minutes per hour then lacks a
proof, and `k ≥ 121` restores it). The other items are proof gaps with true
statements (the clock analysis must start from the asynchronous entry into
Phase 3; a time horizon in Lemma 6.10) and typographical or pseudocode slips.

### From population protocols to non-autocatalytic protocols

A non-autocatalytic protocol (NAP) is a population protocol in which no reaction
net-produces one of its own reactants. The construction under study adds a slack
species, multiplies the field by the square of the slack (the r²-trick, which
gives a quartic system), and cubes: the new species are the degree-3 monomials
of the old ones (the Veronese lift). Formalized in `Ripple/LPP/NAP*.lean`:

- Rewriting each positive monomial independently gives an ODE that is correct on
  the Veronese image but in general is not the balance field of any protocol.
  The reactions are instead routed by a transportation (supply/demand)
  construction. For a syntactic quartic protocol, two sign conditions on its
  coefficients give a non-negative NAP realising the cubed field
  (`exists_nap_realizing_of_C1C2`); the pipeline always satisfies them
  (`exists_nap_realizing_pipeline`). The CF'24 example has an explicit
  141-reaction NAP (`NAPProtocol.cf24Cubing_eq_napField_on_cubed`).
- For every syntactic quadratic PP, every species `j₀` and `λ ∈ (0, 1)`, the NAP
  trajectory from the lifted initial point is the Veronese image of a
  time-changed PP trajectory, with an explicit clock tending to infinity, the same
  readout limit, and the exponential rate transferred when the slack has a
  positive limit (`pp_to_nap_ode_of_init`).
- A cheaper variant (r-trick and squaring) works exactly when no homodimer raises
  the mass of the shrunk set (`squaring_iff`); CF'24 gives a NAP on 10 species
  (`cf24_squaring`).
- Exchange reactions make the lifted image normally attracting: at every
  equilibrium, interior or on the boundary of the simplex, the spectrum of the
  NAP is that of the quartic protocol plus eigenvalues of negative real part for
  every exchange rate above some `K₀` (`normal_stability_interior`,
  `normal_stability_boundary`).
- `{0, 1}` readouts: three layer copies read the original number with the
  original clock (`LayerCopy.pp_to_nap_layer_copy_of_init`); no fixed `{0, 1}`
  subset of the cubic species reads the original marked mass on the whole simplex
  (`MarkedObstruction.no_marked_readout_on_simplex`).

This answers `OPEN_PROBLEMS.md` §4.5 at the mean-field level; the
finite-population semantics remain open.

### Bounded analog complexity: journal-version statements

New modules in `Ripple/Core/`: unique maximal forward solutions of polynomial
IVPs, blow-up at a finite endpoint, the complete time change from a maximal
solution and computability of a finite maximal lifetime (`MaximalPIVP.lean`);
the exact clock modulus kept in the polynomial-time certificate and further
clauses of the surrogate bound (`BACJournalStrong.lean`); selective dual rail,
with one retained output species and same-time comparison of the source and the
CRN (`SelectiveDualRail.lean`); general subset compilation with evolving retained
coordinates (`SubsetCompilation.lean`); and the power trajectory, the BFK cyclic
protocol, the shifted clock and the product clock (`BACJournalRemarks.lean`).

### Verification

Canonical build of the release tree on one NERSC Perlmutter CPU node (job
61266330): `Ripple`, `RippleDefault` and `Tri` from scratch, 10880 jobs, no error,
no `sorry`, all 1950 Ripple and 451 `Tri` modules. The source contains no `sorry`,
no named `axiom` and no `native_decide`. The 41 headline declarations checked,
among them `exact_majority_theorem_three_one`,
`exact_majority_stabilization_time`, `exists_nap_realizing_of_C1C2`,
`pp_to_nap_ode_of_init`, `normal_stability_interior`, `normal_stability_boundary`,
`LayerCopy.pp_to_nap_layer_copy_of_init`, `isCRNComputable_maximalTime_certified`,
`SelectiveDualRail.exists_solution` and the 24 headlines of r2026.11.6, print only
`propext`, `Classical.choice` and `Quot.sound` under `#print axioms`.

## r2026.11.6 — 2026-11-14 (Doty et al. Theorem 3.1 in full; Kurtz's 1978 strong approximation)

This release completes two cited-paper results that earlier releases listed as
open. The exact-majority protocol of Doty, Eftekhari, Gąsieniec, Severson,
Uznański and Viglietta (FOCS 2021) now has its O(log n) stabilization time, in
expectation and with high probability, so Theorem 3.1 of that paper (O(log n)
states, r2026.11.4, and O(log n) time) is formalized in full. Kurtz's strong
approximation theorems for density-dependent Markov chains (Stochastic Process.
Appl. 6, 1978) are proved under the paper's hypotheses: the Poisson–Brownian
coupling of Lemma 3.1, the diffusion approximation of Theorem 3.3(a) and the
Gaussian approximation of Theorem 4.4. The second result needed stochastic
calculus that Mathlib does not have; it is in the new library
`Ripple/Stochastic/`. The release adds 744 modules; of the earlier
statements it changes only the CF'24 readout theorems described below and one
instance-level detail of `ClockDepletionCoupling` (see the changelog).

### Doty et al. Theorem 3.1: the time bound

`DotyStabilizationTime.doty_stabilization_time : TimeTheorem.DotyTimeClaim`
has no hypotheses. For the formalized protocol `NonuniformMajority L K` with
`L = ⌈log₂ n⌉` and `K = 256`, every population size `n ≥ 5·2^(2^41)` and every
valid input configuration of size `n`, let `τ_D` be the number of interactions
until the configuration first reaches a stable endpoint with the correct
majority output (`StableDone`; every such configuration is stable and outputs
the initial majority, `stable_output_of_majorityStableEndpoint`). Then

- `P(τ_D > 23000 n (⌈log₂ n⌉ + 1)) ≤ 110/n²`, and
- `E τ_D ≤ 24 807 000 n ln n`,

that is, O(log n) parallel time with high probability and in expectation. The
probability space is the original uniform random scheduler, recorded as a log of
ordered interaction pairs (including interactions that do not change the
configuration). The population threshold is explicit but astronomically large,
and the constants belong to the formalization (timer `50(L+1)`, `K = 256`), since
the paper leaves its constants `c_k` unspecified.

The proof follows the paper's phase structure but not every step of its
analysis. Phase 3 is entered asynchronously, by an epidemic, so the clock
analysis cannot restart from the synchronized snapshot used in the paper's
Section 6.1; it is redone from the first Phase-3 seed with stopping times
(`asynchronous_clock_estimate`, error `8/n⁵`). The averaging of Phase 3
(`averaging_estimate`, `3/n²`), Phases 0–2 (`phase_zero_two_entry_estimate`,
`2/n²`), the late phases on the small-gap branch (Lemmas 10–14 of the paper,
`smallGap_late_estimate`, `100/n²`), the strong-gap and tie branches
(`strong_continuation_estimate`, `tie_continuation_estimate`) and a recovery bound
from every reachable configuration (`reachable_recovery_estimate`, for the
expectation) are composed by `TimeTheorem.dotyTimeClaim_of_estimates`. The
phase-9 repair of the formalized protocol (r2026.11.4) is a prerequisite: with
the earlier phase-9 Init no O(log n) bound holds.

### Kurtz 1978: strong approximation

Lemma 3.1, `KurtzLemmaThreeOne.kurtz_lemma_three_one`: on one probability
space, a Brownian motion `W` and a unit Poisson process `Y` such that
`K = sup_{t ≥ 0} |Y(t) − t − W(t)| / (log t ∨ 2)` is finite almost surely and
`E exp(λK) < ∞` for an explicit `λ > 0`. The coupling is the dyadic
Komlós–Major–Tusnády construction specialised to the Poisson process: the top
count is coupled with a Gaussian by a Poisson–normal quantile coupling and each
refinement by a Binomial(m, ½)–normal one. The quantile bounds come from the
Serov–Zubkov signed-root intersection inequalities and one-variable calculus, with
no local central limit theorem. Intermediate results are the finite-horizon
coupling with an all-`x` exponential tail
(`continuousTime_arbitraryFiniteHorizonKMT`) and a coarse-block strong invariance
principle (`discrete_sip`).

Theorem 3.3(a), `KurtzTheoremThreeThree.kurtz_theorem_three_three_a`: with one
Lemma 3.1 pair per reaction channel, independent across channels and the same
for every `N`, the chain `X_N` driven by the Poisson processes and the diffusion
`Z_N` of (1.6) driven by the Brownian motions satisfy, almost surely,
`‖X_N(t) − Z_N(t)‖ ≤ β^T log N / N` for all `N ≥ 2` and `t ≤ T` at once, with one
measurable `β^T` having an exponential moment. This is stronger than the printed
form, in which `β_N^T` has a law independent of `N`;
`kurtz_theorem_three_three_a_identicalLaw` states that form. Continuous
solutions `Z_N` are shown to exist for every sample.

Theorem 4.4, `kurtz_theorem_four_four`, takes the paper's Section 4 hypotheses
and nothing else (the record `SectionFourPaperData`). On one coupling space it
constructs the chains `X_N` for every `N ≥ 2` with the original rates, the fluid
limit `X`, strong solutions of (1.7), and one centered Gaussian process `V`
solving its linear equation, and gives for every `T` random variables `γ_N^T`
with a uniform exponential moment such that, almost surely,
`‖√N (X_N(t) − X(t)) − V(t)‖ ≤ γ_N^T log N / √N` for all `N ≥ 2` and `t ≤ T`.
`kurtz_theorem_four_four_covariance` adds the covariance of `V`,
`∫_0^{t∧u} Φ(t,s) Σ(X(s)) Φ(u,s)ᵀ ds`, and
`kurtz_theorem_four_four_paper_witness` shows that the hypotheses are met by a
model with a state-dependent rate. The sharp rate `log N / √N` rests on a
stochastic cancellation: the Itô integral of `√f_l(Z_N) − √f_l(X)` against the
physical Brownian motions. Pathwise arguments alone give a weaker rate. The
proof therefore builds one physical Brownian family first, solves the SDEs
strongly for every `N`, recovers the internal-clock Brownian motions by Knight's
theorem, and attaches Poisson processes to them by transferring the Lemma 3.1
coupling.

Two remarks on the printed proof of Theorem 4.4 came out of this work. They are
paper arguments, not formalized: the compensator of the exponential martingale in
(4.4) is `λ²t/2`; and (4.8) cannot hold for every `λ` (for jumps `±1` and rates
`(2 + tanh x)²/2` it fails for every `λ ≥ 1/(2T)`), but the proof uses it for one
`λ > 0` only, and that is what the formalization proves.

### The stochastic-calculus library

`Ripple/Stochastic/` contains the L² Itô integral for a Brownian motion adapted
to a general filtration and its continuous version on every horizon and on the
half-line; stopping; Doob's maximal inequalities in discrete and continuous time;
the exponential maximal inequality
`P(sup_{t ≤ T} M_t ≥ r, ⟨M⟩_T ≤ q) ≤ exp(−r²/(2q))`; strong existence and pathwise
uniqueness for SDEs with bounded Lipschitz coefficients driven by finitely many
Brownian motions; and Knight's theorem, which turns time-changed stochastic
integrals into independent Brownian motions. It starts from files ported, with
their copyright headers, from formal-mathfin (the L² Itô integral) and from
Degenne et al.'s Brownian-motion and Kolmogorov-extension projects; `NOTICE`
lists them.

### CF'24: a refuted hypothesis

The readout theorems for the CF'24 example from interior initial conditions
assumed `Cf24SaddleExcludedBasinEntry`, the claim that every interior trajectory
off the stable manifold of the interior saddle enters the basin of the target
equilibrium. That claim is false: the vertex `(0, 0, 1)` is a hyperbolic sink
whose open basin contains interior initial conditions with readout limit `1`
(`cf24_saddleExcludedBasinEntry_false`). The readout theorems are restated under
the corrected hypothesis `Cf24CornerExcludedBasinEntry`, which also excludes
convergence to the vertex. The corrected global statement is proved on paper in
`docs/audit/CF24-INTERIOR.md` (Poincaré–Bendixson with a Dulac function); its
planar-topology part is not in Lean.

### Also in this release

The clocked Turing-machine network of SCWB Theorems 3.2 and 4.1 is nonexplosive
from every finite state, and before any fixed number of clock ticks its timed
mass-action law agrees with the canonical Q-matrix CTMC of `Ripple/CTMC/`
(`ctm_noExplosion`, `ctm_identification_up_to_target`).

### Verification

Canonical build of the release tree on one NERSC Perlmutter CPU node: `Ripple`,
`RippleDefault` and `Tri` from scratch (job 61262710), then, after an explicit-binder
fix in `Ripple/Stochastic/StoppedContinuousIto.lean`, an incremental rebuild of that
module and its 17 dependents (job 61264748): 10842 jobs, no error, no `sorry`. The source contains no `sorry`, no named `axiom` and no `native_decide`.
The 24 headline declarations checked, among them `doty_stabilization_time`,
`kurtz_lemma_three_one`, `kurtz_theorem_three_three_a`,
`kurtz_theorem_four_four`, `kurtz_theorem_four_four_covariance`,
`kurtz_theorem_four_four_paper_witness`, `cf24_saddleExcludedBasinEntry_false`
and `ctm_identification_up_to_target`, print only `propext`, `Classical.choice`
and `Quot.sound` under `#print axioms`.

## r2026.11.5 — 2026-11-11 (SCWB Theorem 4.1: Turing machines with unbounded space)

This incremental release proves Theorem 4.1 of Soloveichik, Cook, Winfree and
Bruck, "Computation with finite stochastic chemical reaction networks" (Natural
Computing 7, 2008; Caltech TR etr085v2): a stochastic chemical reaction network
fixed by a Turing machine simulates it over unboundedly many steps and unbounded
space, with cumulative error at most δ, where δ enters only through the initial
count of an accuracy species. With Theorems 3.1, 3.2 (r2026.11.2, r2026.11.3,
completion and continuous time in r2026.11.4) and 4.2, all four theorems of the
paper are now proved in Lean.

### The statement

`ClockedCTM.Unbounded.scwb_theorem_4_1`: for a binary Turing machine `M` whose
blank symbol is `false`, the network `xctmOf M` depends only on `M`. For every
space bound `s ≥ 1` and every `δ ∈ (0, 1]`, start the network with
`i₀ = accuracyIndex (2s + 2) δ ≤ 2s + 4 + 37/√δ` accuracy molecules. Then for
every input of length at most `s`, the probability that the reaction path fails
to pass through a clean encoding of every configuration of the machine's
(possibly infinite) run is at most `1344/(i₀ − 1)² ≤ δ`. The second conjunct,
`TMTimeClaim M`, bounds the expected physical time to the encoding of TM step
`t`, given no error, on the chain with independent exponential holding times:
`552 (s_t + 1) t (37/√δ + 2s + 4 + 6(s_t + 1) t)^5 / ((1 − δ) ρ κ)`, where `s_t`
is the tape length at step `t`, `ρ` the density and `κ` the rate constant
(for `δ < 1` and steps before the machine halts).

The paper gives no network for Theorem 4.1, only the modifications to make to
the bounded-space construction. The network formalized here, its schedule and
its proof are in `docs/audit/FIX3-SCWB-T41.md`; the network repairs the three
defects of the paper's Figure 3.2 that were found for Theorem 3.2.

### How it is proved

The error bound sums, over simulated steps, the probability that a clock tick
arrives before the current window of work is finished. The proof bounds the
expected work in each window (the restoration, read and extension phases) by
potential arguments on the standalone work chain, restarts the raw jump law at
deterministic cuts (`rawLaw_restartLabels`), compares the actual occupation of
the windows with the standalone means (Lemma 8.3), and charges the terminal
clock waiting separately (Lemma 14.4). The general forms are
`errorClaim C : ErrorClaim C` and `timeClaim C : TimeClaim C` for every
extensible clocked CTM.

Two readings of the analysis are false and are refuted in Lean: an occupation
bound over all states that includes terminal clock waiting
(`terminalClockWork_not_all_occupation_le_meanDuration`), and an exact
restoration ratio (`ordinary_restore_ratio_strict_between`: the reachable ratio
lies strictly between 38 and 39). Unconditional tick progress was already shown
false in r2026.11.4 (`TMStarvationWitness`); progress is proved on the no-error
event.

### Scope

The error probability is stated on the embedded jump chain of mass-action
kinetics; the time bound is on the continuous-time chain with exponential
holding times built from it. Identifying that chain with the Q-matrix CTMC of
`Ripple/CTMC/` remains open (`OPEN_PROBLEMS.md` §6.2).

### Verification

Canonical build of the release tree on one NERSC Perlmutter CPU node (`Ripple`,
`RippleDefault` and `Tri` from scratch): 10098 jobs, no error, no `sorry`.
`scwb_theorem_4_1`, `errorClaim`, `timeClaim`, `tmTimeClaim`, `tm_failure_bound`,
`rawStateRestart`, `lemmaEightFourPhases`, `rawLaw_restartLabels` and the two
refutations print only `propext`, `Classical.choice` and `Quot.sound` under
`#print axioms`.

## r2026.11.3 — 2026-11-09 (Ramanujan's 1914 series without hypotheses, the time bound of Kanaya et al. Theorem 4, SCWB Theorem 3.2)

An incremental release on top of r2026.11.2. `CHANGELOG.md` lists every
change and `docs/refactor/STATEMENT-CHANGES.tsv` the restated and renamed
declarations.

### Ramanujan's 1914 series

`Ripple.Number.Ramanujan1914.ramanujan_one_over_pi` now proves

    1/π = (2√2/9801) Σ_{k ≥ 0} (4k)! / (k!)⁴ · (1103 + 26390 k) / 396^{4k}

with no hypothesis. The missing piece was the CM evaluation at level 58,
`1103 F(99⁻⁴)² + 26390·99⁻⁴·(F²)′(99⁻⁴) = 9801/(2√2π)` with
`F = ₂F₁(1/8, 3/8; 1; ·)` (`Modular.ramanujanCM58_evaluation`). Its proof
follows the pattern of the Chudnovsky proof in r2026.11.2, one level down:

- The Hauptmodul `T` of `Γ₀(2)+` satisfies the degree-29 modular equation
  `Ψ₂₉(T(29τ), T(τ)) = 0` (`Modular.psi29_modular_equation`). The kernel
  checks it as the vanishing of a weight-480 form on `Γ₀(58)`: its first
  3601 coefficients are evaluated exactly and a Sturm bound on `Γ₀(N)`
  (`Modular.gamma0_eq_zero_of_coeff`) finishes the argument.
- The point `i√58/2` is fixed by `z ↦ −29/(2z)`, so `T(i√58/2)` is a root
  of `Ψ₂₉(X, X)`; a kernel-checked sign certificate shows it is the only
  root above `1.1·10¹⁰`, which gives `x₂(i√58/2) = 1/99⁴`
  (`Modular.x2_tau58`). The second-order expansion of
  `Ψ₂₉(T(−29/(2z)), T(z)) ≡ 0` at the fixed point gives the CM relation for
  the derivative (`Modular.ramanujan58_cm_relation`).
- The level-2 Kummer identity `2E₂(2τ) − E₂(τ) = F(x₂(τ))²` near `i√58/2`
  (`Modular.Z_sq_eq_gauss`) connects the modular side with the series. It
  is derived from Milla's `E₄ = ₂F₁(1/12, 5/12; 1; 1/J)⁴` (ported in
  r2026.11.2) and two hypergeometric transformations, a quadratic and a
  cubic one, proved by uniqueness of analytic solutions
  (`Hypergeometric.gauss2F1_quadratic`, `gauss2F1_cubic_pow_four`).

The paper notes are in [`docs/audit/CHUD-PAPER.md`](docs/audit/CHUD-PAPER.md)
§4, and the scripts that produced `Ψ₂₉` and its coefficient data in
`docs/audit/evidence/chud/lvl58/`. The former conditional statement is
`ramanujan_one_over_pi_of_cm58`.

### Kanaya et al. Theorem 4: the time upper bound

`P_EM_paper_thm4_time` proves the time part of Theorem 4 of Kanaya et al.
for the paper instance of P_EM (`trank = 40`, `Rmax = ⌈60 ln n⌉`,
`Emax = 208 n`, `Dmax = 32 n`): for `n ≥ 1608` and every configuration of
the finite instance, the expected parallel time to silence is at most
`5215 n`, and the population is silent within `4172 n² ⌈log₂ n⌉`
interactions except with probability at most `1/n`. Together with the
correctness and O(n)-state results of r2026.11.2
(`P_EM_paper_fin_solves_silent_SSEM`, `card_PEMPaperFin_le`), every part
of Theorem 4 is now proved for this instance.

The proof composes one uniform window, `P[silent within 1043 n²] ≥ 1/5`
from every configuration (`P_EM_paper_window`), out of stage bounds for the
two epochs of the paper's analysis: Burman et al. Lemma 3.3 (dormancy,
`P_EM_paper_dormancy_bound`), stage A from every good configuration
(`stageA`), the leader stages (`stageB1`, `stageB2`, `stageB1Z`), tree
ranking, Burman et al. Lemmas 3.3–3.4 in corrected form (`stageB34`), and
the ranked stages (`stageA'`, `stageB56`, `stageC`, `stageE`). The paper
proofs are [`docs/audit/FIX2-BURMAN.md`](docs/audit/FIX2-BURMAN.md),
[`FIX2-P2.md`](docs/audit/FIX2-P2.md) and
[`FIX2-P3.md`](docs/audit/FIX2-P3.md). A statement audit
([`docs/audit/KANAYA-THM4-AUDIT.md`](docs/audit/KANAYA-THM4-AUDIT.md))
compares the Lean statement with the paper's: it is faithful, under the
standard scheduler that picks an ordered pair of distinct agents uniformly
and independently at each step. The finite instances also satisfy
Definition 1 with probability one (`P_EM_paper_fin_kanayaDefinition1`).

### Soloveichik–Cook–Winfree–Bruck Theorem 3.2

The network of the paper's Figure 3.2, which simulates a Turing machine
through a clocked counter machine (CTM), fails as drawn: we found three
defects, each with a proof. With three local repairs it works, and
`ClockedCTM.scwb_theorem_3_2` proves Theorem 3.2 for the repaired network
in the paper's quantifier order: for a binary Turing machine `M` the network
and the count of `A*` are fixed first; then for every `δ ∈ (0, 1]`, input
and step bound `t` within the tape bound there is a count of the accuracy
species `A` with error at most `δ` and expected time at most
`3168 (3/2)^L v s³ t²/(k 3^s δ)`, where `s` is the CTM tape length. For
comparison, SCWB state only `O(v (s+Δ)^{7/2} t^{5/2}/(k 3^{2s+Δ} δ^{3/2}))`,
and the repaired paper analysis gives `2746 (3/2)^{l−1} v s³ t²/(k 3^s δ)`.
A sharper bound in terms of `Θsum` is `scwb_theorem_3_2_of_Θsum`, and
`Θsum_le_log` gives its asymptotics.
Lemma A.9, the simulation of a Turing machine by a CTM, is proved
(`ctm_tracks`). Paper proofs:
[`docs/audit/FIX3-SCWB-T32.md`](docs/audit/FIX3-SCWB-T32.md).

**Caveat for Theorems 3.1 and 3.2.** A statement audit
([`docs/audit/SCWB-T31-T32-AUDIT.md`](docs/audit/SCWB-T31-T32-AUDIT.md))
found that the success events of `scwb_theorem_3_1` (r2026.11.2) and
`scwb_theorem_3_2` are safety predicates: they say that no wrong step
happens before the target step, not that the target step is reached. The
paper's theorems also assert that the computation completes, so the Lean
statements are weaker than the paper's on this point; adding completion to
the success event is in progress. The audit records two further caveats:
probabilities are those of the jump chain of the mass-action process, and
"expected time" is the expected sum of the mean holding times
`1/(total propensity)` along that chain, which is not yet connected in Lean
to a constructed continuous-time process; and `scwb_theorem_3_2` is stated
for the CTM tape length `s`, without the paper's padding parameters.
Theorem 4.1 remains open.

### Build

The default target checks the `Ripple.lean` import closure (600 modules) and
all of `Tri`; the exhaustive `Ripple` target compiles all 1124 Ripple
modules, including the level-58 and SCWB Theorem 3.2 developments. The
release tree was built on one NERSC Perlmutter CPU node, with Mathlib from a
prebuilt cache and Ripple and `Tri` compiled from scratch with 64 compile
threads: `lake build Ripple RippleDefault Tri` completed successfully (5588
jobs) in about 34 minutes of build time over two jobs, the second resuming
incrementally, with no error and no `sorry`. `#print axioms` on 176
headline declarations reports only `propext`, `Classical.choice` and
`Quot.sound`.

## r2026.11.2 — 2026-11-09 (the Chudnovsky formula without hypotheses, SCWB Theorem 3.1, O(n) states for P_EM)

An incremental release on top of r2026.11.1. `CHANGELOG.md` lists every
change and `docs/refactor/STATEMENT-CHANGES.tsv` the restated, renamed and
deleted declarations.

### The Chudnovsky formula

`Ripple.Number.Chudnovsky1989.chudnovsky_one_over_pi` now proves

    640320^{3/2} / (12π) = Σ_{k ≥ 0} (−1)^k (6k)! / ((3k)! (k!)³) · (13591409 + 545140134 k) / 640320^{3k}

with no hypothesis. The proof combines three pieces:

- Milla's proof of the main identity for `Im τ` large enough, which expresses
  the series through `j(τ)` and `s₂(τ) = (E₄/E₆)(E₂ − 3/(π Im τ))`. Xuanji
  Li formalized it in Lean Pool; it is ported under `Ripple/Number/Milla/`
  with its Apache-2.0 headers kept, and `NOTICE` records the origin and the
  changes (`Milla.hauptformel`).
- The CM value `j(τ₁₆₃) = −640320³` at `τ₁₆₃ = (1 + √−163)/2`, already
  verified through the level-41 modular polynomial `Φ₄₁` (the j-evaluation
  chain described in the Technical Report).
- The new value `s₂(τ₁₆₃) = 77265280/90856689` (`Modular.s2_heegnerTau163`).
  `M(z) = 1 − 41/z` fixes `τ₁₆₃`, so `(j(τ₁₆₃), j(τ₁₆₃))` is a node of the
  curve `Φ₄₁(X, Y) = 0`; expanding `Φ₄₁(j(z), j(M z)) ≡ 0` to third order at
  that point determines `s₂(τ₁₆₃)` from finitely many integer partial
  derivatives of `Φ₄₁`, which the kernel checks (`Modular.Phi41TaylorData`).

The paper notes are in [`docs/audit/CHUD-PAPER.md`](docs/audit/CHUD-PAPER.md).
The former conditional statement is `chudnovsky_one_over_pi_of_cm163`.
Ramanujan's 1914 series (`ramanujan_one_over_pi`) stays conditional on a
true level-58 evaluation that is not proved; a false statement about the
Legendre λ value at `i√58/2`, `RamanujanLambda58Statement`, is deleted with
its consumers.

### Soloveichik–Cook–Winfree–Bruck Theorem 3.1

`Clocked.scwb_theorem_3_1` has the paper's quantifier order. For every
register machine `M` the network `net M 1` of the paper's Figure 3.1 is
fixed first; then for every `δ ∈ (0, 1]`, input and step bound `t ≥ 1`
there is an initial count of the accuracy species `A` such that, under the
mass-action jump chain, the first `t` machine steps are simulated correctly
with probability at least `1 − δ`, in expected time at most
`6 v t² / (k δ)`. The clock is analysed in occupation-measure form (a flux
identity and cone invariance by a minimum principle); this also supplies the
"memoryless" step of the paper's Lemma A.4, which its Lemma A.1 proves only
for the clock started at the top. Paper proofs:
[`docs/audit/FIX3-SCWB.md`](docs/audit/FIX3-SCWB.md). Theorems 3.2 and 4.1
(Turing machines) remain open.

### Kanaya et al.: O(n) states, and the first step of the time bound

- `P_EM_fin_silent_SSEM_states`: the Lean P_EM runs on a finite
  role-indexed state type with at most `394 n` states and is silent
  self-stabilizing exact majority for `n ≥ 4`.
- `P_EM_paper_fin_solves_silent_SSEM` and `card_PEMPaperFin_le`: the same
  for the parameters of Kanaya et al. and Burman et al. (constant `trank`,
  `Rmax = ⌈60 ln n⌉`, `Emax = e·n`, `Dmax = d·n`), with O(n) states.
- `P_EM_paper_propagation`, Burman et al. Lemma 3.2: after `⌈4 n ln n⌉`
  interactions from a configuration with a Resetting agent of resetcount at
  least `⌈60 ln n⌉`, the configuration is fully propagating except with
  probability at most `2/n`. The proof replaces the paper's citation by two
  potentials and a product-measure supermartingale lemma
  ([`docs/audit/FIX2-BURMAN.md`](docs/audit/FIX2-BURMAN.md)).

The time upper bound of Theorem 4 is stated for the paper instance
(`KanayaThm4Time`) and remains open.

### Other changes

- `kurtz_finite_horizon` takes the initial condition of Kurtz's theorem: a
  random initial state whose densities converge in probability to `x(0)`;
  `kurtz_finite_horizon_of_close` gives the bound uniformly over
  deterministic initial states near `x(0)`.
- `zero_init_no_collapse` states the eventual lower bound (liminf at least
  `c > 0`); `zero_init_eventually_bounded_below`, which carried that
  statement in r2026.11.1, is removed.

### Build

The default target checks the `Ripple.lean` import closure (568 modules) and
all of `Tri`; the exhaustive `Ripple` target compiles all 1063 Ripple
modules, including the Chudnovsky and SCWB developments. The release tree
was built on one NERSC Perlmutter CPU node, with Mathlib from a prebuilt
cache and Ripple and `Tri` compiled from scratch with 64 compile threads:
`lake build Ripple RippleDefault Tri` completed successfully (5525 jobs) in
about 39 minutes of build time over two jobs, the second resuming
incrementally, with no error and no `sorry`. `#print axioms` on 122 headline
declarations reports only `propext`, `Classical.choice` and `Quot.sound`.

## r2026.11.1 — 2026-11-08 (ζ(3) in real time, bounded analog complexity §§2–7, statements matched to their proofs)

An incremental release on top of r2026.11. It adds results and removes
statements whose names claimed more than their proofs give; it does not
change the computability predicates. `CHANGELOG.md` lists every change and
`docs/refactor/STATEMENT-CHANGES.tsv` the deleted, renamed and restated
declarations.

### Apéry's constant in real time

`Ripple.Number.apery_is_realtime` proves that ζ(3) = ∑ 1/(k+1)³ is
real-time computable for the paper predicate, so it lies in the first floor
of the bounded complexity hierarchy. The witness is a five-variable PIVP
with ℚ-polynomial field and initial value `(1, 0, 0, 1/2, 0)`: ȧ = −a,
ḃ = a − b, ċ = 2b − c, q̇ = a q², Ṡ = (2/3) c q, whose output is
S(t) = (2/3)∫₀ᵗ x²/(1 + eˣ) dx, a Fermi–Dirac integral. Its error is at most
(16/3)e^(−t/2) for t ≥ 0, which gives the modulus μ(r) = 2r + 6
(`fermi_certifiedBoundedTimeComputable`).

### The journal version of the bounded analog complexity paper

Sections 2 to 7 of the journal version of [BAC] are formalized:

- Theorem 4.6 for the definition of Bournez, Graça and Pouly, for numbers
  and for functions on a compact set: poly-length computability gives
  polynomial time for bounded systems, through a shifted-clock compilation
  (`isPolyTimeComputable_of_isBGPPolyLengthComputable`,
  `isPolyTimeComputableOn_of_isBGPPolyLengthComputableOn`).
- Section 5, constructible moduli, with exact moduli: `(r+1)^n − 1`,
  `(r+1) log(r+1)` (through a Lambert function constructed in Lean) and the
  tower `E_{k+1}(r)` (`Constructible.polyFamily_certified`,
  `lambert_certified`, `tower_certified`).
- Theorems 6.1 and 6.4, closure under `α^β` for `α > 0`, with the
  polynomial time classes preserved (`isCRNComputable_rpow`,
  `isPolyTimeComputable_rpow`). The draft's construction assumes that an
  upstream output stays above `−1`, which fails for outputs that are
  negative early, and its modulus `max(μ_α, μ_β) + O(1)` is false; the
  formalized construction drives the filter with the square of the input
  and has modulus `max(max(μ_α(r+C), 0) + r + C, μ_β(r+C))`.
- Section 7, the CRN readout with the modulus relation (`crn_of_certified`):
  a bounded ℚ-PIVP computing `α > 0` gives a mass-action CRN with zero
  initial values and modulus at most `max(μ(r + k), 0) + (4/α + 4α) r + C`,
  by a shift to zero initial values, dual rail and a double-inversion
  readout. Consequences: polynomial-time GPAC and CRN computation agree for
  `α > 0` (`isPolyTimeCRNComputable_iff`), and every `IsCRNComputable`
  number in `[0, 1]` is LPP-computable (`IsCRNComputable.isLPPComputable`),
  for example Euler's γ (`euler_gamma_is_lpp_computable`).

The repaired proofs, with the counterexamples to the draft's steps, are in
[`docs/refactor/BAC2-PAPER.md`](docs/refactor/BAC2-PAPER.md).

### Other new results

- Albenque and Gerin, Theorem 5, in every degree without premises
  (`isEhrenfestComputable_algebraic_of_degree`), using an elementary proof
  of Cassels' divisibility theorem.
- Kanaya et al.: Theorem 2 without the input-oblivious premise
  (`space_lower_bound`), Theorem 3 in expectation and with high probability
  for `n ≥ 2` (`time_lower_bound_omega_n_expected`, `time_lower_bound_whp`),
  and the qualitative part of Theorem 4 (`P_EM_solves_silent_SSEM_linear`).
  The paper's Definition 1 is formalized (`KanayaDefinition1`) and implies
  the reachability forms these theorems use
  (`solvesSSEM_of_kanayaDefinition1`, `silentProtocol_of_almostSure`).
- Kurtz's law of large numbers on `[0, T]` for canonical density-dependent
  chains (`kurtz_finite_horizon`).
- The CF'24 readout limit `(3 − √5)/6` from the canonical initial condition,
  and its λ-trick, r²-trick and NAP-20 lifts (`cf24_readout_canonical`).
- Soloveichik et al. Theorem 4.2 with computable coverability instances.

### Statements removed or renamed

A review of the headline declarations found statements whose names claimed a
paper theorem that their proofs do not give. They are deleted or renamed in
this release, and the paper theorems they named are recorded as open in
`OPEN_PROBLEMS.md` §6:

- Soloveichik–Cook–Winfree–Bruck: 22 reachability wrappers whose conclusion
  holds for every pair of states, 14 wrappers about a network that does not
  depend on the machine, and the two stochastic bounds (one with per-step
  error bound 1, one with a premise that fails for two or more steps).
  Theorems 3.1, 3.2 and 4.1 are open.
- Kanaya et al.: the time upper bound
  `PEM_expected_parallel_time_linear_param`, whose premise is false (the
  timer is unbounded). The time and state bounds of Theorem 4 are open.
- Kurtz: `kurtz_strong_approximation` (premise equals conclusion) and
  `kurtz_clt_second_moment` (fixed `N`, carried bound); two convergence
  statements that assume their key estimate are renamed. The CLT and the
  strong approximation are open.
- CF'24: the readout theorems under the hypothesis `Cf24BasinEntry`, which is
  false (`cf24_basinEntry_false`). The limit from every interior initial
  condition is open.

The erratum `paper/ERRATA.md` now states, for each of the report claims in
its second section, what this release establishes and what remains open.

### Build

The default target checks the `Ripple.lean` import closure (561 modules) and
all of `Tri`; the exhaustive `Ripple` target compiles all 1038 Ripple
modules. The release tree was built on one NERSC Perlmutter CPU node, with
Mathlib from a prebuilt cache and Ripple and `Tri` compiled from scratch with
64 compile threads: `lake build Ripple RippleDefault Tri` completed
successfully (5490 jobs) in about 33 minutes of build time over two 30-minute
jobs, the second resuming incrementally, with no error and no `sorry`.
`#print axioms` on 104 headline declarations reports only `propext`,
`Classical.choice` and `Quot.sound`.

## r2026.11 — 2026-11-08 (faithful computability predicates, bounded compilation, kernel-only certificates)

This release changes what Ripple's central definitions mean, so it is a
breaking release for code that imports Ripple. It does four things:

1. it restates the computability predicates to match the source papers and
   re-proves the results built on them, which corrects statements of the
   Technical Report (see [`paper/ERRATA.md`](paper/ERRATA.md));
2. it proves the bounded surrogate compilation theorems of the bounded analog
   complexity paper;
3. it removes every `native_decide`, so every finite computation is checked
   by the Lean kernel; and
4. it renames and reorganizes the library and makes a from-scratch build fit
   in 16 GB of memory.

### Faithful computability predicates

In `r2026.08`, `IsCRNComputable`, `IsRealTimeComputable` and
`IsPolyTimeComputable` were defined over a semantic PIVP record whose vector
field was an arbitrary function and whose initial value was an arbitrary
real, so each held for every real number (`realtime_const` proved
`∀ c : ℝ, IsRealTimeComputable c`). `IsLPPComputable` allowed an arbitrary
vector field on the simplex and held for every number in `[0, 1]`. Theorems
whose conclusion was one of these predicates were therefore weaker than
their names, even when their proofs built a genuine construction. The
structure `CertifiedBoundedTimeComputable`, a PIVP with a ℚ-polynomial field
and a ℚ initial value, was already faithful and is unchanged.

In `r2026.11`:

- `IsCRNComputable α` is `∃ d, Nonempty (CertifiedBoundedTimeComputable d α)`
  (Definitions 2.1 and 2.3 of the bounded analog complexity paper), and
  `IsRealTimeComputable` and `IsPolyTimeComputable` bound the modulus of such
  a witness linearly or polynomially. `IsRealTimeComputable` equals the
  real-time GPAC class of the DNA 25 paper (`isRealTimeComputable_iff_rtgpac`,
  against the paper-literal `IsRTGPACComputable`: zero initial values,
  integer coefficients, error at most `2^{-t}` for `t ≥ 1`).
- `IsLPPComputable` and `IsPLPPComputable` are the deterministic and
  probabilistic clauses of Definition 9 of the large-population protocol
  paper: a protocol (a transition function, or rational transition
  probabilities), its balance equation, a rational initial point of the
  simplex, and a marked set whose mass tends to the target.
- The semantic record is renamed `SemanticBTC` and is used only as
  infrastructure.

Every result stated with the old predicates was restated with the new ones
and re-proved, deleted, or replaced; the complete list, with a reason for
each entry, is [`docs/refactor/STATEMENT-CHANGES.tsv`](docs/refactor/STATEMENT-CHANGES.tsv).
The main results now proved for the faithful predicates are:

- closure of the real-time class under the field operations
  (`realtime_field_add`, `_mul`, `_neg`, `_sub`, `_inv`, `_div`) and of the
  CRN-computable class under sums and products;
- `e`, `π`, `ln 2`, Euler's `γ` and Catalan's constant are real-time
  computable, with certified ℚ-polynomial systems (new for `e` and `γ`);
- the [LPP] Main Theorem in both directions: `bounded_crn_is_lpp_computable`
  (a certified computation of `α ∈ [0, 1]` with a CRN decomposition gives a
  deterministic LPP) and `lpp_to_gpac`;
- [LPP] Theorem 17 (`isLPPComputable_iff_isPLPPComputable`), Lemma 10
  (`isLPUPComputable_iff_rat`), Lemma 11 (`lpp_product`), Corollary 18
  (`algebraic_lpp_computable`) and the Corollary 19 numbers `π/4`, `1/e`,
  `ln 2`, Catalan's constant and the Dottie number; Ehrenfest urns as
  protocols.

The LPP compiler (`Ripple/LPP/Compiler.lean`) follows the four stages of the
paper with rational coefficients throughout: the saturating filter that
keeps the output below 1, quadraticization by v-variables, the λ-trick with
balancing dilation, an upper-triangular half-product lift that is formally
conservative, and the PP-to-PLPP construction, with a two-fold replication
to read the output. The steps the paper does not spell out are written in
[`docs/refactor/S1-LPP-PAPER.md`](docs/refactor/S1-LPP-PAPER.md), and the
proof of Theorem 17 for the continuum-of-equilibria definition in
[`docs/refactor/S1-THM17.md`](docs/refactor/S1-THM17.md).

**Migration.** Code that built a `BoundedTimeComputable` from a function
field must now give a `PolyPIVP` (an `MvPolynomial` field over `ℚ` and a
rational initial value). Code that consumed `∃ _ : IsLPPComputable α, True`
now receives `IsLPPComputable α`, a `Prop`.

### Bounded surrogate compilation

`Ripple/Core/SurrogateCompilation.lean` and its companions prove
Construction 3.1, Proposition 3.2, Theorems 3.3 and 3.4, Lemmas 4.1 and 4.3,
and Theorems 4.5 and 4.6 of the bounded analog complexity paper. Instead of
eliminating unbounded variables one at a time, the Lean proof uses one joint
time change `dt/dτ = 1/P(y)` with `P = 1 + Σᵢ yᵢ^N` (`N` even, at least the
degree of the field) and the surrogates `W_a = y^a/P` for `|a| ≤ N`, which all
lie in `[−1, 1]`. The compiled system is again a ℚ-polynomial PIVP with a
rational initial value, and its solution is explicit, so no existence theorem
for the compiled ODE is needed.

- `bounded_compilation`: a ℚ-PIVP whose output converges to `α` gives
  `IsCRNComputable α`; `isGPACComputable_iff_isCRNComputable` states that
  bounded and unbounded GPACs compute the same reals.
- `bounded_compilation_of_blowup` and `isCRNComputable_blowupTime`: a solution
  that blows up at a finite time keeps its output limit, and the blow-up time
  itself is computable.
- `bounded_compilation_polyTime`: polynomial time and arc length give a
  polynomial modulus; the product clock `Πᵢ (1 + yᵢ^N)` gives compiled
  dimension `1 + d(N + 1)`.
- `SurrogateCompilationExamples.lean` instantiates the theorems on unbounded
  inputs (`arctan`, a Gaussian, the pole of `tan`), so their hypotheses are
  satisfiable.

[`docs/refactor/BC.md`](docs/refactor/BC.md) gives the paper proofs and lists
steps of the printed proofs that do not go through as written; none of them
changes a theorem. The release also notes in docstrings that
`bounded_surrogate_strong` and `bounded_surrogate_compilation` in
`BoundedUniversality` are vacuous; a faithful bounded compilation of the BGP
Turing-machine simulation is not formalized.

### Trust footprint

Ripple contains no `sorry`, no `axiom` declaration and no `native_decide`.
`native_decide` had 66 uses in 37 files. The largest was the level-41 Sturm
certificate behind the CM-163 evaluation `j((1+√−163)/2) = −640320³`. It is now
a Kronecker-packed big-integer identity that the kernel evaluates
(`SturmPackedEval`). The Fricke involution then halved it: with the symmetry
of Φ₄₁ (`Phi41SymmCheck`), the cleared form `F` satisfies a transformation law
under `S` (`Phi41Fricke`), each non-identity factor of its norm decays like
`F(τ/41)`, and the level-one Sturm bound already applies after 1765
coefficients instead of 3529 (`levelGamma0_41_sturm_weight_1008_of_S`,
argument in [`docs/refactor/FRICKE.md`](docs/refactor/FRICKE.md)). The kernel
evaluation takes about 20 seconds and 2.5 GB. The 3529-coefficient statements
keep their types. The 26 `native_decide` checks of the compiled Γ protocol
are structural proofs and small kernel decisions. The CRT reconstruction
over 251 primes, including the bounded-residue evaluation added after
`r2026.08`, and the `SturmCRT` target are removed.

File-level `maxHeartbeats` raises and scoped raises above four times the
default are gone. The remaining scoped raises are at most four times the
default, and each records its measured heartbeat count.

### Names and layout

Names now state what a result is. Names that recorded how or when a result
was produced (step numbers, `_v2`, `_unconditional`, `Discharge`,
`Capstone`, ...) are replaced, and `Aprey` is spelled `Apery`. About 2,400
declarations, 610 modules and 120 namespaces of `r2026.08` are renamed;
[`docs/refactor/RENAMES.tsv`](docs/refactor/RENAMES.tsv) maps each one.
`Ripple/PopulationProtocol/Majority/` is flattened into
`Ripple/PopulationProtocol/`, `Ripple.Frobenius` is `Ripple.Number.Frobenius`,
and `Tri.Lazy` is `Ripple.Probability.LazyStep`. Where a conditional and an
unconditional form shared a stem, the plain name is now the unconditional
statement (`bounded_crn_is_lpp_computable`, `Tri.Multi.lemma12`,
`modular_poly_41_vanishes_on_diagonal_cm163`).

255 forwarding wrappers whose statement equals their target and 39
declarations whose statement was `True` are removed, together with modules
that no stated result uses (superseded proof routes of the tri-molecular and
stochastic-CRN formalizations, the `Number.Apery` placeholder, and scratch
files). Five standalone modules that did not compile at `r2026.08` now compile,
so the exhaustive `Ripple` target completes.

### Build

The default Lake target checks the `Ripple.lean` import closure (549
modules) and all of `Tri`; the exhaustive `Ripple` target compiles all 1028
Ripple modules, including the Sturm certificate, the CM-163 evaluation and
the Turing-completeness developments. Twenty-six `import Mathlib` lines are
narrowed, which lowers the import floor of the affected modules from about
6.4 GiB to 1.9–3.5 GiB. Measured on the refactored tree (all Ripple and
`Tri` modules, Mathlib from the cache, one CPU node, 16 GB memory limit): 49.9
minutes with 8 compile threads and 29.2 minutes with 16, no out-of-memory
kill, every probed module within 3.87 GiB of its import floor, and a largest
peak of 7.15 GiB.

The release tree was built on one NERSC Perlmutter CPU node, with Mathlib
from a prebuilt cache and Ripple and `Tri` compiled from scratch with 64
compile threads: `lake build Ripple RippleDefault Tri` completed successfully
(5480 jobs; 1028 Ripple and 447 `Tri` modules) in about 34 minutes of build
time over two 30-minute jobs, the second resuming incrementally, with no
error and no `sorry`. `#print axioms` on 63 headline declarations named in
the erratum and among the new results reports only `propext`, `Classical.choice`
and `Quot.sound`.

### Technical Report status

The Technical Report remains exactly `arXiv:2607.13531v2` (21 July 2026). It
is a historical snapshot, and the README now lists it under Publications.
Its statements about LPP computability in §3.3, §3.4, §6.1 and §8 cite
declarations whose conclusion was the former `IsLPPComputable`; the erratum
[`paper/ERRATA.md`](paper/ERRATA.md) explains what they established and
names the corrected declarations. The erratum also records claims of the
report that the cited declarations do not establish and that this release
does not change: the almost-sure and CLT versions of Kurtz's theorem are
reductions, the unconditional stochastic bound for Soloveichik et al. uses a
per-step error bound of 1, the Doty et al. state bound is O(log⁴ n), and the
Kanaya et al. time upper bound has an unsatisfiable or carried hypothesis.
The README now states these results as they are. The report PDF is
unchanged.

### Known limitations

- `zero_init_no_collapse` concludes a lower bound at arbitrarily late times,
  which excludes convergence to 0; the stronger eventual lower bound is
  proved in the same file but not stated as the headline.
- `apery_fermi_is_crn_computable` states convergence of an explicit bounded
  ℚ-polynomial system to ζ(3) for the semantic record; it is not yet stated as
  `IsCRNComputable`, and real-time computability of ζ(3) is conditional.
- Closure of `IsCRNComputable` under `exp` and `log` (bounded analog
  complexity, Theorem 6.1) is taken as hypotheses in
  `closure_exponentiation_via_exp_log`.
- Some generated-data facts about Φ₄₁ in `ModularPoly41` are proved by
  `decide +kernel` over the generated tables.

## r2026.08 — 2026-08-05 (tri-molecular approximate majority)

This release adds `Tri`, a second Lean library formalizing Condon,
Hajiaghayi, Kirkpatrick, and Mañuch's analysis of tri-molecular
approximate-majority chemical reaction networks.

### Paper-facing results

The new public capstones include:

- `Tri.Byzantine.theorem4_entry`, the fully proved corrected
  reached-by-deadline entry clause of paper Theorem 4;
- `Tri.Multi.theorem5`, the unconditional corrected multi-species consensus
  theorem;
- `Tri.Byzantine.lemma8`, allowing history-dependent Byzantine strategies;
  and
- `Tri.Multi.lemma12_unconditional`, covering the full printed species range
  without the absorption premise used by the older proof route.

The release does not assert Theorem 4's additional claim that relaxed
consensus remains preserved for the following `n^γ` interactions. That clause
is false as printed. The explicit counterexample, the corrected statements,
and the remaining paper errata are published in
[`docs/tri/Errata_and_Counterexamples.pdf`](docs/tri/Errata_and_Counterexamples.pdf);
each entry cites both the printed Natural Computing page and the one-based
Springer PDF page.

### Public curation

The snapshot contains the 474-module active import closure rooted at
`Tri.lean`. Private work logs, model transcripts, task specifications,
scratch files, generated objects, source-paper copies, and six orphaned
experimental modules are absent.

`lakefile.toml` registers the `Ripple.lean` import closure and all of `Tri` as
the default build. Existing users can continue to `import Ripple`; users of
the new formalization can `import Tri`. The exhaustive `lake build Ripple`
target remains available for recompiling every standalone Ripple module,
including the optional compute-from-scratch Sturm/CRT certificates, but their
recorded 32-core cold-build cost of 342m48.341s is no longer imposed on
ordinary users.

### Trust and verification

The `Tri` source contains no `sorry`, `admit`, `unsafe`, custom axiom
declarations, or `native_decide`. Its emitted `#print axioms` checks report
only `propext`, `Classical.choice`, and `Quot.sound`, or no axioms. The
repository's pre-existing, explicitly documented `native_decide` uses in the
modular-forms and compiled-constant threads are unchanged.

### Technical Report status

The Technical Report remains exactly `arXiv:2607.13531v2`, dated 21 July
2026. Because the `Tri` library is a substantial later addition, the report is
now labeled as a historical snapshot rather than a complete description of
the live repository.

## v1.0 — 2026-05-08 (Φ₄₁ → CM-163 chain closed)

**0 sorry, 0 named axiom declarations across all six pillars.** `#print axioms` on every headline theorem reports only Lean's three standard axioms.

### Headline

The long-standing `complex_sturm_bound_valence_formula_phi41Level41Cleared`
chain (`Ripple/Number/Modular/ModularPolynomialQExpansion.lean:2751` —
the last open sorry in the Modular pillar) is closed. As a consequence,
the Heegner-class CM evaluation
`j((1 + √-163) / 2) = -640320³` is fully verified in Lean 4 through the
level-41 modular polynomial Φ₄₁.

### What changed

| Commit | Subject |
|---|---|
| `080c9688` | `atkinLehnerInclusion41` — Atkin-Lehner inclusion at level 41 |
| `254deaf2` | `levelOne_cuspForm_eq_zero_of_low_coeffs_vanish` — generic level-1 Sturm bound for arbitrary even k ≥ 4 |
| `e94431d7` | `Phi41ModularFormAssembly.lean` — bundled `phi41Level41ClearedAsModularForm : ModularForm Γ₀(41) 1008` + qExp bridge |
| `eab0efb5` | `Gamma0_41_SturmBound.lean` — partial norm-trick framework |
| `286d65c0` | `phi41Level41SturmBound : 3528 → 3529` (off-by-one fix; classical level-N Sturm at weight 1008 needs 3529 vanishing coefficients, not 3528) |
| `b89c7616` | `levelGamma0_41_sturm_weight_1008` — main Sturm theorem at level 41 weight 1008, via the q-expansion norm bridge `qExp_norm_coeff_zero_of_qExp_coeff_zero` |
| `ec52333d` | `phi41Level41RecurrenceCoeffArrayFirstZero_sturmBound` — finite recurrence-array zero check via `native_decide` |
| `6bb32ab0` | Cleanup: HANDOFFs archived, CHECKPOINT/TODO/WORK_LOG refreshed |
| `2af6ba47` | Removed 30+ obsolete `LevelOneCuspWeight*.lean` files (~7080 LoC) — superseded by `LevelOneSturmGeneric.lean` |
| `8d008407` | Stale doc reference refresh + CRT-route HANDOFF for future kernel-only replacement |

### Build

```bash
cd projects/Ripple
PATH="$HOME/.elan/bin:$PATH" lake build       # 3695 jobs, ~30-45 min from scratch
```

### Trust footprint (important)

The project has **no `sorry`** and **no named `axiom` declarations**.
`#print axioms` on every headline result reports only Lean's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The only
trust beyond the Lean kernel is `native_decide`, used in finitely many
places to discharge large decidable claims:

- `phi41Level41RecurrenceCoeffArrayFirstZero_sturmBound` — first 3529
  entries of the Φ₄₁ cleared q-expansion recurrence array are zero
  (added in this release).
- `phi41Diag_root`, `phi41DiagCofactor_ne_zero` — root and cofactor
  checks for `evalPhi41Diag` at `j(τ₁₆₃)` (pre-existing).
- `(List.range 83).Forall ...` — level-41 difference table vanishes
  (pre-existing).

`native_decide` compiles the decision procedure to native code and
trusts that the result matches what the Lean kernel would compute. The
mathematical content is unchanged; only the verification path differs
from a strict kernel-only proof.

A kernel-only Chinese-Remainder-Theorem replacement is feasible in
principle (see `HANDOFF/crt_route_replace_native_decide.md` for the
plan) but would require either a tighter problem-specific coefficient
bound or a custom reflection evaluator — both research-grade tasks
beyond v1.0 scope. The structural CRT helpers are already in place in
`ModularPolynomialSturmCertificate.lean`.

### Architecture changes

`Ripple/Number/Modular/` shrank from 60 → 25 files:

- **Removed**: `LevelOneCuspWeight{2,4,8,...,70}.lean` (35 files, ~7080
  LoC) and `LevelOneSmallWeights.lean`. These were per-weight cusp-form
  vanishing proofs that have been replaced by the single uniform
  theorem `levelOne_cuspForm_eq_zero_of_low_coeffs_vanish` parametrised
  by `k mod 12 ∈ {0, 2, 4, 6, 8, 10}` (332 lines).
- **Added**: `LevelOneSturmGeneric.lean`, `Phi41Bridge.lean` (extended),
  `Phi41ModularFormAssembly.lean`, `Gamma0_41_SturmBound.lean`,
  `SturmBoundIndex.lean`.

### Non-goals / future work

- **Kernel-only Φ₄₁ certificate** (replacing `native_decide`): see
  `HANDOFF/crt_route_replace_native_decide.md`.
- **Mathlib upstream of `LevelOneSturmGeneric`**: the generic level-1
  Sturm bound for arbitrary even weight could plausibly be contributed
  to Mathlib's `Mathlib.NumberTheory.ModularForms` namespace.
- **`maxHeartbeats 800000` audit**: scattered through the project; some
  could be returned to the 200000 default.
- **CRN library extraction**: split Ripple into reusable
  `CRN.Core` / `CRN.Number` / `CRN.Modular` packages.

### Historical pillars

- `RTCRN1`, `RTCRN2`, `LPP` (DNA28), `BAC` (DNA32) — formalised in the
  Core, ODE, DualRail, and LPP pillars over earlier sessions.
- `Number/Frobenius` — long-term strategic pillar for periods, special
  constants, and holonomic-series-defined numbers (decided 2026-04-21,
  see `STRATEGY.md`).

### Acknowledgements

This release was assembled with extensive collaboration from external
LLM agents (codex, gpt-5.5 high) for matrix algebra grinds and
norm-trick analysis, and a general-purpose subagent for the generic
level-1 Sturm proof. The architectural choices, off-by-one fix,
docstring discipline, and final assembly were directed from the main
Lean session.
