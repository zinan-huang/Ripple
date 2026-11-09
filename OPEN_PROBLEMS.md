# Open Problems in CRN Computable Numbers
## Formalized using the Ripple Framework

### Status Legend
- **PROVED**: Fully verified in Lean (0 sorry, clean axiom trace)
- **STATED**: Statement formalized, proof placeholder / vacuous
- **PARTIAL**: Some components proved
- **OPEN**: Not yet formalized

*Global state (release r2026.11.1):* no `sorry`, no `axiom` declarations and
no `native_decide` in the source; the computability predicates follow the
paper definitions (see `paper/ERRATA.md` for the earlier ones).

---

## 1. Structural Results

### 1.1 LPPs ⊇ bounded CRNs on [0,1] (DNA28 Theorem 8, ← direction)
**Status: PROVED** (`bounded_crn_is_lpp_computable` in
`Ripple/LPP/BoundedLPP.lean`)

Axiom trace: `[propext, Classical.choice, Quot.sound]`. All four DNA28
stages land in the faithful compiler `isLPPComputable_of_certified`
(`Ripple/LPP/Compiler.lean`, r2026.11):
- Stage 1 (v-variable quadraticization, [LPP] Thm 12): `stage1_vvariable_rat`
- Stage 2 (λ-trick, ε-dilation, balancing dilation, [LPP] Thm 13): `stage2_ode_from_room`
- Stage 3 (upper-triangular half-product lift, [LPP] Thm 15 repaired): `symmetricLift`
- Stage 4 (PP → PLPP, [LPP] Construction 1): `SynPPBalance.toPLPPTransitions`,
  composed in `isPLPPComputable_of_stage1`; the deterministic LPP by [LPP] Thm 17
  (`IsPLPPComputable.isLPPComputable`, `Ripple/LPP/Determinization.lean`)

The Stage 2 slack (DNA28 Remark 14 requires `x_out < 1`) is closed
unconditionally via the saturating-surrogate construction in
`Ripple/LPP/SaturatingSurrogate.lean`.

### 1.2 Product Protocol Closure (DNA28 Lemma 11)
**Status: PROVED** (`lpp_product` in `Ripple/LPP/Product.lean`, from the PLPP form
`IsPLPPComputable.mul`; the former `lpp_computable_mul` was a duplicate, deleted in r2026.11)

`z_{i,j} = x_i · y_j` construction over the Cartesian product PIVP.

### 1.3 Unimolecular Protocols Compute Only Rationals (DNA28 Lemma 10)
**Status: PROVED** (`lpup_computes_rational` in `Ripple/LPP/Stages.lean`)

Linear ODE + Cayley-Hamilton + factoring out `x^k` + integration.
Avoids eigenvalue decomposition.

### 1.4 LPP → CRN (easy direction of DNA28 Theorem 8)
**Status: PROVED** (`lpp_to_gpac` in `Ripple/LPP/ToGPAC.lean`)

Augment LPP with readout-sum variable.

---

## 2. Bounded Analog Complexity ([BAC])

### 2.1 Bounded Surrogate Compilation ([BAC] Thm 3.3, Prop 3.2, Thm 3.4, Thm 4.5, Thm 4.6)
**Status: FORMALIZED** (r2026.11; paper proofs and errata in `docs/refactor/BC.md`. Earlier
versions of this file called the theorem "Thm 4.2"; the numbers here are those of the DNA 32
version.)

The joint construction: clock `P(y) = 1 + Σᵢ yᵢ^N` (`N` even, at least the degree of the field),
surrogates `W_a = y^a / P` for `|a| ≤ N`, time change `dt/dτ = 1/P(y)`
(`Ripple/Core/SurrogateCompilation.lean`, `Ripple/Core/TimeChange.lean`).

- [BAC] Thm 3.3: `Ripple.bounded_compilation` (a ℚ-PIVP whose output converges to `α` on
  `[0, ∞)` gives `IsCRNComputable α`), `bounded_compilation_certified` (the certificate is
  pinned to `P.jointSurrogateCompile N`), and `isGPACComputable_iff_isCRNComputable`
  (`Ripple/Core/Compilation.lean`).
- [BAC] Prop 3.2 at a finite blow-up time and [BAC] Thm 3.4 (blow-up times are computable):
  `bounded_compilation_of_blowup(_certified)` and `isCRNComputable_blowupTime(_certified)`
  (`Ripple/Core/SurrogateCompilationBlowup.lean`); the latter compiles to
  `jointClockCompile`, state `(s, (W_a)_a)`, output `s`, so the blowing-up coordinate is not
  kept.
- [BAC] Lemma 4.1, Lemma 4.3: `PolyPIVP.arcLength_le_of_bounded`,
  `PolyPIVP.abs_sub_init_le_arcLength` (`Ripple/Core/ArcLength.lean`).
- [BAC] Thm 4.5 (joint form) and Thm 4.6: `bounded_compilation_polyTime_certified` (modulus at
  most `C' (r+1)^{k(N+1)}`, compiled arc length linear, dimension `jointDim d N ≤ 1 + (N+1)^d`
  by `jointDim_le`) and `bounded_compilation_polyTime`.
- Non-vacuity on unbounded inputs: `Ripple/Core/SurrogateCompilationExamples.lean`
  (`arctanSys`, `gaussianSys`, `tanSys`).
- The product clock `Πᵢ (1 + yᵢ^N)` with per-coordinate surrogates `yᵢ^m/(1 + yᵢ^N)`: compiled
  dimension `1 + d(N+1)` (`productDim_eq`), modulus exponent `k(1 + dN)`
  (`bounded_compilation_productClock_polyTime_certified`,
  `Ripple/Core/ProductClockCompilation.lean`).

Not formalized: a faithful bounded compilation of `BoundedTMSimulates` in `BoundedUniversality`
(`bounded_surrogate_strong` there is vacuous, see its docstring).

### 2.2 Exponentiation Closure (BAC Thm 6.1)
**Status: PROVED** (`isCRNComputable_rpow`, `rpow_certified`, `isPolyTimeComputable_rpow` in
`Ripple/Core/PowerClosure.lean`)

The journal draft's construction needs a repair (its claim `1 + x₁ > 0` fails for upstream outputs
that are negative early) and its modulus `max(μ_α, μ_β) + O(1)` is false; the formalized
construction drives the filter with `x²` and the modulus is
`max(max(μ_α(r+C), 0) + r + C, μ_β(r+C))` (`docs/refactor/BAC2-PAPER.md` §6). The conditional
`closure_exponentiation_via_exp_log` was deleted.

### 2.3 CRN Readout ([BAC] §7)
**Status: PROVED** (`crn_of_certified` in `Ripple/Core/CRNReadout.lean`): a bounded ℚ-PIVP
computing `α > 0` with modulus `μ` gives a mass-action CRN with zero initial values and modulus
at most `max(μ(r + k), 0) + (4/α + 4α) r + C`, through the shift to zero initial values, dual
rail and a double-inversion readout; `isPolyTimeCRNComputable_iff` (polynomial-time GPAC =
polynomial-time CRN for `α > 0`) and `IsCRNComputable.isLPPComputable` follow. The repairs of the
journal draft's §7 are in `docs/refactor/BAC2-PAPER.md` §7. The earlier structural form
`crn_readout_preserves_complexity` (`Ripple/Core/CRNPipeline.lean`) remains.

### 2.4 Real-time classes ([RTCRN2] §3)
**Status: PROVED** (`isRealTimeComputable_iff_rtgpac` in `Ripple/Core/RealTimeGPAC.lean`):
`IsRealTimeComputable` ([BAC] Def 2.3, linear modulus) equals R_RTGPAC, the paper-literal
class `IsRTGPACComputable` (zero initial values, integer coefficients, error `≤ 2^{−t}` for
`t ≥ 1`). [RTCRN2] Thm 2 (R_RTCRN = R_RTGPAC, the CRN side) is not formalised.

### 2.5 Attractor and integral classes (informal question, not a paper result)
**Status: PROVED in syntactic form** (`attractor_iff_integral` in
`Ripple/Number/AttractorIntegralEquivalence.lean`): a number is computed by a certified
system whose output obeys `y' = x_k − y` iff it is `IsCRNComputable` (the relaxation tracker of
`Ripple/LPP/AddRationalPos.lean` with shift 0). Open: a formal "attractor" class with a
fixed-point / stability / basin condition, and whether it is still all of `IsCRNComputable`.

---

## 3. Specific Numbers

### 3.1 ½e⁻¹ is LPP-Computable
**Status: PROVED** (`halfExpNegOne_lpp` in `Ripple/LPP/Example.lean`,
re-exported as `half_exp_neg_one_lpp_computable` in `Stages.lean`)

First transcendental number proved LPP-computable in this framework.

### 3.2 Famous Constants are RT-CRN-Computable
**Status: PROVED** for the faithful `IsRealTimeComputable` (certified ℚ-polynomial systems;
r2026.11)
- `e` (`euler_is_realtime`, `Ripple/Number/Euler.lean`, polynomial system `eulerPolyPIVP`)
- `π/4`, `π` (`pi_quarter_is_realtime`, `pi_is_realtime`, `Ripple/Number/PiCertified.lean`)
- `ln 2` (`ln2_is_realtime`, `Ripple/Number/Ln2Certified.lean`)
- `γ` Euler-Mascheroni (`euler_gamma_is_realtime`, `Ripple/Number/EulerGamma.lean`, the
  8-variable `gammaPolyPIVP`)

### 3.3 ζ(3) is CRN-Computable
**Status: PROVED, real time** (`Ripple.Number.apery_is_realtime`, `Ripple/Number/AperyFermi.lean`)

`apery_is_realtime : IsRealTimeComputable (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3))`, for the faithful
predicate ([BAC] Def 2.1 + Def 2.3 with a linear modulus; the class R_RTGPAC of [RTCRN2] §3 by
`isRealTimeComputable_iff_rtgpac`). The system is the 5-variable Fermi–Dirac PIVP
`fermiPolyPIVP` (ℚ-polynomial field ȧ = −a, ḃ = a − b, ċ = 2b − c, q̇ = a q², Ṡ = (2/3) c q;
rational initial value (1, 0, 0, 1/2, 0)), whose output is S(t) = (2/3)∫₀ᵗ x²/(1+eˣ) dx; the
error is at most (16/3)e^(−t/2) for t ≥ 0 (`fermi_abs_sub_zeta3_le`), so μ(r) = 2r + 6
(`fermi_certifiedBoundedTimeComputable`). This settles the first-floor question for ζ(3).

Still open, separately: the Apéry generating-function route.
`Number.apery_real_time_from_adaptation` (`Ripple/Number/AperyBounded.lean`) states real-time
computability of ζ(3) through Apéry's ODE, conditional on `h_invariant`, `h_z_init` and
`hthree` (not produced). Research notes from `experiments/FINDINGS.md`:
- ODE: `x²(4+x)F''' + x(10+3x)F'' + (2+x)F' = 1`
- Generates ζ(3) via Apéry's generating function
- Obstacle: singular point at `x = 0` needs regularization for PIVP form
- Deeper obstacle (2026-04 finding): MUM singularity is a *universal*
  structural barrier for the Apéry-style generating function, not Apéry-specific

### 3.4 Catalan's Constant is CRN-Computable
**Status: PROVED.** `catalan_is_lpp_computable` and `catalan_is_realtime` in
`Ripple/Number/CatalanCertified.lean`; standard axioms only (`propext`, `Classical.choice`,
`Quot.sound`). Uses the `W := 1 − V` substitution: E, R, W, G satisfy a 4-var
bounded polynomial IVP with `|G(t) − G| ≤ (t+1)·exp(−t)`, wired through
`bounded_crn_is_lpp_computable`.

---

## 4. Research Questions

### 4.1 Can LPP-computable numbers use a single output variable?
Currently requires marking a *set* of states. Is there a single-output
characterization? (DNA28 §4 open question)

### 4.2 Complexity hierarchy for LPP computation
The GPAC→LPP translation introduces at most linear slowdown (from the
balancing dilation). Is this tight? Can we define LPP-analogues of the
bounded complexity floors?

### 4.3 Scarce-variable population protocols
Protocols with some variables at `O(1)` population (not tending to ∞)
escape Kurtz's theorem. What can they compute? (DNA28 §4)

### 4.4 Black-and-white k-PPs
Two-state k-PPs with restricted products can compute some algebraic
numbers (e.g., `(3-√5)/2`) but not all rationals (e.g., not `1/5`).
Exact characterization is open.

### 4.5 PP → NAP construction: is it general?
**Status: OPEN** (raised by X. Huang, 2026-04-19: there are examples that convert successfully,
but it is not clear that the method is general.)

`Ripple/LPP/NAP.lean` formalizes the monomial-level splitting-feasibility combinatorics
(`nap_splitting_feasibility`, `pure_power_split`, `mixed_support_split`), and
`SynPPBalance.nap_split_via_lambdaLift` gives a balanced non-autocatalytic split for every
positive coefficient of the λ-lifted field of a syntactic PP. The section "Connection to Stage 3
Self-Product" of the file analyses the Stage 3 self-product PP in prose; no protocol-level NAP
theorem is stated.

**Open sub-goals**:
- Formalize an `IsNAP` protocol-level predicate
- Theorem: "for any 4-PP π satisfying [strict no-self-prod OR pipeline+foreign],
  cubing(π) is a NAP"
- Theorem (stronger): "for any PP π, cubing(r²-trick(π)) is a NAP" — or
  identify the PP class for which this holds

---

## 5. Infrastructure Priorities

1. **Polynomial degree tracking** — Stages 1-3 of the LPP construction
   reason about polynomial degree and homogeneity informally. A syntactic
   layer for degree-bounded polynomials would make a few ad-hoc arguments
   systematic.

2. **Simplex invariance** — Many LPP proofs need the fact that the
   probability simplex `{x ≥ 0, Σx_i = 1}` is invariant under conservative
   systems. Currently re-derived per callsite.

---

## 6. Cited-paper results not formalized

### 6.1 Kanaya et al. 2025, Theorem 4: time and state bounds of P_EM
**Status: OPEN.** Paper: arXiv:2503.17652v1, §5.2, Theorem 4 and Lemma 14: `P_EM` is silent SSEM, uses O(n) states,
and becomes silent within O(n) expected and O(n log n) w.h.p. parallel time.

Proved: the qualitative part, `P_EM_solves_silent_SSEM_linear`
(`Ripple/PopulationProtocol/SSEM/Convergence/SilentPEM.lean`), for `n ≥ 4`.

Open:
- **O(n) states.** The Lean state type `AgentState n` is a product with five unbounded
  `ℕ` fields (`resetcount`, `timer`, `children`, `errorcount`, `delaytimer`) shared by all
  roles, so it is infinite, and the paper's count (a sum over roles of bounded variables,
  with `Rmax = 60 log n`) is not expressible. Needed: a finite state type (bounded counters,
  role-dependent variables), the transition restricted to it, and the convergence proof
  transported to it.
- **O(n) expected / O(n log n) w.h.p. silence time.** Not proved. The Lean protocol also
  instantiates the timer parameter `trank` by `n` (timer range `7(n+4)`), where the paper
  takes `trank = O(1)`. The former `PEM_expected_parallel_time_linear_param` assumed a
  false global timer bound and was deleted. What remains is the conditional
  `PEM_expected_parallel_time_from_phase_bounds` (`SSEM/UpperBound.lean`; four phase
  lemmas as hypotheses, O(Rmax · n)).

### 6.2 Soloveichik–Cook–Winfree–Bruck 2008, Theorems 3.1, 3.2, 4.1: error-bounded simulation
**Status: OPEN.** Paper: "Computation with finite stochastic chemical reaction networks",
Caltech technical report etr085v2;
Natural Computing 7 (2008) 615–633.

- **Theorem 3.1.** For any register machine there is an SCRN such that for every δ > 0,
  input and step bound t, some initial amount of the accuracy species A gives cumulative
  error probability at most δ, in expected time O(v t² / (k δ)).
- **Theorem 3.2.** The same for any Turing machine and bound s_tm on its space (padding ∆).
- **Theorem 4.1.** For any Turing machine and δ > 0, an SCRN simulates it on inputs of size
  at most s_tm0 with cumulative error at most δ over unboundedly many steps and unbounded
  space.

Proved: Theorem 4.2 (coverability is decidable, a computable procedure:
`Decidability.petriCoverabilityDecidable`, `Decidability.networkCoverabilityDecidable`);
one-instruction facts for the register-machine network without clock
(`RegisterMachine.rmNetwork_reaches_successor`, `rm_error_source_characterization`,
`rm_correct_when_zero`); lemmas for the clock and the error series (`Stochastic/ClockCRN.lean`,
`GamblersRuin.inv_geometricSum_*`, `UnboundedError.*`, `MassAction.rawLaw`).

Open: the clock module and its analysis (paper Appendix, Lemmas A.1–A.3), a network fixed by
the machine with the clock output as catalyst of the zero branch, and the error bound under
the mass-action law (Lemma A.4 for registers; A.5–A.9 for the Turing-machine theorems). The former paper-facing statements were removed in r2026.11.1: the 22
`PaperTheorems.exists_*` wrappers (conclusion true for every pair of states), the
`PaperTheorems.statePairTransfer_*` wrappers (the named network does not depend on the
machine), `scwb_stochastic_bound` (error bound 1) and
`scwb_stochastic_bound_of_enabled_of_clock` (premise `hEnabled` unsatisfiable for n ≥ 2).

### 6.3 CF'24 protocol: readout limit from every interior initial condition
**Status: OPEN (not a claim of the cited paper).** The PP-to-NAP note claims the readout limit `(3 − √5)/6` from the canonical
initial condition `(1, 0, 0)`; that is proved (`Ripple/LPP/CF24Canonical.lean`,
`cf24_readout_canonical` and its λ, r², NAP-20 lifts). The stronger statement, the same
limit from every interior initial condition off the stable manifold of the interior saddle
(`Cf24SaddleExcludedBasinEntry` in `Ripple/LPP/CF24Example.lean`), is open: it needs a
global argument (stable-manifold theorem plus a Poincaré–Bendixson-type exclusion of other
ω-limits, or a globally valid Lyapunov function). The conditional theorems
`cf24_*_of_saddleExcludedBasinEntry` remain as lemmas, not roots. The earlier hypothesis
`Cf24BasinEntry` is false (`cf24_basinEntry_false`); the theorems that assumed it were deleted
(r2026.11.1).

### 6.4 Doty et al. 2021, Theorem 3.1: state count and stabilization time
**Status: OPEN.** Paper: arXiv:2106.10201v2, Theorem 3.1:
the protocol Nonuniform Majority uses O(log n) states and stably computes majority in
O(log n) stabilization time, in expectation and with high probability.

Proved: stable computation (`ExactMajority.stable_majority_correct`, `…_fixed_size`,
`…_clog`). The Lean state type `AgentState L K` is a flat record whose cardinality is
`state_count_eq`, of order (L+1)⁴ = O((log n)⁴) (`state_count_poly_bound`).

Open:
- **O(log n) states.** The paper's count uses that each role and phase uses only some fields.
  Needed: either a phase- and role-indexed state type with the transition and the
  correctness proof transported to it, or a bound of order L on the set of states that
  occur in configurations reachable from valid initial configurations.
- **O(log n) stabilization time** (expected and w.h.p.). No statement exists: the
  development has no random scheduler and stopping-time API for this protocol
  (`Analysis/MainTheorem.lean`, time-part comment). The phase analyses in
  `ExactMajority/Probability/` are conditional on carried hypotheses.

### 6.5 Kurtz 1971 and 1978: central limit theorem and strong approximation
**Status: OPEN.** Papers: Kurtz, J. Appl. Prob. 8 (1971) 344–356 (CLT: `√N (X_N − x)`
converges to a Gaussian diffusion); Kurtz, Stoch. Proc. Appl. 6 (1978) 223–240 (strong
approximation: a coupling with `sup_{t ≤ T} |N X_N(t) − N x(t) − W(t)| = O(log N)` a.s.).

Proved: the law of large numbers on `[0, T]` (Kurtz 1970, Thm 3.1) for canonical
density-dependent CTMCs, `Kurtz.kurtz_finite_horizon` (`Ripple/Kurtz/FiniteHorizon.lean`).

Open:
- **CLT.** Needs weak convergence of processes in the Skorokhod space and the Gaussian limit;
  neither exists in the development. The former `kurtz_clt_second_moment` (fixed `N`, carried
  second-moment hypothesis) was deleted.
- **Strong approximation.** Needs the KMT coupling for Poisson processes. The former
  `kurtz_strong_approximation` assumed its conclusion and was deleted.
- **`DensityProcessFamily`** (`Ripple/Kurtz/Defs.lean`) has no constructor; theorems taking
  it (`kurtz_convergence_for_density_process_family`) are conditional. A constructor from the
  canonical chains would follow from the proof of `kurtz_finite_horizon`.

---

*Status as of release r2026.11.1.*
*Papers: [RTCRN1] Nat.Comput.2018, [RTCRN2] DNA25, [LPP] DNA28, [BAC] DNA32.*
