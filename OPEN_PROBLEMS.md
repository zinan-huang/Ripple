# Open Problems in CRN Computable Numbers
## Formalized using the Ripple Framework

### Status Legend
- **PROVED**: Fully verified in Lean (0 sorry, clean axiom trace)
- **STATED**: Statement formalized, proof placeholder / vacuous
- **PARTIAL**: Some components proved
- **OPEN**: Not yet formalized

*Global state (release r2026.11.8):* no `sorry`, no `axiom` declarations and
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
**Status: ANSWERED, PROVED at the mean-field ODE level (r2026.11.7).** Raised by X. Huang,
2026-04-19: there are examples that convert successfully, but it was not clear that the method is
general.

Answer: the construction is general, with a different routing. Rewriting each positive monomial of
the cubed field independently (the per-monomial splitting of `Ripple/LPP/NAP.lean`,
`nap_splitting_feasibility`) gives an ODE that is correct on the Veronese image but in general is
not the balance field of any protocol: the net coefficient of a pair summed over all species need
not vanish. The reactions are instead routed by a transportation (supply/demand) construction per
degree-6 monomial (`Ripple/LPP/NAPTransport.lean`). In Lean (`Ripple/LPP/NAP*.lean`):

- protocol-level `NAPProtocol.IsNAP`, `balanceField_conservative`, and an explicit 141-reaction NAP
  for the cubed CF'24 example (`cf24Cubing_isNAP`, `cf24Cubing_eq_napField_on_cubed`);
- cubing an arbitrary syntactic quartic protocol `f`: a non-negative NAP realisation exists when
  (C1) `[y³k] f_y ≤ 0` and (C2) `[y³k] f_k + 2 [y⁴] f_y ≤ 0` for all species `y ≠ k`
  (`exists_nap_realizing_of_C1C2`); a realisation forces non-positive demand at every monomial all
  of whose splittings contain the species (`realizes_nonpos_of_unique_pair`). Not every quartic protocol cubes to a NAP:
  `3y + k → 4y` violates (C1) and has no realisation (on paper);
- the pipeline: for every syntactic quadratic PP, the slack trick, the r²-trick and cubing satisfy
  (C1), (C2) (`exists_nap_realizing_pipeline`), and the NAP trajectory from the lifted initial
  point is the Veronese image of a time-changed PP trajectory, with the same readout limit and the
  exponential rate transferred when the slack has a positive limit (`pp_to_nap_ode_of_init`,
  `pp_to_nap_ode_of_init_set`);
- the squaring variant (r-trick and degree-2 lift) is NAP-realisable iff no homodimer raises the
  mass of the shrunk set (`squaring_iff`); CF'24 gives a 10-species instance (`cf24_sq_of_init`);
- with exchange reactions the lifted image is normally attracting at every equilibrium, interior
  (`normal_stability_interior`) or on the boundary (`normal_stability_boundary`), for every exchange
  rate above some `K₀`;
- `{0, 1}` readouts: three layer copies read the original number with the original clock
  (`LayerCopy.pp_to_nap_layer_copy_of_init`, exact exponent `pp_to_nap_layer_copy_exact`); a
  marked set of cubic species carries the cube of the original marked mass
  (`pp_to_nap_marked_cube_of_init_set`); no fixed `{0, 1}` subset of the cubic species reads the
  original marked mass on the whole simplex (`MarkedObstruction.no_marked_readout_on_simplex`).

**Open sub-goals**:
- Stochastic (finite-population) semantics: all statements are at the mean-field ODE level
- A quantitative, sharp exchange threshold `K₀` (Lean gives existence only)
- Minimal numbers of species and reactions

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
**Status: FORMALIZED** (r2026.11.3) for the paper instance with `trank = 40`,
`Emax = 208 n`, `Dmax = 32 n`, `n ≥ 1608`. Paper: arXiv:2503.17652v1, §5.2, Theorem 4 and Lemma 14: `P_EM` is silent SSEM, uses O(n) states,
and becomes silent within O(n) expected and O(n log n) w.h.p. parallel time.

Proved: the qualitative part, `P_EM_solves_silent_SSEM_linear`
(`Ripple/PopulationProtocol/SSEM/Convergence/SilentPEM.lean`), for `n ≥ 4`.

Open:
- **O(n) states: proved for the Lean instance.** `P_EM_fin_silent_SSEM_states`
  (`Ripple/PopulationProtocol/SSEM/Convergence/FiniteStatePEM.lean`): for `n ≥ 4` the Lean
  P_EM (`trank = Rmax = Emax = Dmax = n`), run on the role-indexed finite type `PEMFinState`
  (one summand per role, each with only the fields that role reads; timer only at the median
  rank), solves silent SSEM (`SolvesSilentSSEM`, reachability form) with at most `394 n`
  states. The transition reads only those fields (`transitionPEM_relPEM`, needs `1 ≤ Rmax`,
  `2 ≤ Dmax`).
- **Definition 1 with probability one:** on the finite state type reachability gives
  probability one, so both finite instances satisfy `KanayaDefinition1` literally
  (`P_EM_fin_kanayaDefinition1`, `P_EM_paper_fin_kanayaDefinition1`) and are silent almost surely
  (`P_EM_paper_fin_silent_almostSurely`); `SSEM/UpperBound/SimulationTransfer.lean`. The
  reachability caveat applies only to the flat (infinite) state space.
- **The paper's parameters: correctness and states proved.**
  `protocolPEMPaper n trank e d` (`SSEM/UpperBound/PaperInstance.lean`) is P_EM with a constant
  `trank`, `Rmax = ⌈60 ln n⌉`, `Emax = e·n`, `Dmax = d·n`; `P_EM_paper_fin_solves_silent_SSEM`:
  for `n ≥ 4`, `d ≥ 1`, its finite version `protocolPEMPaperFin` is silent SSEM, with
  `card_PEMPaperFin_le` states (`O(n)` for constant `trank, e, d`). The time part is stated
  on the finite protocol as `KanayaThm4Time` (`KanayaThm4TimeExpected`: expected parallel time
  to silence `≤ c₁ n` from every configuration; `KanayaThm4TimeWhp`: not silent after
  `c₂ n² ⌈log₂ n⌉` interactions with probability `≤ 1/n`). Proved (next item).
- **O(n) expected / O(n log n) w.h.p. silence time: proved.**
  `P_EM_paper_thm4_time : KanayaThm4TimeExpected 40 208 32 1608 5215 ∧
  KanayaThm4TimeWhp 40 208 32 1608 4172` (`SSEM/UpperBound/Thm4Final.lean`): for `n ≥ 1608` and
  every configuration of the finite paper instance, expected parallel time to silence `≤ 5215 n`,
  and silence within `4172 n² ⌈log₂ n⌉` interactions except with probability `≤ 1/n`;
  `kanayaThm4Time : KanayaThm4Time` is the existential form. It is assembled from the uniform
  window `P_EM_paper_window` (P3 Theorem W, `P[silent within 1043 n²] ≥ 1/5`), itself composed
  of the stage bounds `stageA`, `stageA'`, `stageB1`, `stageB2`, `stageB34`, `stageB56`, `stageC`,
  `stageB1Z`, `stageB2M`, `stageB34M`, `stageB56M`, `stageE` (Burman 3.3–4.3 and Kanaya
  Lemmas 7–14 in their corrected form). Non-vacuity: `docs/audit/probes/ProbeKanayaThm4.lean`. Statement audit:
  `docs/audit/KANAYA-THM4-AUDIT.md`.
  History: the Lean protocol also
  instantiates the timer parameter `trank` by `n` (timer range `7(n+4)`), where the paper
  takes `trank = O(1)`. The former `PEM_expected_parallel_time_linear_param` assumed a
  false global timer bound and was deleted. What remains is the conditional
  `PEM_expected_parallel_time_from_phase_bounds` (`SSEM/UpperBound.lean`; four phase
  lemmas as hypotheses, O(Rmax · n)). The target is now `KanayaThm4Time` for the paper
  instance above; the missing input is Burman et al. (PODC 2021, arXiv:1907.06068v5) Thm 4.3 with Lemma 3.2 and Cor. 3.5. Paper phase:
  `docs/audit/FIX2-BURMAN.md`. Paper side complete: every node has a paper proof checked
  by a second reader and an independent review; the uniform window is
  `P[silent within 1043 n²] ≥ 0.2` for `trank = 40`, `e = 208`, `d = 32`, `n ≥ 1608`, which gives
  `KanayaThm4Time` with `c₁ = 5213`, `c₂ = 4172` on paper (Lean: `c₁ = 5215`, from `1043 · 5`). Several printed statements of Kanaya et al.
  (Lemmas 7, 8, 9, 11, 14) and of Burman et al. (Lemma 4.2) are false or vacuous as printed and
  are corrected there. Lean: Burman Lemma 3.2 proved (`P_EM_paper_propagation`,
  `SSEM/UpperBound/PropagationPaper.lean`); the remaining nodes (Burman 3.3–4.3 and Kanaya
  Lemmas 7–14 in their corrected form) are formalized as the stage bounds above.

### 6.2 Soloveichik–Cook–Winfree–Bruck 2008, Theorems 3.1, 3.2, 4.1: error-bounded simulation
**Status: Theorems 3.1, 3.2 and 4.1 PROVED in Lean (3.2 and 4.1 for the repaired networks;
success events include completion; also on the continuous-time chain; Theorem 4.1 since
r2026.11.5).** Paper: "Computation with finite stochastic chemical reaction networks",
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

Paper proofs (`docs/audit/FIX3-SCWB.md`, independently reviewed): Theorem 3.1 complete,
via an occupation-measure form of the clock analysis (cone invariance by a minimum principle;
this also closes the paper's "memoryless" step in Lemma A.4, which Lemma A.1 proves only for
the clock started at the top): error `≤ t/(1 + a + … + a^{l−1})`, expected time
`≤ 2t(1 + a + … + a^{l−1}) v/k`; Theorem 3.2 sketched with a better error and time bound than
the paper's; Theorem 4.1 has no network in the paper (only modifications are described).
Lean: the clock lemmas (`Stochastic/ClockOccupation.lean`), the one-step Markov property of
`rawLaw` on prefix events (`Stochastic/MassAction/PrefixMarginal.lean`), and Theorem 3.1 with
the paper's quantifier order (`RegisterMachine/Clocked/Theorem.lean`, `scwb_theorem_3_1`):
the network `net M 1` is fixed by `M`; for every `δ ∈ (0, 1]`, input `y₀` and `t ≥ 1` there is
`a` with `P(first t steps simulated incorrectly) ≤ δ` and expected time `≤ 6 v t²/(k δ)`;
general clock length `theorem_3_1_general` (Theorem 3.1′). Expected time is the expected
holding time in non-halted states before `t` machine reactions; the clock starts at `C_l`.

Theorem 3.2 (paper proof, independently reviewed): `docs/audit/FIX3-SCWB-T32.md`. The network
of Fig. 3.2 as drawn fails (microstep 4 always yields the wrong tape count; the tick's `I` is
captured outside microstep 3; `S_{j,4}` is ambiguous); with three local repairs Theorem 3.2′
holds with explicit constants (Lemmas A.5–A.7 with constants, A.9 proved directly), expected
time `O(v (s_tm+∆)³ t_tm²/(k 3^{2s_tm+∆} δ))`. Theorem 4.1 (paper proof, independently reviewed,
`docs/audit/FIX3-SCWB-T41.md`): explicit network, statement and proof (network fixed by the TM; δ only
through the initial count of `A`; `P(Err) ≤ 1344/(i₀−1)²`; expected time given correctness
`≤ 552 (s_tm+1) t_tm (37δ^{−1/2} + 2s_tm0 + 4 + 6(s_tm+1)t_tm)^5/((1−δ) ρ_v k)`).

Lean, Theorem 3.2 (`ClockedCTM/TMtoCTM.lean`, `scwb_theorem_3_2`): binary TM with blank
`false`, halting by `delta = none`; network fixed by the TM and `L`, then `#A*`, then δ, input
and `t`; error `≤ δ`, expected time, with CTM tape length `s = 2 Lc`,
`≤ 2880 (3/2)^L v s² t² (1 + (s−1) ln 3)/(k 3^s δ) ≤ 3168 (3/2)^L v s³ t²/(k 3^s δ)` (repaired paper
analysis `docs/audit/FIX3-SCWB-T32.md`: `2746 (3/2)^{l−1} v s³ t²/(k 3^s δ)`; SCWB's printed Theorem 3.2 states only
`O(v (s+Δ)^{7/2} t^{5/2}/(k 3^{2s+Δ} δ^{3/2}))`). Since r2026.11.4 the success events include
completion (the statement audit `docs/audit/SCWB-T31-T32-AUDIT.md` had found them safety-only):
`Simulates` in Theorem 3.1 requires `t` machine reactions or halting, and `TmSimulates` in
Theorem 3.2 requires tick `4N` drawn with the TM configuration after `t` steps encoded there. The
sharper `Θsum` form is `scwb_theorem_3_2_of_Θsum`; `Θsum_le_log` proves `Θsum(n) = O((1 + ln m)/m)`.

Continuous time (`sCRNUniversality/CTMCBridge.lean`): `timedLaw` is the law of the mass-action
CTMC with independent unit exponential clocks; its expected elapsed time is the holding-time
functional above (`lintegral_registerElapsed`); Theorems 3.1 and 3.2 hold on it with the same
constants (`scwb_theorem_3_1_timed`, `scwb_theorem_3_1_ctmc_stop`, `scwb_theorem_3_2_timed`,
`scwb_theorem_3_2_ctm_timed`).

Lean, Theorem 4.1 (r2026.11.5, `ClockedCTM/UnboundedClockOccupation.lean`,
`scwb_theorem_4_1`): for a binary TM `M` with blank `false`, the network `xctmOf M` depends only
on `M`; for every space bound `s ≥ 1` and `0 < δ ≤ 1`, the initial accuracy count
`i₀ = accuracyIndex (2s+2) δ ≤ 2s + 4 + 37/√δ` gives, for every input of length at most `s`,
`P(the run fails to visit a clean encoding of every configuration of the unbounded TM run)
≤ 1344/(i₀−1)² ≤ δ`; and `TMTimeClaim M`: on the chain with exponential holding times, the
expected physical time to TM step `t` given no error (for `δ < 1` and every `t` before the TM
halts) is at most
`552 (s_tm+1) t (37/√δ + 2s + 4 + 6(s_tm+1)t)^5/((1−δ) ρ κ)` (`s_tm` the TM tape length at step
`t`, `ρ` the density, `κ` the rate constant). The XCTM forms `errorClaim C : ErrorClaim C` and
`timeClaim C : TimeClaim C` hold for every extensible clocked CTM. Layers: the deterministic
layer (`ExtensibleCTM.lean`), the network and statements (`Unbounded.lean`), the error series and
"no error and progress imply correct simulation" (`UnboundedError.lean`), the window analysis and
Lemma 8.3 (`UnboundedWindow.lean`, `UnboundedOccupation.lean`), the time reducers
(`UnboundedTime.lean`), the work-duration and restart layer (`UnboundedRestart.lean`), the Markov
restart of the raw law after a deterministic cut with the W2/W4 work durations
(`UnboundedMarkov.lean`), and the actual clock occupation with the active-window volume
(`UnboundedClockOccupation.lean`). Two readings of the paper note fail and are refuted in Lean:
unconditional tick progress (a reachable starvation trap, `TMStarvationWitness`), so progress is
conditioned on the no-error event; and an occupation bound over all states, including terminal
clock waiting (`terminalClockWork_not_all_occupation_le_meanDuration`), so terminal clock time is
charged separately (Lemma 14.4). The error is stated on the embedded jump chain. Since r2026.11.6 the
chain is tied to the Q-matrix CTMC of `Ripple/CTMC/` (`CTMGlobalNonexplosion.lean`): the clocked
network is nonexplosive from every finite state (`ctm_noExplosion`), and before the `K`-th clock tick,
for every `K`, its timed mass-action law agrees with the canonical record law of a finite Q-matrix
localization, with elapsed time equal to the first exit time (`ctm_identification_up_to_target`).

The former paper-facing statements were removed in r2026.11.1: the 22
`PaperTheorems.exists_*` wrappers (conclusion true for every pair of states), the
`PaperTheorems.statePairTransfer_*` wrappers (the named network does not depend on the
machine), `scwb_stochastic_bound` (error bound 1) and
`scwb_stochastic_bound_of_enabled_of_clock` (premise `hEnabled` unsatisfiable for n ≥ 2).

### 6.3 CF'24 protocol: readout limit from every interior initial condition
**Status: statement as posed REFUTED (r2026.11.6); corrected statement proved on paper, open in Lean
(not a claim of the cited paper).** The PP-to-NAP note claims the readout limit `(3 − √5)/6` from
the canonical initial condition `(1, 0, 0)`; that is proved (`Ripple/LPP/CF24Canonical.lean`,
`cf24_readout_canonical` and its λ, r², NAP-20 lifts). The stronger statement, the same limit from
every interior initial condition off the stable manifold of the interior saddle
(`Cf24SaddleExcludedBasinEntry`), is false: the vertex `(0, 0, 1)` is a hyperbolic sink with an
open basin of interior initial conditions whose readout tends to `1` (`Ripple/LPP/CF24Interior.lean`,
`cf24_saddleExcludedBasinEntry_false`, `cf24_corner_readout_tendsto_one`; for example
`(1/200, 1/200, 99/100)`). Proved on paper ([`docs/audit/CF24-INTERIOR.md`](docs/audit/CF24-INTERIOR.md),
Theorem A): every interior trajectory converges to exactly one of the target equilibrium (readout
`(3 − √5)/6`), the vertex `(0, 0, 1)` (readout `1`), or the saddle (only on its stable manifold);
the first two occur on open sets. Tools: Poincaré–Bendixson on the invariant triangle, the Dulac
function `a^(−4/3)` (in Lean: `Ripple/LPP/CF24Dulac.lean`, `cf24_dulac`, with the repelling source
`cf24_source_repelling`), an explicit trapping region at the vertex, and the sharp Lyapunov basin
at the target. Open in Lean: Corollary A′, `Cf24CornerExcludedBasinEntry` (an interior trajectory
that converges neither to the saddle nor to `(0, 0, 1)` enters the sharp basin); it needs ω-limit
sets, Poincaré–Bendixson and Green's theorem, none of which is in Mathlib. The readout theorems
`cf24_*_of_cornerExcludedBasinEntry` take it as hypothesis. The earlier hypothesis `Cf24BasinEntry`
is false as well (`cf24_basinEntry_false`; the theorems that assumed it were deleted in r2026.11.1).

### 6.4 Doty et al. 2021, Theorem 3.1: state count and stabilization time
**Status: PROVED (states r2026.11.4, time r2026.11.6, one protocol r2026.11.7).** Paper:
arXiv:2106.10201v2, Theorem 3.1:
the protocol Nonuniform Majority uses O(log n) states and stably computes majority in
O(log n) stabilization time, in expectation and with high probability.

Proved: stable computation (`ExactMajority.stable_majority_correct`, `…_fixed_size`,
`…_clog`) on the flat state type `AgentState L K` (cardinality `state_count_eq`, of order
(L+1)⁴, `state_count_poly_bound`), and the **O(log n) state count**: the compact state type
`Compact.CompactState L K` (one live Θ(L) field per role and phase) carries the induced protocol
`Compact.NonuniformMajorityCompact L K`, which stably computes majority on the same validity
domain (`Compact.compact_stable_majority_correct`, `…_clog`, through the state simulation
`StateSimulation.stablyComputes`), and
`Compact.card_compactState_le : Fintype.card (CompactState L K) ≤ 73920 ((K + 53)(L + 1) + 4)`.
The phase-9 Init of the formalized protocol read a frozen field (fixed in r2026.11.4; see the
changelog); with that defect no O(log n) bound could hold.

Proved (r2026.11.6; constants of r2026.11.7): the **O(log n) stabilization time**,
`StabilizationTime.exact_majority_stabilization_time : TimeTheorem.StabilizationTimeClaim`
(formerly `DotyStabilizationTime.doty_stabilization_time`), with no hypotheses.
For `L = ⌈log₂ n⌉`, `K = 256`, every `n ≥ 5·2^(2^23)` and every valid input configuration of size
`n`, the number `τ_D` of interactions until the first stable endpoint with the correct output
(`StableDone`) satisfies `P(τ_D > 16300 n (⌈log₂ n⌉ + 1)) ≤ 110 n⁻²` and
`E τ_D ≤ 470 235 n ln n`, under the uniform random scheduler on the ordered-pair log. The
population threshold is explicit but astronomically large, and the constants are those of the
formalization (`K = 256`; scalar calibration in `Probability/Calibration.lean`). The estimates
composed in `TimeTheorem.stabilizationTimeClaim_of_estimates` are all proved: Phases 0–2
(`2n⁻²`), the Phase-3 clock started at the first Phase-3 seed, since Phase 3 is entered
asynchronously (`8n⁻⁵`), Phase-3 averaging (`3n⁻²`), the late phases (Lemmas 10–14 of the paper,
`100n⁻²` on the small-gap branch), the strong-gap and tie continuations, and the recovery bound
for the expectation.

Proved (r2026.11.7): Theorem 3.1 as **one theorem about one protocol**,
`TheoremThreeOne.exact_majority_theorem_three_one`: for every `n ≥ 5·2^(2^23)` the compact
protocol `NonuniformMajorityCompact (⌈log₂ n⌉) 256` has at most `23 136 960 (⌈log₂ n⌉ + 1)`
states, stably computes majority on valid inputs of size `n`, and its own stabilization time
satisfies both bounds above. The compact transition runs directly on the scheduled labels; the
run is the encoding of the flat run on every log, and its stabilization time is at most `τ_D`.

Paper errata found along the way (two printed statements false without affecting Theorem 3.1,
proof gaps, and slips): [`docs/doty/ERRATA.pdf`](docs/doty/ERRATA.pdf), summarized in
`paper/ERRATA.md`.

### 6.5 Kurtz 1971 and 1978: central limit theorem and strong approximation
**Status: CLT (finite-dimensional distributions) PROVED (r2026.11.4); strong approximation (Kurtz
1978 Lemma 3.1, Theorems 3.3(a) and 4.4) PROVED (r2026.11.6); process-level CLT OPEN.** Papers:
Kurtz, J. Appl. Prob. 8 (1971) 344–356 (CLT: `√N (X_N − x)` converges to a Gaussian diffusion);
Kurtz, Stoch. Proc. Appl. 6 (1978) 223–240 (strong approximation).

Proved: the law of large numbers on `[0, T]` (Kurtz 1970, Thm 3.1) for canonical
density-dependent CTMCs, with the paper's initial condition (initial densities converging in
probability), `Kurtz.kurtz_finite_horizon` (`Ripple/Kurtz/FiniteHorizon.lean`); with an
explicit exponential tail, uniform on `[0, T]`, `Kurtz.kurtz_finite_horizon_exp_tail`
(`Ripple/Kurtz/ExponentialTail.lean`); and the **CLT for finite-dimensional distributions**,
`Kurtz.kurtz_finite_dimensional_clt` (`Ripple/Kurtz/FluctuationCLT.lean`): under the model
hypotheses and `√N (X_N(0) − x(0)) → v₀`, `(√N (X_N(t_j) − x(t_j)))_j` converges in law to the
Gaussian with the linearized mean and covariance. Paper proofs: `docs/audit/FIX-KURTZ2-FINAL.md`.

Proved (r2026.11.6, `Ripple/Kurtz/StrongApprox/`):
- **Lemma 3.1** (`KurtzLemmaThreeOne.kurtz_lemma_three_one`): a Brownian motion `W` and a unit
  Poisson process `Y` on one space with `K = sup_{t≥0} |Y(t) − t − W(t)|/(log t ∨ 2)` finite a.s.
  and `E exp(λK) < ∞` for an explicit `λ > 0` (dyadic KMT coupling from Binomial–normal and
  Poisson–normal quantile couplings, Serov–Zubkov intersection inequalities).
- **Theorem 3.3(a)** (`KurtzTheoremThreeThree.kurtz_theorem_three_three_a`,
  `…_identicalLaw` for the printed form): with independent Lemma 3.1 pairs per channel, the same
  for every `N`, continuous solutions `Z_N` of (1.6) exist, and one measurable `β^T` with an
  exponential moment gives `‖X_N(t) − Z_N(t)‖ ≤ β^T log N / N` for all `N ≥ 2`, `t ≤ T` a.s.
  Hypotheses (3.1), (3.2), (3.19), measurable `f^N`, finitely many channels; arbitrary random
  initial states.
- **Theorem 4.4** (`kurtz_theorem_four_four`) from the Section 4 hypotheses only ((3.1), (3.2), the
  summed square-root condition, bounded first and second coordinate partials of the drift, finitely
  many channels): one coupling space with the chains (1.3), the fluid limit, strong solutions of
  (1.7), one centered Gaussian `V` solving its linear equation, and `γ_N^T` with a uniform
  exponential moment such that `‖√N (X_N(t) − X(t)) − V(t)‖ ≤ γ_N^T log N / √N` for all `N ≥ 2`,
  `t ≤ T` a.s.; the covariance of `V` in `kurtz_theorem_four_four_covariance`; non-vacuity in
  `kurtz_theorem_four_four_paper_witness` (a state-dependent rate).

Remarks on the printed proof of Theorem 4.4 (paper arguments, not formalized): the compensator of
the exponential martingale in (4.4) is `λ²t/2`; and (4.8) cannot hold for every `λ` (a model with
jumps `±1` and rates `(2 + tanh x)²/2` violates it for every `λ ≥ 1/(2T)`), while the proof needs it
for some `λ > 0` only.

Open:
- **Process-level CLT.** Convergence in the Skorokhod space `D[0, T]` is not formalized.
- **`DensityProcessFamily`** (`Ripple/Kurtz/Defs.lean`) has no constructor; theorems taking
  it (`kurtz_convergence_for_density_process_family`) are conditional. A constructor from the
  canonical chains would follow from the proof of `kurtz_finite_horizon`.

### 6.6 Ramanujan 1914 and Chudnovsky 1989: series for 1/π
**Status: PROVED (both).**

Proved (r2026.11.2): `Chudnovsky1989.chudnovsky_one_over_pi`, the series identity
`640320^{3/2}/(12π) = Σ (−1)^k (6k)!/((3k)!(k!)³) (13591409 + 545140134 k)/640320^{3k}` with no
premise. Route (`docs/audit/CHUD-PAPER.md`): Milla's main theorem (`Milla.hauptformel`, ported
from Lean Pool, Apache-2.0) at `τ₁₆₃ = (1+√−163)/2`, with `j(τ₁₆₃) = −640320³`
(`KleinJCM163Statement_proof`) and `s₂(τ₁₆₃) = 77265280/90856689` (`Modular.s2_heegnerTau163`,
from the third-order expansion of `Φ₄₁(j(z), j(1−41/z)) ≡ 0` at the node `(j₀, j₀)`).

Proved (r2026.11.3): `Ramanujan1914.ramanujan_one_over_pi`,
`1/π = (2√2/9801) Σ (4k)!/(k!)⁴ (1103 + 26390k)/396^{4k}` with no premise. Route: the
`Γ₀(2)+` Hauptmodul `T = P/Q` satisfies the degree-29 modular equation `Ψ₂₉(T(29τ), T(τ)) = 0`
(Sturm certificate on `Γ₀(58)`); at the fixed point `τ₅₈ = i√58/2` of `τ ↦ −29/(2τ)`,
`T(τ₅₈) = 256·99⁴ − 104`, i.e. `x₂(τ₅₈) = 1/99⁴` (`Modular.hauptT58_tau58`); the second-order
expansion of `Ψ₂₉` at the node gives the CM relation `c₅₈ = 1103/26390`
(`Modular.ramanujan58_cm_relation`); the level-2 Kummer identity `Z = ₂F₁(1/8,3/8;1;x₂)²` near
`τ₅₈` (`Modular.Z_sq_eq_gauss`) turns it into the premise of
`ramanujan_one_over_pi_of_cm58` (`Modular.ramanujanCM58_evaluation`). The former
`RamanujanLambda58Statement` (`thetaLambda (i√58/2) = 1/99²`) was false and was deleted in r2026.11.2.

---

*Status as of release r2026.11.8.*
*Papers: [RTCRN1] Nat.Comput.2018, [RTCRN2] DNA25, [LPP] DNA28, [BAC] DNA32.*
