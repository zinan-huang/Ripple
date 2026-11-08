# Open Problems in CRN Computable Numbers
## Formalized using the Ripple Framework

### Status Legend
- **PROVED**: Fully verified in Lean (0 sorry, clean axiom trace)
- **STATED**: Statement formalized, proof placeholder / vacuous
- **PARTIAL**: Some components proved
- **OPEN**: Not yet formalized

*Global state (release r2026.11):* no `sorry`, no `axiom` declarations and
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
**Status: CONDITIONAL** (`closure_exponentiation_via_exp_log` in
`Ripple/Core/CRNPipeline.lean`, conditional on `h_exp` and `h_log`)

The reduction `α^β = exp(β · log α)` and the multiplication closure (`crn_computable_mul`, a
certified product tracker) are proved. Open: closure of `IsCRNComputable` under `exp` and under
`log` on positive reals, the content of [BAC] Thm 6.1. The duplicate `closure_exponentiation`
was deleted.

### 2.3 CRN Readout ([BAC] §7)
**Status: PROVED (structural form)** (`crn_readout_preserves_complexity` in
`Ripple/Core/CRNPipeline.lean`): a zero-initial certified computation of `α ∈ [0, 1]` gives a
certified computation of `α` with a `PolyCRNDecomposition`. The sharpened modulus bound of
[BAC] Thm 7.3 (low-pass filter `δ̇ + α·δ = α·ε(t)`, two-regime convolution bound) is not stated.

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
**Status: PARTIAL.** `apery_fermi_is_crn_computable` (`Ripple/Number/AperyFermi.lean`): an
explicit bounded five-variable rational polynomial system whose output converges to ζ(3) (the
Fermi–Dirac integral). It is stated for the semantic `PIVP` record, not yet as
`IsCRNComputable`; real-time computability is open.

`Number.apery_real_time_from_adaptation` (`Ripple/Number/AperyBounded.lean`) states real-time
computability of ζ(3) for the faithful predicate, conditional on `h_invariant`, `h_z_init` and
`hthree` (not produced).

The Apéry constant. Research directions from `experiments/FINDINGS.md`:
- ODE: `x²(4+x)F''' + x(10+3x)F'' + (2+x)F' = 1`
- Generates ζ(3) via Apéry's generating function
- Obstacle: singular point at `x = 0` needs regularization for PIVP form
- Deeper obstacle (2026-04 finding): MUM singularity is a *universal*
  structural barrier for the Apéry-style generating function, not Apéry-specific
- Open: first-floor (real-time) vs second-floor characterization

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

*Status as of release r2026.11.*
*Papers: [RTCRN1] Nat.Comput.2018, [RTCRN2] DNA25, [LPP] DNA28, [BAC] DNA32.*
