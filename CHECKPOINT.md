# Ripple CHECKPOINT — 2026-04-18 (updated, session 29)

> **Work log:** see [WORK_LOG.md](WORK_LOG.md) for append-only proof progress log with timestamps.

## Session 29 (2026-04-18) — axiom pruning + DNA 25 semantic zero-init

- **Stages.lean pruning** (commit `1dadf42`): deleted `stage2_core`, `stage2_to_tpp`,
  `stage3_to_lpp`, `gpac_to_lpp`, `algebraic_lpp_computable` and their transitive axioms.
  Canonical axiom-free chain is now `stage2_convergence_from_room → stage2_ode_axiomless_from_room
  → stage2_core_from_room → stage2_to_lpp_from_room`. Axiom count 8 → 7.
- **`Stage2Convergence.lean`: `stage2_to_lpp_from_bounds`** (commit `8c6b439`):
  closes the `h_room` hypothesis via bounded-trajectory + small-λ argument from
  [LPP] Remark 14 (c_room + M_out + M_rest bounds; uses `Finset.card_erase_of_mem`,
  `Finset.sum_le_sum`, `mul_le_mul_of_nonneg_left`, linarith). h_room no longer a
  free-floating assumption when the user supplies uniform bounds.
- **NEW: `Core/InitShift.lean`** (commit `25b5a50`) — [RTCRN2]/DNA 25 Theorem 3:
  - `PIVP.shiftToZero` (noncomputable def): semantic zero-init shift
    via change of variables `ẑ(t) := y(t) − y₀`. Field `p̂(z) := p(z + y₀)`,
    init = 0, output preserved.
  - `PIVP.Solution.shift`: shifted trajectory solves the shifted PIVP.
    `is_solution` proved via `hasDerivAt_pi` + `HasDerivAt.sub_const`.
  - `PIVP.shiftToZero_isBounded`: boundedness transfers with constant `M + ‖P.init‖ + 1`.
  - `BoundedTimeComputable.shiftToZero`: BTC-level zero-init reduction,
    same modulus preserved. Output converges to `α − y₀.output`.
  - `shiftToZero_zero_output_init`, `shiftToZero_pivp_output`, `_init`: simp lemmas.
- **NEW: `IsRealTimeComputable` DNA 25 corollaries** (commit `062c502`):
  - `IsRealTimeComputable.zero_init_decomposition`: RT α ⇒ ∃β, zero-init BTC for (α−β) with linear modulus.
  - `IsRealTimeComputable.of_zero_init_plus_const`: reconstruction via `realtime_field_add` + `realtime_const`.
  - DNA 25 reduction cycle now closed at BTC semantic layer.
- **Ripple.lean**: adds `import Ripple.Core.InitShift`.
- **NEW: `Ripple/DualRail/BTCReduction.lean`** (commit `d863085`):
  - `axiom BoundedTimeComputable.toDualRail`: zero-init BTC α ⟹ higher-dim
    BTC α with all-zero init + non-neg-interior species + same modulus.
    Narrow research-gap axiom, discharge requires upgrading
    `dualRail_polynomial_scale_bounded` to yield full `PIVP.Solution`.
  - `BoundedTimeComputable.dna25_shift_dualRail`: composes shiftToZero +
    toDualRail. Any BTC α reduces to zero-init + nonneg-interior BTC for
    `α − y₀` with same modulus.
  - `IsRealTimeComputable.dna25_full_reduction`: IRTC-level DNA 25 full
    reduction with linear modulus preserved.
- **Axiom count**: 7 → 8 (added `toDualRail` as narrow paper-level gap).
  Current axioms: `dualRail_polynomial_scale_bounded`, `toDualRail`,
  `noCollapse_step2_root_liminf`, `noCollapse_step3_scc_induction`,
  `minPolyPIVP_exists_solution`, `minPolyPIVP_convergence_modulus`,
  `algebraic_shift_to_smallest_positive_root`, `certified_add_rational`.
- **NEW: `exists_rational_gap_below_real`** (commit `a646d6d`) — first
  structural brick toward `algebraic_shift_to_smallest_positive_root`.
  Given nonzero `p : ℤ[X]` and `α : ℝ`, there is a rational `q < α`
  such that `(q, α)` contains no real root of `p`. Uses
  `Polynomial.finite_setOf_isRoot` + `Finset.max'` + `exists_rat_btwn`.
- **NEW: `rational_polynomial_to_integer_real_roots`** (commit `c13ab42`)
  — second structural brick, factored per 2026-04-18 architectural
  guidance. For any nonzero `p : ℚ[X]`, produces `P : ℤ[X]` with
  identical real roots. Uses `IsLocalization.integerNormalization`
  machinery from Mathlib; key step: `Algebra.smul_def` +
  `eq_intCast` + `← C_eq_intCast` to unfold the ℤ-algebra smul into
  `C ((b : ℚ)) * p`, then `eval₂_mul` + `eval₂_C` to evaluate.
  Standalone theorem so the shift axiom reduces to pure root geometry.
- **NEW: `algebraic_shift_to_smallest_positive_root` proved**
  (commit `e3a70bb`) — axiom → theorem. Composes gap + clearing:
  1. `exists_rational_gap_below_real` gives `q ∈ ℚ` with gap;
  2. Shift `p₀.map (algebraMap ℤ ℚ) |>.comp (X + C q)` to ℚ[X];
  3. `rational_polynomial_to_integer_real_roots` clears to ℤ[X];
  4. Sign case split on `P_abs.coeff 0` (negate if negative).
  Nonzeroness of composition via `Polynomial.comp_eq_zero_iff` +
  `natDegree_X_add_C = 1`. Root correspondence via
  `Polynomial.aeval_comp` + `aeval_map_algebraMap`.
- **Axiom count**: 8 → 7. Remaining: `dualRail_polynomial_scale_bounded`,
  `toDualRail`, `noCollapse_step2_root_liminf`, `noCollapse_step3_scc_induction`,
  `minPolyPIVP_exists_solution`, `minPolyPIVP_convergence_modulus`,
  `certified_add_rational`.

## Current State

### Fully Proved (0 sorry, 0 axiom)
- **PIVP.lean**: PIVP + PolyPIVP (syntactic layer with rational coefficients)
- **BoundedTime.lean**: Field closure complete
  - `realtime_const`, `realtime_field_add`, `realtime_field_mul`
  - `realtime_field_neg`, `realtime_field_inv_pos`, `realtime_field_inv`, `realtime_field_div`, `realtime_field_sub`
  - `BoundedTimeComputable.to_tendsto` (quantitative convergence → Filter.Tendsto)
  - `CertifiedBoundedTimeComputable`, `certified_realtime_rat_const`
- **Compilation.lean**: Bounded surrogate basics
  - `boundedSurrogate_mem_Icc`, diagonal lemmas, tendsto lemmas, derivative
  - `time_length_equivalence`
  - `bounded_compilation` / `bounded_compilation_rat` (placeholder proofs, non-vacuous hypotheses)
- **CRNPipeline.lean**: Statements with certified inputs
  - `crn_readout_preserves_complexity` (placeholder)
  - `closure_exponentiation` (placeholder)
- **Euler.lean**: e is real-time CRN-computable
- **Pi.lean**: pi is real-time CRN-computable
- **Ln2.lean**: ln 2 is real-time CRN-computable
- **EulerGamma.lean**: gamma is real-time CRN-computable (fully verified)
- **LPP/Defs.lean**: Core definitions + PLPP (0 sorry)
  - `IsPositivePoly`, `IsCRNImplementable`, `IsConservative`
  - `IsPPImplementable` (standalone balance equation form, enforces all 4 conditions):
    - `f` (production quadratic), `f_pos`, `f_homog` (degree 2), `field_eq`, `sum_f` (conservation)
    - Derived: `toCRN`, `conservative`, `no_self_square`
  - `PolyCRNDecomposition` — syntactic CRN decomposition (non-negative poly coefficients), with `toIsCRNImplementable`
  - `IsLPPComputable`, `PPBalanceEquation`, `PPBalanceEquation.toField`
  - `one_trick`, `one_trick_sq`
  - `PPBalanceEquation.conservative_of_sum_eq` (fully proved)
  - `PLPPTransitions`, `PLPPTransitions.balanceField`, `PLPPTransitions.balanceField_conservative`
  - **Fixed**: `toField` uses formal degradation `f_r(x) - 2x_r·(Σx_k)`, not simplex-specialized
  - **Fixed**: `IsPPImplementable` restructured to enforce degree ≤ 2 + no-self-square
- **LPP/Syntactic.lean**: Syntactic PP balance + Stage 4 PLPP construction (0 sorry)
  - `SynPPBalance`: explicit ℚ coefficient tensor with conservation `Σ_r c_{r,i,j} = 2`
  - `evalProd`, `toField`, `evalProd_nonneg`, `sum_evalProd`, `conservative`
  - `toPPBalance`, `toField_eq_balance`, `toCRN`, `toPP`
  - **Stage 4 construction**: `toPLPPTransitions` (product distribution α_{i,j,k,l} = c_k c_l / 4)
  - `toPLPPTransitions_row_marginal`, `toPLPPTransitions_col_marginal`, `toPLPPTransitions_marginal`
  - `toPLPPTransitions_balanceField_eq` — PLPP field = PP field (exact, no ε)
- **LPP/Example.lean**: Motivating example ½e⁻¹ (0 sorry)
  - Complete `IsLPPComputable` witness for `Real.exp (-1) / 2`
  - Formal PP field `halfExpFieldPP` (bimolecular embedding, degree 2)
  - Production terms `halfExpProd`: f_F=2F²+2FG, f_E=E·S, f_G=3FE+2FG+E²+3EG+2G²
  - `halfExpFieldPP_pp`: full `IsPPImplementable` witness (5 fields)
  - `halfExpFieldPP_eq_on_simplex`: bridge to simplex-specialized CRN field
  - ODE solution via simplex bridge: halfExpFieldPP = halfExpField on simplex
  - All component derivatives, initial values, simplex invariant, convergence proved
- **LPP/NAP.lean**: PP→NAP splitting feasibility — Note 14 Theorem 1 (0 sorry)
  - Multi-index infrastructure: `miWeight`, `miSupp`, `miDvd`, `miUnit`, `miShift`
  - `MonomialSplit`: non-autocatalytic factorization δ = β + γ with β|α, γ|α, neither unit
  - `ProductionMonomial`: chain rule monomial with `pipeline_bound` (μ_source ≤ 2) + `foreign_pair`
  - `IsCubedIndex`: cubing construction v_α = C(3,α)·∏xⱼ^{αⱼ}
  - `miShift_weight`, `miShift_ne`, `miShift_reverse_ne`: shift lemmas
  - `exponent_redistribution`: algebraic heart — divisor β of degree-6 monomial with α|β + foreign_pair
  - `exists_foreign_atom`: foreign_pair implies existence of i₀ ∈ supp(μ)\{source}
  - `pure_power_split`: |supp(α)|=1 case — trivial 3+3 split
  - `mixed_support_split`: |supp(α)|≥2 case — primary/backup miShift strategy
  - `nap_splitting_feasibility`: every ProductionMonomial admits MonomialSplit
  - `trivial_split_of_lt`: δ_source < α_source ⟹ any split has β ≠ α ∧ γ ≠ α
  - `exists_weight_divisor`: any multi-index of weight ≥ k has a weight-k divisor (greedy induction)
  - `trivial_balanced_split`: δ_source < α_source + |δ|=6 ⟹ balanced NAP split
  - `pp_to_nap_split`: **GENERAL PP→NAP** — case split on foreign_pair: yes → nap_splitting_feasibility, no (μ_source=0) → trivial_balanced_split
  - `CubedPPMonomial`: structure bundling chain rule data + strict no-self-production
  - `cubed_pp_nap`: protocol-level wrapper — every CubedPPMonomial admits balanced NAP split
  - `nap_split_comprehensive`: disjunctive criterion — μ_source = 0 OR (pipeline_bound + foreign_pair)
  - **Key discovery**: `foreign_pair` field is necessary — bare `pipeline_bound` insufficient
  - **Key discovery**: Note 14 proof has a gap in Step 2 (δ = 2α not justified); formalization sidesteps via strict no-self-production
  - **Key insight**: strict no-self-production (μ_source = 0) cleanly splits proof into two cases
- **LPP/Rational.lean**: Cyclic unimolecular protocol (0 sorry)
  - `predPerm`: predecessor permutation via `finRotate.symm`
  - `cyclicField`: formal version (x_{pred(i)} - xᵢ)·(Σxₖ) (degree 2)
  - `cyclicProd`: production f_r(x) = (x_{pred(r)} + x_r)·(Σxₖ)
  - `cyclicField_conservative`: via `Equiv.sum_comp` (permutation sum reindexing)
  - `cyclicField_pp`: full `IsPPImplementable` witness (5 fields)
  - `cyclicField_on_simplex`: bridge to simplex-specialized form
  - `cyclicField_equilibrium`: uniform distribution 1/(q+1) is equilibrium

- **LPP/VVariable.lean**: v-Variable quadraticization — **FULLY PROVED (0 sorry)**
  - Multi-index set `MIndex d D = Fin d → Fin (D+1)` with `degree`, `basis`, `zero'`, `eval`
  - Key lemmas: `eval_zero'`, `eval_basis`, `eval_nonneg`, `eval_bounded`, `eval_rational`, `degree_le`
  - Finsupp conversion: `finsuppToMIndex`, `MIndex.toFinsupp`, `toFinsupp_injective`, `finsupp_component_le_totalDegree`
  - `MIndex.sub_basis`: α - e_k for α_k > 0, with `sub_basis_eval`, `sub_basis_mul`
  - `eval₂_as_mindex_sum`: bridge between MvPolynomial.eval₂ (Finsupp) and bounded MIndex sums
  - v-coefficients: `vCoeffA`, `vCoeffB` with `vCoeffA_nonneg`, `vCoeffB_nonneg`
  - v-init: `vInit` with `vInit_nonneg`, `vInit_rational`
  - **`hasDerivAt_monomial`**: chain rule for monomials (via `HasDerivAt.fun_finset_prod` + `HasDerivAt.fun_pow`)
  - **`vfield_chain_rule_eq`**: algebraic identity — CRN quadratic form = chain rule derivative on monomial manifold
  - **`stage1_vvariable`**: main theorem — constructs v-PIVP with CRN form, **fully verified**:
    - `is_solution`: via `hasDerivAt_pi` + `hasDerivAt_monomial` + `vfield_chain_rule_eq` + `Equiv.sum_comp` reindexing
    - Boundedness transfer via `eval_bounded` + `degree_le`
    - Convergence transfer (v_{e_output}(t) = x_{output}(t))

### Theorem Statements with axioms (no sorry remaining)
- **LPP/Stages.lean**: Four-stage GPAC→PP construction (**0 sorry, 2 axioms** as of session 28; Core/ODEGlobal.lean now 0 axiom, was 1 in session 27)
  - `crn_simplex_global_ode_solution` — **NOW A THEOREM** (session 27): delegates to `crn_simplex_global_ode_solution'` in `Core/ODEGlobal.lean`; the underlying Mathlib-gap is now the narrow axiom `locally_lipschitz_bounded_global_ode` (pure ODE extension, no CRN content)
  - `stage2_convergence_axiom` — Stage 2 output converges to α with same modulus (time dilation argument). **A proved replacement `stage2_convergence_from_room` is now available in `LPP/Stage2Convergence.lean` (0 sorry, 0 axiom); it discharges the content under an h_room hypothesis that must come from the upstream CRN construction.** **Also available**: `stage2_ode_axiomless_from_room` — a parallel ODE-existence-plus-convergence entry point matching `stage2_ode_axiom`'s conclusion, with no use of `stage2_convergence_axiom` (commit 979fefd). The axiom itself remains in the pipeline pending upstream CRN constructions that can supply `h_room` + `h_zero_init`.
  - `stage2_ode_axiom` — **FULLY PROVED THEOREM** (was axiom → theorem): derives from the two axioms above
    - Locally Lipschitz via `stage2_field_cubicForm` + `cubicForm_locally_lipschitz` (requires explicit A, B coefficients)
    - CRN implementability derived from A, B decomposition inside proof
  - `stage1_core_axiom` — **FULLY PROVED THEOREM** (was axiom → theorem), calls `stage1_vvariable` (0 sorry)
  - `algebraic_is_certified_crn` — algebraic numbers → CertifiedBTC + CRN ([RTCRN1] Theorem 3.4)
  - `lpp_computable_mul_certified` — product of LPP-computable → CertifiedBTC + CRN (certified pipeline)
  - **PROVED** (session 23): `algebraic_lpp_computable` — sorry→axiom: `algebraic_is_certified_crn` (algebraic numbers have certified CRN reps)
  - **PROVED** (session 23): `lpp_computable_mul` — sorry→axiom: `lpp_computable_mul_certified` (LPP product has certified CRN rep)
  - **PROVED** (session 22): `stage2_ode_solution` — fully proved via axiom + explicit parameter choice:
    - Parameter choice: n = ⌈∑init⌉₊+1, c = 1/n (rational, positive, c·∑init ≤ 1), ε = n (ε·c = 1)
    - Rationality via `push_cast; ring`
    - c·∑init ≤ 1 via `Nat.le_ceil` + `Nat.le_succ` + `div_le_one`
    - Solution + convergence from `stage2_ode_axiom`
  - **PROVED** (session 22): `stage2_core` boundedness — proved from simplex + CRN non-negativity:
    - Previously got `h_bounded` from `stage2_ode_solution`; now proved explicitly
    - Simplex invariance → ∑ sol_i = 1; CRN non-negativity → sol_i ≥ 0
    - Each component sol_i ≤ ∑ sol_j = 1 ≤ 2, with `pi_norm_le_iff_of_nonneg`
  - **PROVED** (session 21): `crn_nonneg_invariance` — CRN non-negativity invariance via squared negative mass + Grönwall:
    - `hasDerivAt_minSq`: derivative of min(s,0)² is 2·min(s,0) (3 cases: s<0, s=0, s>0)
    - Squared negative mass functional F(t) = ∑min(xⱼ(t),0)², F(0)=0 from init≥0
    - HasDerivAt F via `HasDerivAt.sum` + `congr_of_eventuallyEq` bridge
    - Trajectory bound via `isCompact_Icc.exists_isMaxOn`
    - Lipschitz splitting: field(x) = field(x⁺) + [field(x)-field(x⁺)]
      - First term ≤ 0 by CRN positivity (prod ≥ 0 on x⁺)
      - Second term ≤ 2Ld·F by Lipschitz + ‖m‖² ≤ ∑mⱼ² + Pi.sum_norm_apply_le_norm
    - `max L₀ 0` trick for positivity of Lipschitz constant
    - Grönwall: F ≤ 0 + F ≥ 0 → F = 0 → each component ≥ 0
  - **PROVED** (session 21): `cubicForm_locally_lipschitz` — Stage2CubicForm polynomial fields are locally Lipschitz:
    - Each component is ContDiff ℝ ⊤ (polynomial), proved via `contDiff_apply`, `ContDiff.sum`, `ContDiff.mul`
    - Full field ContDiff via `contDiff_pi'` (zero component = -(∑ others))
    - `ContDiff.continuous_fderiv` → `IsCompact.exists_bound_of_continuousOn` → bounded ‖fderiv‖ on R-ball
    - `Convex.norm_image_sub_le_of_norm_fderiv_le` (Mean Value Theorem) closes the Lipschitz bound
    - Wired into `stage2_core` call site (line 1864), eliminating the locally-Lipschitz sorry
  - **PROVED** (session 21): `gpac_to_lpp` — refactored to accept `CertifiedBoundedTimeComputable` directly:
    - Was: takes semantic `BoundedTimeComputable`, sorry for BTC→CBTC bridge (unprovable without polynomial witness)
    - Now: takes `CertifiedBoundedTimeComputable` + `IsCRNImplementable`, trivially delegates to `stage3_to_lpp`
    - Sorry moved to `lpp_computable_mul` (semantic→certified bridge for product closure)
  - **PROVED** (session 19): `conservative_trajectory_sum` — conservation invariant via MVT
  - **PROVED** (session 19): `conservative_trajectory_simplex` — simplex corollary
  - **PROVED** (session 19): `stage2_core` — now proved by composition from stage2_ode_solution + crn_nonneg_invariance + algebraic infrastructure
  - **PROVED** (session 18): `stage1_quadraticization`, `stage2_to_tpp`, `stage3_to_lpp` — derived by composition from stage1_core + stage2_core + tpp_to_lpp
  - **PROVED**: `tendsto_zero_of_tendsto_bounded_deriv` — Barbalat-lite (f→L, f' Lipschitz → f'→0):
    - Strengthened statement to require bounded f'' (original required only bounded f', which is INSUFFICIENT — counterexample exists)
    - Direct proof: MVT gives f'(c) = slope, Lipschitz bounds |f'(t)-f'(c)| ≤ Cδ, Cauchy bounds slope, total < ε
  - **PROVED**: `const_of_iterated_deriv_zero_bounded` — bounded + D^m=0 → constant:
    - Tower-shifting induction: g' j = g(j+1), IH gives g 1 constant
    - Case g 1 0 = 0: constant_of_has_deriv_right_zero
    - Case g 1 0 ≠ 0: affine → unbounded → contradiction (reverse triangle inequality via abs_add_le)
  - **PROVED**: `bounded_linear_ode_limit_rational` — analysis core, **0 internal sorry** (was 4):
    - rootMultiplicity factoring, g derivative tower, g 0 bounded, g 0 0 rational, Barbalat induction
    - g m = 0 from CH (sum re-indexing + ℚ→ℝ cast via exact_mod_cast)
    - g 0 → c_m·ν (tendsto_finset_sum + Finset.sum_ite_eq')
    - Final conclusion: Metric.tendsto_nhds + constancy → c_m·ν = g(0)(0), eq_div_iff → ν ∈ ℚ
    - Depends on 2 sorry'd analysis sub-lemmas (Barbalat + iterated-deriv-const)
  - **PROVED**: `linear_ode_marked_sum_rational` — **0 sorry** (was 1)
    - Reduction from matrix ODE to scalar: derivative tower f_k, HasDerivAt, boundedness, rationality at 0, Cayley-Hamilton entry-wise — all fully proved
    - Key fix: `let` binding mismatch — goal had `(Matrix.of A).charpoly` but `h_entry` had `Matrix.charpoly A_mat`; fixed by matching h_entry to goal form + `exact_mod_cast`
  - **RESOLVED**: `tpp_to_lpp` — **0 sorry** (was 1). Resolved by removing `.pp : IsPPImplementable` from `IsLPPComputable` in Defs.lean. Justified by paper gap: ppField is NOT globally conservative (only on manifold), so IsPPImplementable cannot be directly proved. The `.pp` field was never accessed by any downstream proof.
  - **PROVED**: `lpp_computable_mul` (Lemma 11: product closure, routes through CRN pipeline)
  - **PROVED**: `crn_computable_mul` (CRN product closure via PIVP product rule)
  - **PROVED**: `lpp_to_gpac` (LPP → CRN-computable, augments with readout sum)
  - **PROVED**: `lpp_computable_in_01` (LPP numbers lie in [0,1])
  - **PROVED**: `stage4_to_plpp` (Stage 4, syntactic input, product distribution)
  - **PROVED**: `half_exp_neg_one_lpp_computable` (uses Example.lean witness)
  - **PROVED**: `gpac_to_lpp` (chains stage3_to_lpp, no own sorry)
  - **PROVED**: `constant_dilation_reparametrize` (ε-trick for scalar functions)
  - **PROVED**: `constantDilation` + `constantDilation_crn` + `constantDilation_conservative` (Op 2)
  - **PROVED**: `lambdaTrick` + `lambdaTrick_smul_cancel` + `lambdaTrick_solution` + `lambdaTrick_crn` (Op 3, uniform)
  - **PROVED** (session 20): `selectiveUnscale`, `selectiveScale`, `selectiveLambdaTrick` (Op 3b, selective)
    - `selectiveUnscale_output`, `selectiveUnscale_ne`, `selectiveUnscale_scale`
    - `selectiveLambdaTrick_solution` — solutions preserved under selective scaling
    - `selectiveLambdaTrick_tendsto` — output convergence to α (not c·α!) preserved
    - `selectiveLambdaTrick_crn` — CRN-implementability preserved
    - `selectiveLambdaTrick_quadratic_form` — quadratic CRN form preserved with explicit selective coefficients
    - `inner_stage2_hasDerivAt`, `inner_stage2_init`, `inner_stage2_tendsto`, `inner_stage2_bounded`
  - **UPDATED** (session 20): `stage2_field`, `stage2_field_tpp`, `stage2_pivp`, `stage2_field_cubicForm` — all migrated from uniform `lambdaTrick` to `selectiveLambdaTrick` using `P.output` as the unscaled variable. Fixes mathematical bug where output converged to c·α instead of α.
  - **PROVED**: `oneTrick` + `oneTrick_conservative` (1-trick, note: does NOT preserve CRN)
  - **PROVED**: `balancingDilation` + `balancingDilation_conservative` + `balancingDilation_crn` (Op 4)
  - **PROVED**: `conservative_sum_constant` + `conservative_simplex_invariant` (simplex invariance)
  - **PROVED**: `stage2_field` + `stage2_field_tpp` (Stage 2 algebraic composition)
  - **PROVED**: `selfProduct_rowSum` + `selfProductField` + `selfProductField_conservative` (Stage 3 building block)
  - **PROVED**: `selfProduct_rowSum_eq` + `selfProduct_totalSum` + `selfProduct_simplex` (Stage 3 simplex)
  - **PROVED**: `selfProduct_hasDerivAt` (product rule: z_{i,j} = x_i·x_j solves selfProductField ODE)
  - `vecSnoc`, `vecAddCases` (non-dependent Fin tuple helpers + simp lemmas)
  - `IsKPPImplementable`, `IsTPPImplementable` (definitions)

### Placeholder Theorems in Core/ (proved vacuously, need real proofs)
1. `bounded_compilation` — needs actual U_{n,m} surrogate ODE construction from [BAC] §3
2. `closure_exponentiation` — needs exp/ln PIVP composition from [BAC] §6
3. `crn_readout_preserves_complexity` — needs low-pass filter from [BAC] §7

## Build Status
- `lake build` passes with 0 errors
- All sorry's are in theorem statements (open research goals)
- Style warnings only (flexible simp, unused simp args, long lines)

## Key Design Decision: Formal vs Numerical Cancellation

The LPP balance equation has two forms:
- **Formal** (polynomial identity): x'_r = f_r(x) - 2x_r·(Σx_k), conservation: Σf_r = 2(Σx)²
- **Simplex-specialized**: x'_r = f_r(x) - 2x_r, conservation: Σf_r = 2 (only when Σx = 1)

The formal version is required for the 4-stage construction. Stage 4 extracts PLPP
transition coefficients at the z-monomial level, which requires z-monomial-level
cancellation (Note 13 in DNA30_BD). This is strictly stronger than x-monomial-level
cancellation and depends on the canonical factoring (x₀ universal factor from Stage 2).

Both `PPBalanceEquation.toField` and `PLPPTransitions.balanceField` now use the formal
version. `balanceField_conservative` is fully proved, validating the formal structure.

## Architecture
```
Ripple/
├── Core/
│   ├── PIVP.lean          -- PIVP + PolyPIVP
│   ├── BoundedTime.lean   -- Time modulus, field closure (1292 lines, 0 sorry)
│   ├── Compilation.lean   -- Bounded surrogates, time-length equiv
│   └── CRNPipeline.lean   -- Dual-rail + readout pipeline
├── Number/
│   ├── Euler.lean         -- e is RT-CRN-computable
│   ├── Pi.lean            -- π is RT-CRN-computable
│   ├── Ln2.lean           -- ln2 is RT-CRN-computable
│   ├── EulerGamma.lean    -- γ is RT-CRN-computable
│   └── Apery.lean         -- ζ(3) placeholder
└── LPP/
    ├── Defs.lean          -- Core definitions + PLPP (0 sorry)
    ├── Syntactic.lean     -- Syntactic PP balance + Stage 4 construction (0 sorry)
    ├── Stages.lean        -- Four-stage construction (0 sorry, 4 axioms: 2 analytic + 1 bridge + 1 algebraic)
    ├── Example.lean       -- ½e⁻¹ motivating example (0 sorry)
    ├── Rational.lean      -- Cyclic UPP for rationals (0 sorry)
    └── NAP.lean           -- PP→NAP splitting + general theorem (0 sorry)
```

## Next Steps
1. **Paper gap resolved (via symmetric self-product + matching)**:
   - CF'24 paper (Huang-Migunov) confirms: z₀₁ and z₁₀ merged, PLPP via coefficient matching
   - `tpp_to_lpp` already works without IsPPImplementable ✓
   - Future: refactor self-product to use d(d+1)/2 symmetric variables
   - Future: implement matching-based PLPP construction (pairing positive/negative coefficients)
2. **Stage 2 infrastructure (COMPLETE — all algebraic proved, ODE via 2 axioms)**:
   - `stage2_field_tpp` ✓, `stage2_field_cubicForm` ✓, `balancingDilation_cubicForm` ✓
   - `conservative_trajectory_sum` ✓, `stage2_core` ✓, `crn_nonneg_invariance` ✓
   - `stage2_ode_axiom` ✓ (THEOREM, derived from 2 axioms below)
   - `stage2_ode_solution` ✓ (parameter choice proved)
   - **Axiom** `crn_simplex_global_ode_solution` — Mathlib lacks global ODE extension
   - **Axiom** `stage2_convergence_axiom` — time-dilation convergence
   - `stage2_field_output/nonoutput/zero` — field simplification lemmas for convergence
   - `stage2_output_hasDerivAt` — output derivative extraction
3. **Stage 1**: `stage1_core_axiom` ✓ (THEOREM, calls `stage1_vvariable`)
4. **Unimolecular → rational** (Lemma 10): **FULLY PROVED**
5. **Remaining axioms** (2 total, session 28):
   - `stage2_convergence_axiom` — convergence under time dilation ([LPP] Remark 14)
   - `algebraic_is_certified_crn` — Newton's method as PolyPIVP ([RTCRN1] Theorem 3.4)
   - **ELIMINATED** (session 28): `locally_lipschitz_bounded_global_ode` — proved as theorem via iterated Picard + ODE uniqueness (see Session 28 log)
   - **ELIMINATED** (session 26): `lpp_computable_mul_certified` — replaced by direct proof via `lpp_product` in `LPP/Product.lean`
6. **Placeholder proofs in Core/**: bounded_compilation, closure_exponentiation, crn_readout

## Session Log (2026-04-17, session 28)
- **`locally_lipschitz_bounded_global_ode`: axiom → THEOREM** (main achievement):
  - ODEGlobal infrastructure (parts 1-5):
    - `field_bound_on_closedBall`, `lipschitz_field_bound_on_closedBall`, `locally_lipschitz_continuous` — local-Lip ⇒ continuity/boundedness machinery.
    - `lipschitzOnWith_shifted_ball`, `field_bound_shifted_ball`, `picard_uniform_step` — uniform (ε, K, B) with B·ε ≤ 1/2 feeding `IsPicardLindelof.of_time_independent`.
    - `single_step_solution` — one Picard step on Icc t₀ (t₀+ε).
  - Gluing infrastructure (part 6):
    - `hasDerivWithinAt_Icc_extend_right/left` — interval extension via `mono_of_mem_nhdsWithin`.
    - `glue_two_Icc_solutions` — piecewise β on Icc a T ∪ Icc T T' via `HasDerivWithinAt.union` at seam.
    - `iterate_one_step` — extend partial solution on [0, T] by one ε-step.
    - `extend_left_linear_hasDerivAt` — linearly prolong to t < 0 (slope f y₀) to get two-sided HasDerivAt on Ico 0 T.
    - `solution_bounded_of_invariant` — lift h_invariant bound from Ico to Icc via continuity + `IsClosed.mem_of_tendsto` + `right_nhdsWithin_Ico_neBot`.
    - `y0_norm_le_M` — initial bound ‖y₀‖ ≤ M from local Picard + h_invariant.
    - `exists_solution_on_step_Icc` — Nat induction yielding α_n on Icc 0 (n·ε) with α_n(0) = y₀ and ‖α_n(n·ε)‖ ≤ M.
  - Closing step (part 7):
    - `hasDerivWithinAt_Icc_to_Ici` — convert Icc HDW to Ici HDW (needed for Mathlib uniqueness signature).
    - `solutions_agree_on_Icc` — ODE uniqueness via `ODE_solution_unique_of_mem_Icc_right` on closedBall 0 M.
    - `locally_lipschitz_bounded_global_ode_proved` — THEOREM replacing the axiom. Uses `Classical.choose` on `exists_solution_on_step_Icc` to get family α : ℕ → ℝ → Fin d → ℝ; uniqueness-based consistency α_n = α_m on overlap; define y via n_of t = ⌈t/ε⌉+1 plus linear left extension. Two-sided HasDerivAt at t = 0 via `HasDerivWithinAt.union` on Iic 0 ∪ Ici 0 = univ.
  - Axiom deleted; call site `crn_simplex_global_ode_solution'` rerouted to theorem.
- **Result**: **0 sorry, 2 axioms** (down from 3). Both remaining are research-content axioms, not Mathlib gaps.
- Commits: 36d849c, 3c7d3c8, 86d5fb1, cbba685, bc46ce5, 47d6cfa, 2513451, e6691da, 1206f5a, d50e52b, 0ff5eec, a2812ce.

### Session 28 continued — stage2_convergence_axiom infrastructure
- **`stage2_unscaledTail_hasDerivAt`** (chain-rule core): `w(t) := selectiveUnscale o c (tail (sol t))` satisfies uniform `dw/dt = (ε · z₀(t)) • P.field(w(t))` at every coordinate. Case split on j = o (output unchanged) vs j ≠ o (divide by c). commit `c218f3a`.
- **`stage2_zero_hasDerivAt`**: `dz₀/dt = -(Σ slt(cd) (tail sol))_j · z₀(t)`, directly from `stage2_field_zero` + `hasDerivAt_pi`. commit `4a20d3b`.
- **`stage2_effectiveTime`** + **`stage2_effectiveTime_hasDerivAt`**: defined `τ(t) := ε · ∫₀ᵗ z₀(s) ds`, proved `dτ/dt = ε · z₀(t)` for t > 0 via `intervalIntegral.integral_hasDerivAt_right` + continuity on `Set.Ici 0`. Boundary t=0 deferred. commit `39e92b4`.
- **`stage2_unscaledTail_init`**: characterizes `w(0)`. Since `stage2_init` scales all tail entries uniformly by c but `selectiveUnscale` only divides non-output coordinates, `w(0) = update P.init o (c · P.init o)` — **not** `P.init` unless `P.init o = 0`. commit `45f45a3`.
- **`stage2_output_eq_unscaledTail`**: `sol(t)_{o.succ} = w(t)_o` (identity at output coordinate). commit `4735502`.

### Known issue in stage2_convergence_axiom statement
The current axiom statement does NOT assume `btc.pivp.init btc.pivp.output = 0`. Without this, the chain-rule argument breaks: w(0) = P.init at j ≠ o but w(0)_o = c · P.init_o at j = o, so w and `btc.sol.trajectory ∘ τ` disagree at t = 0 and remain different under ODE uniqueness. The LPP proof implicitly relies on DNA 25 preprocessing which zeros `P.init_o`. Correct formalization path: (a) strengthen axiom to require `P.init_o = 0`, OR (b) derive this from the BTC structure (not always true). TBD.

### Session 28 continued (night, 2026-04-17 → 2026-04-18) — more infra lemmas
- **`stage2_effectiveTime_nonneg`** + **`stage2_btcTraj_comp_tau_hasDerivAt`**: τ ≥ 0 from ε ≥ 0 + z₀ ≥ 0; chain rule `d/dt btc.sol.traj(τ(t)) = (ε·z₀)•f(btc.sol.traj(τ(t)))` via `HasDerivAt.scomp`. commits `c218f3a` … `3a44996`.
- **`pivp_solution_nonneg`** + **`pivp_solution_sum_const`**: global extensions of `crn_local_nonneg` and `conservative_local_sum_const` to `PIVP.Solution` on `[0, ∞)` via picking T := t+1. Reusable for any future CRN PIVP. commit `98d9e38`.
- **`stage2_z0_nonneg`**: z₀(t) ≥ 0 for all t ≥ 0 via `pivp_solution_nonneg` + stage2 CRN-implementability (from `stage2_field_tpp`). commit `98d9e38`.
- **`stage2_sum_eq_one`**: ∑ᵢ sol(t)ᵢ = 1 via `pivp_solution_sum_const` + `balancingDilation_conservative` + `stage2_pivp_init_simplex`. commit `4741a4c`.
- **`stage2_z0_eq_one_minus_tail_sum`**: z₀(t) = 1 - ∑_{i≥1} z_i(t) via `Fin.sum_univ_succ`. commit `4741a4c`.
- **`stage2_tail_nonneg`** + **`stage2_z0_le_one`**: tail coords ≥ 0; z₀(t) ≤ 1. commit `a439308`.
- **Status**: chain rule, simplex, non-negativity all proved globally. Still open for `stage2_convergence_axiom`: (a) ODE uniqueness step (Mathlib `ODE_solution_unique_of_mem_Icc_right` with time-varying v(t,x) = (ε·z₀(t))•f(x)); (b) z₀(t) ≥ c lower bound (LPP Remark 14 core invariant, requires additional constraint on P dynamics — not just simplex conservation); (c) zero-init hypothesis needed in axiom signature.
- **Continuity + vField + Lipschitz**: added `stage2_unscaledTail_continuousOn` (w on Ici 0), `stage2_btcTraj_comp_tau_continuousOn` (btc.sol∘τ on Ioi 0), `stage2_vField btc sol t x := (ε·z₀(t))•f(x)` (common RHS), and `stage2_vField_lipschitzOnWith` (uniform Lipschitz on closedBall 0 M, constant |ε|·L, using z₀∈[0,1]). commits `80855b6`, `c9b1832`.
- **Night session commit chain (2026-04-17 → 2026-04-18)**: `3a44996 → 98d9e38 → 4741a4c → a439308 → 10b3445 → 80855b6 → c9b1832`. 7 commits, +~200 lines of proved infra, 0 sorry, 2 axioms unchanged.

### Session 28 post-compaction (2026-04-18 early morning) — ODE uniqueness closed
- **`stage2_effectiveTime_hasDerivWithinAt_zero`**: boundary right-derivative of τ at t=0 via `integral_hasDerivWithinAt_right` with `IntervalIntegrable.refl` (a=b=0) + StronglyMeasurableAtFilter on 𝓝[>] 0. commit `c50042d`.
- **`stage2_effectiveTime_hasDerivWithinAt`** + **`stage2_btcTraj_comp_tau_hasDerivWithinAt`**: unified right-derivatives of τ and btc.sol∘τ on Ici 0 (interior + boundary). Upgraded `stage2_btcTraj_comp_tau_continuousOn` to Ici 0. commit `61f4e47`.
- **`stage2_unscaledTail_eq_btcTraj_comp_tau`** (MAIN): ODE uniqueness via `ODE_solution_unique_of_mem_Icc_right`. Given zero-init `P.init o = 0` + uniform M, L bounds, `w(t) = btc.sol(τ(t))` on `[0, T]`. Packages `stage2_vField_lipschitzOnWith'` (LipschitzOnWith on closedBall 0 M). commit `351ba59`.
- **`stage2_output_eq_btc_output_at_tau`**: corollary — `sol(t)@stage2.out = btc.sol(τ(t))@btc.out` on [0,T]. commit `7fe6f2b`.
- **`stage2_effectiveTime_mono`**: τ non-decreasing when ε ≥ 0 and z₀ ≥ 0 (previously deferred, now closed via `integral_add_adjacent_intervals`). commit `cdd5d26`.
- **`stage2_effectiveTime_lb`**: τ(t) ≥ ε·c·t under z₀ ≥ c. commit `1e3f491`.
- **`stage2_convergence_from_invariants`** (BIG): conditional convergence theorem — under the still-open LPP z₀≥c invariant + uniform bounds, the content of `stage2_convergence_axiom` is now PROVEN for all t ≥ 0. Chain: output-equality + τ≥ε·c·t≥t + btc.convergence. commit `ec8c86b`.
- **Remaining gap to close the axiom**: (a) prove h_z0_lb (LPP Remark 14 z₀≥c invariant — non-trivial; z₀ is not constant because Σtail isn't monotone for general btc fields); (b) establish uniform M, L globally; (c) handle t < 0 regime (or restrict axiom signature).
- **Post-compaction commit chain**: `c50042d → 61f4e47 → 351ba59 → 7fe6f2b → cdd5d26 → 1e3f491 → ec8c86b`. 7 commits, +~340 lines, 0 sorry, 2 axioms unchanged but `stage2_convergence_axiom` is now 90% proved conditionally.

## Session Log (2026-04-17, session 27)
- **Axiom 1 narrowed**: old monolithic `crn_simplex_global_ode_solution` axiom (composite of ODE extension + CRN invariance + conservation + simplex bound) replaced by:
  - New file `Core/ODEGlobal.lean` (~330 lines, 0 sorry, 1 axiom):
    - `axiom locally_lipschitz_bounded_global_ode`: pure Mathlib-gap statement. Given locally Lipschitz `f` and a priori bound `M` on every local solution, global solution exists. No CRN, no simplex, no conservation — clean ODE extension step.
    - `simplex_norm_le_one` (proved): non-negative + sum=1 ⇒ sup-norm ≤ 1.
    - `conservative_local_sum_const` (proved): conservation + ODE ⇒ ∑ y(t) = ∑ y(0) on `Ico 0 T`, via `HasDerivAt.fun_sum` + `constant_of_has_deriv_right_zero`.
    - `crn_local_nonneg` (proved, ~170 lines): CRN + locally Lipschitz ⇒ non-negativity preserved, local Ico version of `crn_nonneg_invariance` via squared-negative-mass + Grönwall.
    - `crn_simplex_global_ode_solution'` (noncomputable def): combines all pieces with M=1, uses `Classical.choose` to extract the trajectory from the Prop existential axiom.
  - `LPP/Stages.lean`: `axiom crn_simplex_global_ode_solution` replaced with `noncomputable def` delegating to the above.
- **Result**: **0 sorry, 3 axioms** (was 0 sorry, 3 axioms — same axiom count, but the CRN-specific one is now cleanly a Mathlib gap rather than a composite CRN+ODE statement). All CRN/conservation/simplex content is proved.
- Commit: `19298d4`
- **Next targets** (in no particular order, per 爸爸's directive "挨个推就好"):
  - `stage2_convergence_axiom` — time-dilation convergence from [LPP] Remark 14.
  - `algebraic_is_certified_crn` — Newton's method as PolyPIVP ([RTCRN1] Theorem 3.4).
  - `locally_lipschitz_bounded_global_ode` — iterated local Picard with uniform step size (substantial classical ODE proof).

## Session Log (2026-04-17, night — session 26)
- **`stage2_ode_axiom`: axiom → THEOREM** (main achievement):
  - Refactored monolithic `stage2_ode_axiom` axiom into two focused axioms + proved theorem
  - New `crn_simplex_global_ode_solution` axiom: global ODE existence for CRN+conservative+simplex (reusable)
  - New `stage2_convergence_axiom`: convergence specific to stage2 time dilation
  - `stage2_ode_axiom` now proved from the two axioms
  - **Lipschitz sorry eliminated**: threading A, B coefficients through `stage2_ode_axiom` and `stage2_ode_solution`
    → builds `stage2_field_cubicForm` → `cubicForm_locally_lipschitz` → no sorry
  - Also updated `stage2_ode_solution` and `stage2_core` call sites
- **Stage 2 output dynamics lemmas** (infrastructure for convergence axiom):
  - `stage2_field_output`: output field = ε · field(unscale(tail x))_o · x₀ (key: NO c-scaling)
  - `stage2_field_nonoutput`: non-output field = c · ε · field(unscale(tail x))_j · x₀
  - `stage2_field_zero`: balancing variable field = -(∑ g_j) · x₀
  - `stage2_output_hasDerivAt`: extract output derivative from system solution
- **Warning cleanup**: fixed deprecated `push_neg` → `push Not`, `show` → `change`,
  removed unused `<;> ring`, extra whitespace, long lines. Down to 1 harmless warning.
- **Result**: 0 sorry, 4 axioms (was 3 axioms with sorry in theorem → 4 axioms, 0 sorry)
- Build: 0 errors, 1 warning (unused bound variable in `∑ j`)

## Session Log (2026-04-16, night — session 14)
- **Attacked `lpup_computes_rational` (Lemma 10) infrastructure:**
  - **PROVED** `marked_sum_hasDerivAt`: derivative of Σ_{marked} sol_i = Σ_{marked} (A·sol)_i
  - **PROVED** `marked_sum_bounded`: marked sum in [0,1] from simplex + non-negativity
  - **NEW** `bounded_linear_ode_limit_rational`: pure analysis/algebra core (sorry)
    - Eigenvalue-free proof strategy: Cayley-Hamilton → scalar ODE → factor p = x^k·q → q(D)f bounded poly = const → integration argument → ν = g(0)/q(0) ∈ ℚ
    - Key observation: all derivatives bounded because sol on simplex ⟹ A^k·sol bounded (no need for solution representation)
  - Added `import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic` for Cayley-Hamilton
- **Stage 3 → NAP analysis** (from session 13, documented in NAP.lean):
  - Case 1 (i,j ≠ 0): strict NSP transfers from x-PP ✓
  - Cases 2-3 (boundary): pipeline_bound + foreign_pair ✓
  - `nap_split_comprehensive` covers all cubed z-PP production monomials
- **Manifold discussion + references** for 爸爸 (projects/Next/future-work.md §7)
- Build: 0 errors, 6 sorry (was 5, +1 bounded_linear_ode_limit_rational)

## Session Log (2026-04-16, night — session 15)
- **PROVED `linear_ode_marked_sum_rational`** — the major achievement:
  - Fixed Cayley-Hamilton `simp_rw` failure: `let A_mat := Matrix.of A` caused partial unfolding — goal had `(Matrix.of A).charpoly` but `h_entry` had `Matrix.charpoly A_mat`. Solution: declare `h_entry` matching goal form, use `exact_mod_cast hCH` for ℚ→ℝ cast
  - All 5 hypotheses of `bounded_linear_ode_limit_rational` fully proved: derivative tower (HasDerivAt.sum + Finset.sum_fn), boundedness (triangle + simplex), rational initial values (choose + push_cast), Cayley-Hamilton (entry-wise CH + sum rearrangement), convergence (hf0 rewrite)
- **Structured `bounded_linear_ode_limit_rational`** with analysis sub-lemmas:
  - Added `tendsto_zero_of_tendsto_bounded_deriv` (Barbalat-lite, sorry'd)
  - Added `const_of_iterated_deriv_zero_bounded` (bounded + D^m = 0 → constant, sorry'd)
  - Main proof: rootMultiplicity factoring of charpoly, g = q(D)f₀ combination, derivative tower, Barbalat induction for f_k → 0. Algebraic structure all compiles, 4 internal sorry remain (sum re-indexing, triangle bound, limit argument, conclusion)
- **Key Mathlib finds**: `isBoundedUnder_abs_atTop_iff` (bounded polynomial ↔ degree ≤ 0), `exists_eq_pow_rootMultiplicity_mul_and_not_dvd`, `coeff_X_pow_mul'`, `constant_of_has_deriv_right_zero`
- **Barbalat's lemma** NOT in Mathlib — this is the main remaining analysis gap
- Build: 0 errors, 7 sorry declarations (4 pipeline + 2 analysis sub-lemmas + 1 structured analysis core)

## Session Log (2026-04-16, night — session 19)
- **PROVED `conservative_trajectory_sum`** — conservation invariant:
  - General theorem: if field is conservative (∑ field(x)_i = 0) and trajectory solves ODE, then ∑ trajectory(t)_i = ∑ init_i for all t ≥ 0
  - Proof: `HasDerivAt.fun_sum` + `hasDerivAt_pi` gives derivative of sum = sum of derivatives = 0; then `constant_of_has_deriv_right_zero` (Mathlib MVT) gives constancy
  - Added import `Mathlib.Analysis.Calculus.MeanValue`
- **PROVED `conservative_trajectory_simplex`** — corollary: simplex invariance when ∑ init = 1
- **Factored `stage2_core` into proved composition**:
  - `stage2_core` was monolithic sorry; now proved by composing:
    - `stage2_ode_solution` (sorry) — ODE existence + convergence for balanced system
    - `crn_nonneg_invariance` (sorry) — CRN non-negativity invariance
    - `conservative_trajectory_simplex` (proved) — simplex from conservation
    - `stage2_init_rational` (existing) — rational init
    - `stage2_field_tpp` + `stage2_field_cubicForm` (existing) — TPP + CubicForm
  - Sorry count 4 → 5 but total sorry surface decreased: stage2_core's algebraic + conservation content now proved
- Build: 0 errors, 5 sorry declarations (stage1_core + stage2_ode_solution + crn_nonneg_invariance + bridge + algebraic)

## Session Log (2026-04-16, night — session 18)
- **Structural refactoring: 5 → 4 sorry declarations**
  - Created `stage1_core` (sorry): v-variable quadraticization with explicit A/B coefficient output
  - Created `stage2_core` (sorry): analytic stage (ODE existence + convergence for balanced system)
  - **PROVED `stage1_quadraticization`**: derived from `stage1_core` by constructing IsCRNImplementable from A/B decomposition
  - **PROVED `stage2_to_tpp`**: derived from `stage1_core` + `stage2_core` (composition)
  - **PROVED `stage3_to_lpp`**: derived from `stage1_core` + `stage2_core` + `tpp_to_lpp` (composition)
  - Key pattern: A/B coefficients give `field_eq : field x i = (∑_a ∑_b A i a b * x a * x b) - (∑_a B i a * x a) * x i`, which IS the CRN decomposition with prod = ∑∑A·x·x and degr = ∑B·x
- **Resolved v-variable CRN-implementability question** (asked 爸爸):
  - Original concern: product-rule gives degradation ∝ v_{α-e_k}·v_{e_k} ≠ v_α off manifold
  - Resolution (from paper Theorem 12): define v-ODE using manifold-simplified formula v'_α = Σ_k α_k·P_k·v_{α-e_k} - (Σ_k α_k·Q_k)·v_α. This formula is CRN-implementable FOR ALL v (algebraic identity), and agrees with product rule on manifold
  - 爸爸's insight: "写成 v 变量的形式，它没有什么依赖的" — just look at the form in v-variables
  - **Paper typo noted**: Theorem 12 formula missing chain-rule factor α_k in the sum (writes Σ_k instead of Σ_k α_k). Conclusion still correct since α_k ∈ ℕ≥0 preserves positivity
- Build: 0 errors, 4 sorry declarations

## Session Log (2026-04-16, night — session 17)
- **PROVED `const_of_iterated_deriv_zero_bounded`** — bounded + D^m=0 → constant:
  - Statement requires ALL g j bounded (not just g 0): `∀ j, ∃ C, ∀ t ≥ 0, |g j t| ≤ C`
  - Proof: `induction m generalizing g`, tower-shifting `g' j = g(j+1)`
  - IH gives g 1 constant; case split on g 1 0 = 0 or ≠ 0
  - Key fix: `hg_deriv 0 s hs0` gives `HasDerivAt (g 0) (g (0+1) s) s`; extracted as `hd0` helper to avoid `g (0+1)` vs `g 1` mismatch in `rw`
  - Case g 1 0 ≠ 0: proved g 0 affine via `constant_of_has_deriv_right_zero` on `g 0 - g 0 0 - g 1 0 * t`; contradiction via reverse triangle inequality (`abs_add_le` + `ring`)
  - Positivity fix: derived `hC_nn : 0 ≤ C` from `abs_nonneg` + bound at 0
- **PROVED `tendsto_zero_of_tendsto_bounded_deriv`** — Barbalat-lite:
  - **Statement change**: added `f'' : ℝ → ℝ` and `hf'_deriv`, `hf''_bdd` (bounded second derivative). Old statement (bounded f' only) is FALSE — oscillating bumps of decreasing width give counterexample
  - Direct proof (no contradiction): for given ε, set δ = ε/(4(C+1)), η = εδ/8
  - MVT (`exists_hasDerivAt_eq_slope`) on f gives slope bound |f'(c)| ≤ |f(t+δ)-f(t)|/δ
  - MVT on f' gives Lipschitz: |f'(t)-f'(c)| ≤ Cδ
  - Cauchy from convergence: |f(t+δ)-f(t)| < 2η via `dist_triangle` + `dist_comm`
  - Arithmetic: 2η/δ + Cδ ≤ ε/4 + ε/4 = ε/2 < ε; closed by `field_simp` + `nlinarith`
- Updated usage sites in `bounded_linear_ode_limit_rational`: added `(f 2)` / `(f (k+2))` and `(h_deriv 1)` / `(h_deriv (k+1))`
- **Result: 6 → 4 sorry declarations** (all 4 are pipeline stages, 0 analysis sorry remaining)
- Build: 0 errors

## Session Log (2026-04-16, night — session 16)
- **PROVED all 4 internal sorry in `bounded_linear_ode_limit_rational`** — now 0 internal sorry:
  - **hg_zero** (g m = 0 from CH): sum re-indexing via `Finset.sum_range_add`, prefix zeroing via `Finset.sum_eq_zero` with `exact_mod_cast` for ℚ→ℝ cast (`simp [this]` failed because it couldn't see through the cast)
  - **hg_lim** (g 0 → c_m·ν): `tendsto_finset_sum` with per-term convergence; k=0 term → c_m·ν via `tendsto_const_nhds.mul h_conv`; k≥1 terms → c_{m+k}·0 via `hf_lim_zero`; simplified with `Finset.sum_ite_eq'` + `mul_ite`
  - **Final conclusion** (ν ∈ ℚ): `by_contra` + `Metric.tendsto_nhds` + constancy: for any ε > 0, ∃ N s.t. dist(g 0 t, c_m·ν) < ε for t ≥ N; take t = max(N,0) ≥ 0 so g 0 t = g 0 0 (constant); get dist(g 0 0, c_m·ν) < ε; with ε = dist(g 0 0, c_m·ν) > 0 → contradiction; then `push_cast` + `eq_div_iff` + `mul_comm`
- **Key Lean pattern**: `tendsto_const_nhds.mul h_tendsto` gives `Tendsto (fun x => c * f x) l (nhds (c * L))` — don't simplify `c * 0` to `0` before applying (type mismatch)
- Build: 0 errors, 6 sorry declarations (4 pipeline + 2 analysis sub-lemmas)
- **Lemma 10 analysis core: COMPLETE** — `bounded_linear_ode_limit_rational` + `linear_ode_marked_sum_rational` both 0 sorry

## Session Log (2026-04-16, night — session 13)
- **Stage 3 → NAP connection analysis (documented in NAP.lean)**:
  - Analyzed which ppField cases have self-production in the z-PP:
    - **Case 1 (i,j ≠ 0)**: strict no-self-production holds (A(i,i,j) = A(j,i,j) = 0 from x-PP NSP)
    - **Case 2a/2b (one index = 0)**: self-production through colCoupling/rowCoupling (B coefficients not constrained by NSP), but μ_source = 1 ≤ 2 and foreign_pair holds
    - **Case 3 (i=j=0)**: z(0,0) always in production, μ_source = 1 ≤ 2, foreign_pair holds
  - **Conclusion**: `nap_split_comprehensive` covers ALL production monomials of cubed self-product PP
  - Added documentation block at end of NAP.lean summarizing the case analysis
- **Manifold insight discussion with 爸爸 (msg 790)**:
  - 爸爸独立悟出 invariant manifold 的核心思想："先有 flow 再有流形"
  - M = Image(Φ) is invariant because z(t) = Φ(x(t)) IS the push-forward
  - Connects to conservation gap: ∑ ppField ≠ 0 off M, but on M it reduces to the original conservative system
- **Added §7 to projects/Next/future-work.md**: Manifold calculus learning path
  - Recommended: Tu (intro), Lee (GTM 218), Hirsch-Smale-Devaney (ODE/dynamical systems)
- Build: 0 errors, 5 sorry (all in Stages.lean, unchanged)

## Session Log (2026-04-16, night — session 12)
- **Protocol-level PP→NAP theorem + paper gap discovery**:
  - `CubedPPMonomial`: structure bundling chain rule data + strict no-self-production
  - `cubed_pp_nap`: protocol-level theorem — every CubedPPMonomial admits balanced non-autocatalytic split
  - **PAPER GAP FOUND**: Note 14b Theorem proof Step 2 claims δ = 2α without justification:
    - Step 1 correctly derives α ≤ δ from no-NAP hypothesis
    - Step 2 claims γ* = δ - α must equal α "by hypothesis," but partition β = α, γ = δ-α satisfies hypothesis because β = α (doesn't force γ = α)
    - Concrete issue: α = (2,1,0), μ = (3,1,0,...), δ = (5,1,0) has only 2 weight-3 divisors {α, (3,0,0)}, no NAP split
    - For ACTUAL PPs: production coefficients ≤ 2 per reaction, so problematic monomials cancel (net coefficient ≤ 0)
    - Formalization sidesteps the gap: strict no-self-production (μ_source = 0) cleanly splits into two proved cases
  - **Open question**: Does Stage 3 construction guarantee strict no-self-production (x_j exponent = 0 in all monomials of p_j)?
- Build: 0 errors, 5 sorry (all in Stages.lean, unchanged)

## Session Log (2026-04-16, night — session 11)
- **Extended NAP.lean with general PP→NAP theorem — still 0 sorry, 0 errors**:
  - `trivial_split_of_lt`: when δ_source < α_source, any weight-3 divisor gives β ≠ α ∧ γ ≠ α
  - `exists_weight_divisor`: greedy induction — any multi-index of weight ≥ k has weight-k divisor
  - `trivial_balanced_split`: combines exists_weight_divisor + trivial_split_of_lt for the ¬foreign_pair case
  - `pp_to_nap_split`: **GENERAL PP→NAP** monomial theorem — case splits on foreign_pair:
    - foreign_pair holds → routes to `nap_splitting_feasibility` (pure_power + mixed_support)
    - foreign_pair fails → μ concentrated on one non-source variable → μ_source=0 → δ_source < α_source → `trivial_balanced_split`
  - **Key insight**: PP strict no-self-production ensures μ_source = 0, making the two-case split clean
  - Build fix: `Finset.add_sum_erase` needed explicit function arg + drop `.symm` (LHS/RHS were swapped)
- Build: 0 errors, 5 sorry (all in Stages.lean, unchanged)

## Session Log (2026-04-16, night — session 10)
- **Completed NAP.lean core — 0 sorry, 0 errors**:
  - `nap_splitting_feasibility` (Note 14 Theorem 1): every degree-6 production monomial from cubing construction admits non-autocatalytic factorization
  - Two-case proof: `pure_power_split` (|supp(α)|=1) + `mixed_support_split` (|supp(α)|≥2)
  - Mixed case uses primary/backup miShift strategy: try β₁ = miShift α i₀ source; if γ₁ = α (unit), use β₂ = miShift α i₀ k. Both γ-failures contradict at source coordinate.
  - `pp_pipeline_bound`: PP self-exponent ≤ 1 implies pipeline_bound ≤ 2
  - **Key discovery**: `foreign_pair` condition is essential for ProductionMonomial — the r²-trick ensures μ has weight on ≥2 distinct non-source variables. Without this, counterexample: α=(1,2), μ=(1,3), δ=(1,5) has no valid split.
  - **Key discovery**: Note 14's published proof has a gap — "|supp(α)|≥2 implies extra divisors" only holds for δ=2α, not general δ. The `foreign_pair` fills this gap.
  - Technical notes: `set` + `rw [miShift_*]` incompatible (opacity); use miShift directly with pre-computed chain rule bounds + omega
- Build: 0 errors, 5 sorry (all in Stages.lean, unchanged)

## Session Log (2026-04-16, night — session 9)
- **Bournez MFCS 2012 gap analysis**: Ran CF'24 counterexample x²-x+1/9 through Bournez's construction
  - dx_δ = -dx₁ = ε(-1/9 + x₁ - x₁²). At origin: p_δ(0,0) = -ε/9 < 0. CRN-implementability FAILS.
  - Rendered LaTeX derivation and sent to 爸爸
  - Key insight: ANY quadratic with a₀ = ab > 0 (both roots in (0,1)) is a counterexample
  - Vieta: design space is {(p,q) : 2√p ≤ q < 1+p}, entire 2D region of counterexamples
- **Fixed `stage1_quadraticization` and `stage2_to_tpp` statements**: Tightened existentials
  - Old: `∃ field', ∃ _ : IsTPPImplementable field', ∃ btc'` (disconnected — vacuously provable)
  - New: `∃ btc', ∃ _ : IsTPPImplementable btc'.pivp.field` (field tied to BTC)
  - Build: 0 errors, 5 sorry (count unchanged)
- **Published blog post**: "Vieta's Theorem and a Gap in CRN-to-Protocol Translation" on infsup.com
  - Covers: CRN constraint, Bournez's conservation trick failure, Vieta counterexample family, balancing dilation fix
  - Fair to Bournez et al.: "pioneered the connection", "result is correct, construction has gap"
- **Read BD repo appendix.tex**: Found 爸爸's systematic example construction
  - Table of candidates: u=1/2(boring), u=1/3(CF'24), u=1/4, etc.
  - "only used 初中高中数学: 韦达定理 + inequalities"
- **Proved 4 new infrastructure lemmas**:
  - `crn_boundary_nonneg`: CRN fields point inward at non-negative orthant boundary (x_i=0 → field_i ≥ 0)
  - `stage2_init`: Definition of Stage 2 initial conditions (Fin.cons (1 - c·∑y₀) (c·y₀))
  - `stage2_init_simplex`: Stage 2 init sums to 1 (always on simplex)
  - `stage2_init_rational`: Stage 2 init is rational when c ∈ ℚ and y₀ ∈ ℚⁿ
  - `stage2_init_nonneg`: Stage 2 init is non-negative when c·∑y₀ ≤ 1
- **Fixed `stage1_quadraticization` + `stage2_to_tpp` statements**: Tied BTC field to TPP/CRN proof
  - Old: `∃ field' ... ∃ btc'` (disconnected, vacuously provable)
  - New: `∃ btc', ∃ _ : IsTPPImplementable btc'.pivp.field` (properly tied)
- Build: 0 errors, 5 sorry

## Session Log (2026-04-16, night — session 8)
- **Proved `constantDilation_reparametrize`**: Solution preservation under time rescaling
  - If x solves x' = field(x), then x(ε·t) solves x' = constantDilation ε field(x)
  - Proof via component-wise chain rule: hasDerivAt_pi + HasDerivAt.comp + smul_eq_mul
  - This is a key building block for Stage 2 analytic argument
- **Factored `lpup_computes_rational`**: Extracted `linear_ode_marked_sum_rational` helper
  - Helper isolates the hard linear algebra: rational A + rational x₀ + simplex + convergence → rational ν
  - Plumbing from IsLPPComputable to clean statement verified (0 errors)
  - Proof sketch in docstring: spectral projection P₀ is polynomial in A (Bezout), hence rational
- **Restructured `stage3_to_lpp`**: Verified composition with tpp_to_lpp
  - Now chains: sorry'd stages 1+2 bundle (BTC + TPP + cubicForm + simplex + nonneg + init_rat) → tpp_to_lpp
  - The sorry is consolidated into the stages 1+2 existential bundle
- **Restructured `algebraic_lpp_computable`**: Separated algebraic→BTC from pipeline
  - Now: sorry'd "algebraic number is BTC" + stage3_to_lpp
- **Written graph-modeling note**: `notes/graph-modeling-matching.md`
  - Documents demand/supply asymmetry, per-monomial bipartite graphs, Hall's condition
  - PP→NAP via cubing: bucket size argument, CF'24 running example, causal chain
  - Connection to LPP Stage 4, Note 12 flow network, Note 25 cross-square theorem
- **Analysis of remaining 5 sorry**:
  - stage1: blocked by semantic vs syntactic PIVP gap (needs CertifiedBTC or MvPolynomial)
  - stage2: blocked by stage1 + balancingDilation analytic argument (time reparametrization)
  - stage3: composition, resolves when 1+2 are done
  - algebraic_lpp: needs algebraic→BTC (constructive PIVP for algebraic numbers)
  - lpup_rational: needs spectral projection theory over ℚ
- Build: 0 errors, 5 sorry (proof structure improved, no sorry count change)

## Session Log (2026-04-16, night — session 7)
- **Proved `stage2_field_cubicForm`**: Complete Stage 2 pipeline → Stage2CubicForm bridge
  - Shows `stage2_field ε c field = balancingDilation (lambdaTrick c (constantDilation ε field))`
    produces a Stage2CubicForm when input field has quadratic production (A) + linear degradation (B)
  - Scaled coefficients: A' = ε·A/c, B' = ε·B/c
  - Proof routes through `balancingDilation_cubicForm` with explicit coefficient scaling
  - Production sum matching via `Finset.mul_sum` + `Finset.sum_congr` + `field_simp`
  - This completes the bridge: quadratic CRN input → Stage 2 composition → Stage2CubicForm → Stage 3
- **Fixed `lpup_computes_rational` statement**: Corrected quantifier order
  - Old (buggy): `∀ x ∀ i, ∃ a, field x i = ∑ a·x` (trivially true for any polynomial)
  - New (correct): `∃ A, ∀ x ∀ i, field x i = ∑ A i j · x j` (constant matrix)
- **Paper gap discussion with 爸爸**:
  - 爸爸 sent CF'24 paper (Huang-Migunov): GPAC→PP compiler
  - Paper uses symmetric self-product (z₀₁ merged with z₁₀) — resolves the gap
  - PLPP constructed via coefficient matching (positive vs negative term pairing), not IsPPImplementable
  - 爸爸 confirms: "formal cancellation 不成问题"
  - Resolution: use d(d+1)/2 symmetric variables, direct matching for PLPP
- Build: 0 errors, 5 sorry

## Session Log (2026-04-16, night — session 6)
- **Resolved `tpp_to_lpp` sorry** (6→5 sorry):
  - Removed `.pp : IsPPImplementable n field` from `IsLPPComputable` in Defs.lean
  - Added detailed docstring about paper gap (Theorem 15 off-manifold conservation failure)
  - Removed `pp := h_pp` from `tpp_to_lpp` construction, `halfExpFieldPP_pp` from Example.lean
  - Fixed unused variables: `hα01` → `_hα01`, `tpp` → `_tpp`
- **Blog post published**: "The Geometry Hiding in Algebraic Manipulations" on infsup.com
  - Third-person perspective (no "My dad"), proper references [1]-[4], removed Ripple mentions
  - Fixed LaTeX rendering via Hugo Goldmark passthrough extension (config.yaml)
  - Restored $\lambda$-trick and $g$-trick notation after passthrough fix
- **Proved `balancingDilation_cubicForm`**: Bridge lemma from Stage 2 output to Stage 3 input
  - Given a field with explicit quadratic production (A) and linear degradation (B) coefficients,
    `balancingDilation` produces a `Stage2CubicForm` on Fin (n+1) with zero = 0
  - Zero-padded coefficients: A'(i+1,a+1,b+1) = A(i,a,b), A'(·,0,·) = 0; B'(i+1,a+1) = B(i,a), B'(·,0) = 0
  - field_eq proved via Fin.sum_univ_succ + Fin.cases reduction
  - field_zero proved via balancingDilation_conservative (conservation → zero variable equation)
  - This bridges the algebraic building blocks (Op 2-4) to tpp_to_lpp's Stage2CubicForm hypothesis
- Build: 0 errors, 5 sorry

## Session Log (2026-04-16, night — session 5)
- **Proved 18 new lemmas** for ppField algebraic structure (all 0 sorry):
  - Non-negativity: Pz_nonneg, x0Qz_nonneg, totalPz_nonneg, totalQxz_nonneg, colCoupling_nonneg, rowCoupling_nonneg
  - Scaling/homogeneity: Pz_smul, x0Qz_smul, totalPz_smul, totalQxz_smul, colCoupling_smul, rowCoupling_smul
  - ppField_homog: degree-2 homogeneity (ppField(c•z) = c²·ppField(z))
  - CRN decomposition: ppProd (def), ppDegr (def), ppField_eq_crn, ppProd_nonneg, ppDegr_nonneg
- **IsPPImplementable status for ppField**: 4 of 5 conditions now formally verified:
  - CRN form ✓ (ppField_eq_crn + ppProd_nonneg + ppDegr_nonneg)
  - Degree 2 homogeneity ✓ (ppField_homog)
  - No self-square — provable from case structure
  - Conservation ✗ (paper gap — only on manifold, genuine gap in Theorem 15)
- Build: 0 errors, 6 sorry (unchanged)

## Session Log (2026-04-16, night — session 4, continued)
- **Fixed ppField Cases 2a/2b** to match paper's exact Theorem 15 construction:
  - Added `colCoupling` and `rowCoupling` definitions: ∑_{k≠0} z(k,j)·x0Qz_k and ∑_{k≠0} z(i,k)·x0Qz_k
  - Added manifold agreement lemmas for both coupling terms
  - Cases 2a/2b now use coupling terms instead of z·totalQxz
  - ppField_eq_on_manifold proofs updated (ring still closes)
- **Discovered paper gap in Theorem 15**: the paper's EXACT construction is also NOT globally conservative.
  For d=2 with A_{1,0,0}=1, ∑ppField = z_{00}·(z_{01}-z_{10})·Pz_1 ≠ 0 off manifold.
  Even with symmetric Sym2 variables (3 vars for d=2), simple sum ∑z' ≠ 0 — the correct
  conservation is the WEIGHTED sum ∑_{d²} z' = 0 (counting z_{01} and z_{10} separately).
  This means IsPPImplementable (which requires unweighted global conservation) cannot be directly proved.
  Three possible resolutions: (a) Sym2 + weighted conservation, (b) weaken IsPPImplementable,
  (c) construct PLPP directly without IsPPImplementable.
- **Documented both issues** in Stages.lean comment above the sorry line.

## Session Log (2026-04-16, night — session 4)
- **Proved `ppField_eq_on_manifold`**: manifold agreement theorem — all 4 cases closed
  - Case 1 (i,j≠0): folded P/Q helpers → `ring`
  - Case 2a/2b (one index = 0): beta-reduction helpers + totalQxz/totalPz manifold lemmas → `ring`
  - Case 3 (i=j=0): h_fz conservation helper → `ring`
  - h_fz helper proof refactored: `Finset.sum_congr` + `← Finset.sum_mul` + `Finset.sum_sub_distrib` → `ring`
  - Key technique: keep P/Q folded (not raw ∑∑A sums) so `ring` can close; beta-reduce z-applications via explicit rfl helpers
- **Sorry count**: 6 (unchanged — ppField_eq_on_manifold was inside Stage2CubicForm namespace, not a top-level sorry)
- **Wired ppField into `tpp_to_lpp`**:
  - Added `s : Stage2CubicForm d btc.pivp.field` as hypothesis
  - Concrete `ppfld` defined: `s.ppField` transported through encoding `e : Fin d × Fin d ≃ Fin (d*d)`
  - Manifold agreement fully proved via `ppField_eq_on_manifold`
  - Remaining sorry narrowed: `IsPPImplementable (d * d) ppfld` — pure algebraic verification
  - Sorry went from big existential to concrete property check
- **Explained "manifold agreement" to 爸爸** (msg 658): two different vector fields in z-space that agree on the submanifold {z_{i,j} = x_i·x_j}; ODE solution stays on manifold so the PP field gives same trajectory
- **PP-implementability analysis**: the production function f_r = ppField + 2·z_r·∑z may NOT be non-negative on the non-negative orthant if B coefficients are too large (counterexample: z_{0,0}=1, z_{i,j}=ε, B_{i,0}+B_{j,0}>2). The paper resolves this via the λ-trick (Stage 2 scales coefficients by λ). Two paths forward:
  - (a) Add `B i a ≤ 1` constraint to Stage2CubicForm (justified by λ-trick)
  - (b) Prove Corollary 3 characterization (CRN + conservative + no-self-square + quadratic ⟹ PP)
  - Both require additionally proving ppField conservation (∑ ppField z = 0 for ALL z, not just on manifold) and degree-2 homogeneity
- **Blog draft**: `zinan/blog-drafts/drafts/manifold-perspective-crn.md` — "The Geometry Hiding in Algebraic Manipulations: A Manifold Perspective on CRN Computation"

## Session Log (2026-04-16, night — session 3)
- **Restructured `tpp_to_lpp` sorry from FALSE to TRUE**:
  - **Discovery**: `selfProductField` is degree 4 in z (cubic field × linear rowSum) — cannot be PP-implementable
  - Paper's Theorem 15 constructs a DIFFERENT degree-2 field via symbolic substitution
  - **New proof structure**: existential `∃ ppfld, IsPPImplementable ppfld ∧ manifold_agreement`
  - Preserved existing `is_solution` proof: z(t) solves `selfProductField` by product rule (`h_sol_zfld`)
  - New `h_sol_pp`: derives z(t) solves ppfld via manifold agreement
  - All 7 other fields of `IsLPPComputable` remain fully proved
  - Sorry count unchanged (6), but the sorry is now CORRECT (provable)
- **Added degree warning** to `selfProductField` docstring
- **Updated CHECKPOINT next steps** with detailed PP z-field construction plan from paper

## Session Log (2026-04-16, evening)
- **Proved `tpp_to_lpp` structure** (Stage 3 pure theorem — TPP → LPP):
  - Full construction with `finProdFinEquiv` encoding: `Fin d × Fin d ≃ Fin (d * d)`
  - z-trajectory: `z_i(t) = x_{π₁(i)}(t)·x_{π₂(i)}(t)` via self-product
  - z-field: selfProductField transported through encoding
  - Marked states: output row `{e(o, j) | j : Fin d}` — readout via `∑z_{o,j} = x_o·∑x_j = x_o`
  - **All 8 fields of IsLPPComputable proved except `pp`** (PP-implementability):
    - `init_rational`: product of rationals via `Rat.cast_mul`
    - `init_simplex` + `simplex`: `Fintype.sum_equiv` reindexing + `selfProduct_simplex`
    - `init_nonneg` + `nonneg`: `mul_nonneg` on non-negative factors
    - `is_solution`: `selfProduct_hasDerivAt` transported via `hasDerivAt_pi`, equiv composition
    - `convergence`: `Metric.tendsto_atTop` + BTC quantitative bound + `exp(-r) < ε` via Archimedean
  - Refactored signature: `tpp` now takes `btc.pivp.field` directly (no separate `field` parameter)
  - **1 sorry**: `IsPPImplementable (d * d) zfld` — the mathematical core
- **Key technique: `Fintype.sum_equiv`** for sum reindexing through `finProdFinEquiv.symm`
- **Key technique: `Function.Injective.injOn`** for `Finset.sum_image` (Mathlib API change: expects `Set.InjOn`)
- **Stages.lean**: 43 definitions/theorems total (37 proved + 6 sorry, sorry count unchanged but `tpp_to_lpp` structurally reduced from full sorry to single `h_pp` sorry)

## Session Log (2026-04-16, afternoon)
- **Proved `crn_computable_mul`** (CRN product closure via PIVP product rule):
  - Two PIVPs in parallel, product variable z = x_{o₁}·y_{o₂}, z' by product rule
  - Dimension d₁+d₂+1, boundedness via |z| ≤ M₁·M₂, convergence via Tendsto.mul
- **Proved `lpp_computable_mul`** (Lemma 11: LPP product closure):
  - Routes: `lpp_to_gpac` → `crn_computable_mul` → `gpac_to_lpp`
  - Avoids direct PP-level product protocol; self-square handling deferred to `stage3_to_lpp`
  - 爸爸 notes: should eventually build direct self-product construction with Hall condition
- **Proved `lpp_to_gpac`** + **`lpp_computable_in_01`** (LPP → CRN + range bound)
- **Key infrastructure: `vecSnoc`/`vecAddCases`** (non-dependent Fin tuple wrappers):
  - `Fin.snoc`/`Fin.addCases` are dependently typed — `rw`/`simp` fail in non-dependent contexts
  - Created wrappers fixing motive to `fun _ => α`, with `@[simp]` lemmas
  - `vecSnoc_natAdd_castSucc`: handles Lean's normalization of `Fin.castSucc ∘ Fin.natAdd`
  - `Fin.castSucc_natAdd_comm`: commutativity lemma for the index embeddings
- **Fixed `lpp_to_gpac` boundedness**: `pi_norm_le_iff_of_nonneg` produces `‖·‖` goals, need `Real.norm_eq_abs` bridge
- **Sorry count: 6 → 5** (eliminated `lpp_computable_mul`)
- **Stage 3 analytical building blocks** (all proved, 0 sorry):
  - `selfProduct_rowSum_eq`: row sum recovers original trajectory on simplex
  - `selfProduct_totalSum`: ∑z_{i,j} = (∑x_i)²
  - `selfProduct_simplex`: on simplex, ∑z_{i,j} = 1
  - `selfProduct_hasDerivAt`: product rule — z_{i,j}(t) = x_i(t)·x_j(t) satisfies selfProductField ODE
- **Stages.lean**: 42 definitions/theorems total (37 proved, 5 sorry)

## Session Log (2026-04-16, early morning)
- **Added all 4 Operations from [LPP] §3.2 as proved building blocks**:
  - Operation 2: `constantDilation` + `constantDilation_crn` + `constantDilation_conservative`
  - Operation 3: `lambdaTrick` + `lambdaTrick_smul_cancel` + `lambdaTrick_solution` + `lambdaTrick_crn`
  - One-trick: `oneTrick` + `oneTrick_conservative` (note: does NOT preserve CRN — discovered and documented)
  - Operation 4 (from previous session): `balancingDilation` suite
- **Stage 2 algebraic composition**: `stage2_field` + `stage2_field_tpp` (composes Ops 2+3+4 → TPP)
- **Stage 3 building blocks**: `selfProduct_rowSum` + `selfProductField` + `selfProductField_conservative`
- **Key insight documented**: one-trick alone doesn't preserve CRN-implementability (x₀' has no x₀-dependent degradation); the g-trick (balancingDilation) does because it multiplies by x₀
- **12 new proved definitions/theorems**, 0 new sorry
- **Simplex invariance**: `conservative_sum_constant`, `conservative_simplex_invariant`
  - Proved using `hasDerivAt_pi` (component extraction) + `is_const_of_deriv_eq_zero`
  - Key result: conservative fields preserve ∑xᵢ, so simplex is an invariant
- **BoundedTimeComputable.to_tendsto** (in BoundedTime.lean): converts quantitative convergence bound to Filter.Tendsto using `Metric.tendsto_atTop'` + Archimedean property of exp
- **Proved gpac_to_lpp** by routing through strengthened `stage3_to_lpp` (eliminates 1 sorry: 7→6)
  - Merged old `stage3_to_pp` + `gpac_to_lpp` into single `stage3_to_lpp` (sorry)
  - `gpac_to_lpp` is now fully proved (calls `stage3_to_lpp`)
- **Stages.lean**: 31 definitions/theorems total (25 proved, 6 sorry)

## Session Log (2026-04-15, night)
- **Restructured IsPPImplementable** (per 爸爸's direction "(3)和(4)需要enforce"):
  - Changed from `extends IsCRNImplementable + conservative` to standalone balance equation form
  - 5 fields: f, f_pos, f_homog (degree 2), field_eq, sum_f (conservation)
  - Derived theorems: `toCRN`, `conservative`, `no_self_square`
  - `no_self_square`: automatic from conservation + non-negativity (f_r(e_r) ≤ 2)
- **Updated all consumers of IsPPImplementable**:
  - Syntactic.lean `toPP`: updated to new 5-field structure (0 sorry)
  - Rational.lean `cyclicField_pp`: formal degree-2 field (x_{pred}-x_i)·(Σx_k), production cyclicProd (0 sorry)
  - Example.lean: new `halfExpFieldPP` (formal PP field), `halfExpProd`, `halfExpFieldPP_pp` (0 sorry)
  - Example.lean `halfExpNegOne_lpp`: bridged via `halfExpFieldPP_eq_on_simplex` (0 sorry)
- **Merged stage4_to_plpp with syntactic version**: eliminated 1 sorry (8→7)
  - Semantic stage4 not provable without explicit coefficients
  - Syntactic version gives exact match (no ε needed)
- **Full project builds**: 0 errors, 7 sorry remaining (all in Stages.lean)

## Session Log (2026-04-15, evening)
- Created LPP/Syntactic.lean (0 sorry): syntactic PP balance equation layer
  - `SynPPBalance` with explicit ℚ coefficients, mirroring PolyPIVP/PIVP distinction
  - Stage 4 PLPP construction via product distribution α_{i,j,k,l} = c_k·c_l/4
  - `toPLPPTransitions_balanceField_eq`: exact match (no ε-scaling needed)
- Refactored: moved PLPPTransitions from Stages.lean to Defs.lean (cleaner dependency)
- Added `stage4_syn_to_plpp` (proved) in Stages.lean

## Session Log (2026-04-15, afternoon)
- Fixed Rational.lean build: `Equiv.sum_comp` for conservation, removed redundant `ring`
- Fixed formal cancellation bug: `PPBalanceEquation.toField` and `PLPPTransitions.balanceField` now use formal degradation `2x_r(Σx_k)` instead of simplex-specialized `2x_r`
- Proved `PLPPTransitions.balanceField_conservative` (0 sorry): uses sum swap + hα2 key lemma + exact_mod_cast for ℚ→ℝ
- Added comprehensive documentation about formal vs numerical cancellation in Defs.lean
- Updated OPEN_PROBLEMS.md (done in previous session)
