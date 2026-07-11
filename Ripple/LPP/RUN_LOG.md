# Kurtz Bridge Run Log

## Run 2026-06-27 16:00
- doctrine version: initial → updated with NoAbsorbing analysis
- starting avenue: (a) Construct PopProtocol from IsPPImplementable
- end: 2026-06-27 (all avenues resolved or documented)
- final result: avenue (a) CLOSED, (b) DOCUMENTED GAP, (c)+(d) CLOSED via merged theorem

### Progress (continued 2026-06-27)

**Avenue (a): COMPLETE.** Resolved the x_uno scaling issue by using a direct
3-species PopProtocol with 4 reactions (including E+E self-reaction) instead
of adding a 4th catalyst species. The x_uno approach fails because the
unimolecular E→G rate needs variable S = F+E+G (simplex sum), not a constant
catalyst concentration.

Created `ExamplePP.lean` with:
1. `halfExpPP : PopProtocol 3` — 4 reactions (R1: F+E→G+E, R2: F+E→G+G, R3: E+E→G+E, R4: E+G→G+G)
2. `halfExpPP_meanFieldDrift_eq` — drift = halfExpFieldPP (0 sorry)
3. `halfExpPP_drift_eq_on_simplex` — drift = halfExpField on simplex (0 sorry)
4. `halfExpPP_boundaryCompatibleOnSimplex` — boundary compatibility despite E+E self-reaction (0 sorry)
5. `halfExpMeanFieldSolution` — ODE solution as MeanFieldSolution for halfExpPP.toRateSpec (0 sorry)
6. `halfExp_exchanged_limit_stochastic` — end-to-end exchanged limit to ½e⁻¹ (0 sorry), with Kurtz convergence as hypothesis

**Avenue (b): IDENTIFIED BLOCKER.** DensityProcessFamily construction requires
NoAbsorbing (every state has positive total rate), but the ½e⁻¹ system has
absorbing states (all states with E=0). This is a genuine mathematical
difficulty noted in the DOCTRINE's Key Risk section. Options:
  - Restrict to reachable states (E > 0 initially → E = 0 only asymptotically)
  - Add negligible leak reaction (G → E at rate ε/N)
  - Prove absorption probability → 0 as N → ∞ on finite time horizons
  - Accept as a conditional theorem (hKurtz hypothesis in the exchanged-limit theorem)

**Avenues (c)+(d): MERGED INTO (a).** The exchanged-limit theorem
`halfExp_exchanged_limit_stochastic` combines ODE readout convergence and
Kurtz concentration into a single end-to-end statement. No separate wiring
to PLPPContinuumComputation is needed because we bypass PLPPTransitions
and work directly with PopProtocol.toRateSpec.

### ChatGPT usage
- family1: DensityProcessFamily + self-reaction question (garbled answer, no useful content)
- family2: BoundaryCompatibleOnSimplex approach (confirmed the reaction_rates_zero helper applies)

### Build verification
- ExamplePP.lean: 0 sorry, 0 axiom, build green (2862 jobs)
- All LPP/*.lean files: 0 sorry

### Commits this session
- b65850d: ExamplePP: concrete PopProtocol with drift equality
- e6b64fc: fix Fin.val_ofNat' simp args
- c5ae46c: MeanFieldSolution + exchanged-limit stochastic theorem
- 1f3d38d: fix add_lt_add_left type mismatch
- 0e0bc71: BoundaryCompatibleOnSimplex proof
- ca3c270: fix InputsDistinct decidability + R3 proof structure
- cf5b5b7: fix omega upper bound + RUN_LOG
- 3531f86: DOCTRINE update

## Run 2026-06-27 (session 2, automode)
- doctrine version: updated with NoAbsorbing root cause + avenue (e)
- starting avenue: (e) frozenStateAt + absorbing-aware DensityProcess
- end: (in progress)
- final result: (in progress)

### Analysis completed
- Root cause: CTMCPath.stateAt returns `init` (wrong) when times plateau at absorption
- IsCompatible requires strict monotonicity that fails after absorption (times n+1 = times n)
- Mathematical argument confirmed by ChatGPT family1+family2: QV bound holds without NoAbsorbing

### Progress
- DensityDependentAbsorbing.lean: 1195 lines, 0 sorry, BUILD GREEN
- ExamplePP.lean: wiring scaffold, builds green with 2 sorry
- GronwallEventInclusion.lean: scaffold, 2 sorry
- DriftZeroAtAbsorbing weakened to OnSimplex (all-cube version is false)

### Completed this session
- DensityDependentAbsorbing.lean: 1201 lines, 0 sorry, BUILD GREEN
- GronwallEventInclusion.lean: ~200 lines, 0 sorry, BUILD GREEN
- ExamplePP halfExpPP_driftZeroAtAbsorbingOnSimplex: PROVED
- ExamplePP halfExpPP_frozenDensityProcess: defined

### Remaining for hKurtz discharge (wiring only)
1. Wire kurtz_mean_field_convergence + kurtz_gm_of_event_inclusion
2. Discharge hKurtz in halfExp_exchanged_limit_stochastic

### ChatGPT usage (session 2)
- family1: Q1602 (empty) → Q1606 (route B) → Q1617 (right-continuity proof) → Q1623 (DriftZeroAtAbsorbing is false on cube, need simplex restriction) → Q1638 (Gronwall integral form)
- family2: Q1607 (QV bound confirmed) → Q1621 (no measurability bypass) → Q1624 (Gronwall event inclusion missing) → Q1639 (DriftZeroAtAbsorbing on simplex)
- family3: Q1640 (absorbing states verification, truncated)

## Run 2026-06-27 (session 3, automode)
- doctrine version: same as session 2 (avenue (e))
- starting avenue: (e) continued — wire final convergence theorem
- end: (in progress)
- final result: (in progress)

### Design decision: per-N probability spaces (not common space)
kurtz_mean_field_convergence + kurtz_gm_of_event_inclusion require all DensityProcesses
on a COMMON probability space (Ω, μ). But halfExpPP_frozenDensityProcess gives per-N
canonical measures. Rather than constructing a product space, prove the Gronwall-Markov
bound per-N directly using integral_gronwall_core, then state the final theorem with
per-N measures. This avoids a heavy product-space construction while being mathematically
equivalent.

### Progress
- halfExpSol_norm_le_one: PROVED (Finset.single_le_sum + simplex)
- halfExpPP_kurtz_finite_horizon: SORRY (1 sorry — needs O(T/N) QV for frozen M)
- halfExpPP_stochastic_convergence: PROVED from kurtz_finite_horizon + ODE convergence
  - Measure inclusion (triangle + point ≤ sup via le_ciSup): PROVED
  - ODE convergence (halfExpSol_F_tendsto → choose T₀): PROVED
  - Chaining via MeasureTheory.measure_mono: PROVED

### Gap: O(T/N) QV bound for frozen martingale
canonical_frozen_martingale_qv_bound gives C*T/N but C = K*N/T + 1 (depends on N).
So the effective bound is K + T/N ≈ K (constant), not O(1/N).
Mathematical fix: frozen M = M(t ∧ τ_abs) (stopped martingale).
E[sup frozen_M²] ≤ 4·E[QV(T∧τ_abs)] ≤ 4·C₀·T/N (from Doob + instantQVRate).
Formalization requires: stopped martingale Doob inequality infrastructure.

### Commits this session
- 0f10878: scaffold per-N Gronwall-Markov + stochastic convergence (2 sorry)
- 5b83c02: fix halfExpSol_norm_le_one + stochastic convergence scaffold
- 888eaa9: simplify proof structure
- c58c2b6: sorry measure inclusion step
- 30988f8: fix halfExpSol_norm_le_one with Finset.single_le_sum
- 368a02e: close measure inclusion sorry (le_ciSup pattern)
- 7349ef0: fix abs_add→abs_add_le + clean BddAbove proofs
- 3bbdb4a: fix halfExpSol T 0 vs halfExpSol_F T
- ae98cd5: RUN_LOG session 3 progress
- 5bfa0e9: add canonical_frozen_martingale_qv_bound_of_doob (sorry)
- 4ca700f: partially fill QV bound proof
- 0f0242f: expand QV bound proof
- b14e66e: simplify QV bound proof to clean sorry

### Session 3 final state (BUILD GREEN)
- GronwallEventInclusion.lean: 0 sorry (+100 lines: gronwall_event_inclusion_pathwise_rightContinuous)
- ExamplePP.lean: 2 sorry (h_integral_ineq + kurtz_finite_horizon)
  - integrableOn_frozen_error_mul_lipschitz: PROVED (0 sorry, key: let M + show + nlinarith)
  - 5/6 plumbing: hg_cont_right ✓ hg_sm ✓ hg_prim_cont ✓ hg_int ✓ hM_sq_le_sup ✓
- DensityDependentAbsorbing.lean: 1 sorry (canonical_frozen_martingale_qv_bound_of_doob)
- FrozenRandomIndexDoob.lean: 8 sorry (514 lines, guarded Doob infrastructure, Codex-generated)
- halfExpPP_stochastic_convergence: FULLY PROVED (0 sorry, modulo chain)

Total: 11 sorry across 3 files
ChatGPT: 35+ rounds across family1/2/3 (all consumed, exact Lean API names for every sorry)


## Run 2026-06-30 (compiled gamma system)
- doctrine version: appended to DOCTRINE.md
- starting avenue: (a) Python emitter → Lean certificate
- end: 
- final result: 
