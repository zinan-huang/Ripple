/-
  Ripple.LPP.ExamplePP — Concrete PopProtocol for the ½e⁻¹ System

  Constructs the population protocol whose mean-field ODE is exactly
  `halfExpFieldPP` (the bimolecular PP embedding of the ½e⁻¹ system).

  Species: F(0), E(1), G(2).

  Reactions:
    R1: F + E → G + E    (catalytic conversion of F by E)
    R2: F + E → G + G    (absorption: both consumed, two G produced)
    R3: E + E → G + E    (self-interaction: unimolecular E→G embedded)
    R4: E + G → G + G    (E absorbed by G environment)

  The combination R2 + R3 + R4 implements the unimolecular decay E→G
  via the bimolecular embedding: E' = -E·(F+E+G) = -E·S, which on
  the simplex (S = 1) equals E' = -E.

  R3 is a self-reaction (in1 = in2 = E), so the protocol is NOT
  InputsDistinct.  The mean-field drift is still well-defined and
  matches halfExpFieldPP exactly.
-/

import Ripple.LPP.Example
import Ripple.Kurtz.PopulationProtocol
import Ripple.Kurtz.MeanField
import Ripple.CTMC.DensityDependentAbsorbing
import Ripple.CTMC.FrozenRandomIndexDoob
import Ripple.Kurtz.GronwallEventInclusion
import Ripple.Kurtz.FiniteHorizonGeneric
import Mathlib.MeasureTheory.SpecificCodomains.Pi

namespace Ripple

open Kurtz

/-! ## The four reactions -/

def halfExp_rxn1 : PPReaction 3 := ⟨0, 1, 2, 1⟩  -- F+E → G+E
def halfExp_rxn2 : PPReaction 3 := ⟨0, 1, 2, 2⟩  -- F+E → G+G
def halfExp_rxn3 : PPReaction 3 := ⟨1, 1, 2, 1⟩  -- E+E → G+E
def halfExp_rxn4 : PPReaction 3 := ⟨1, 2, 2, 2⟩  -- E+G → G+G

/-! ## The population protocol -/

def halfExpPP : PopProtocol 3 :=
  ⟨{halfExp_rxn1, halfExp_rxn2, halfExp_rxn3, halfExp_rxn4}⟩

/-! ## Drift equality: meanFieldDrift = halfExpFieldPP

  The mean-field drift of halfExpPP is:
    F' = (-1)·FE + (-1)·FE + 0 + 0 = -2FE
    E' = 0 + (-1)·FE + (-1)·E² + (-1)·EG = -E(F+E+G) = -E·S
    G' = 1·FE + 2·FE + 1·E² + 1·EG = 3FE + E² + EG = 2FE + E·S

  This exactly equals halfExpFieldPP. -/

private theorem halfExp_rxns_distinct_12 : halfExp_rxn1 ≠ halfExp_rxn2 := by decide
private theorem halfExp_rxns_distinct_13 : halfExp_rxn1 ≠ halfExp_rxn3 := by decide
private theorem halfExp_rxns_distinct_14 : halfExp_rxn1 ≠ halfExp_rxn4 := by decide
private theorem halfExp_rxns_distinct_23 : halfExp_rxn2 ≠ halfExp_rxn3 := by decide
private theorem halfExp_rxns_distinct_24 : halfExp_rxn2 ≠ halfExp_rxn4 := by decide
private theorem halfExp_rxns_distinct_34 : halfExp_rxn3 ≠ halfExp_rxn4 := by decide

theorem halfExpPP_meanFieldDrift_eq :
    halfExpPP.meanFieldDrift = halfExpFieldPP := by
  ext x i
  simp only [PopProtocol.meanFieldDrift, halfExpPP, halfExpFieldPP,
    PPReaction.netChange, PPReaction.massActionRate,
    halfExp_rxn1, halfExp_rxn2, halfExp_rxn3, halfExp_rxn4,
    Finset.sum_insert (show halfExp_rxn1 ∉
      ({halfExp_rxn2, halfExp_rxn3, halfExp_rxn4} : Finset _) from by decide),
    Finset.sum_insert (show halfExp_rxn2 ∉
      ({halfExp_rxn3, halfExp_rxn4} : Finset _) from by decide),
    Finset.sum_insert (show halfExp_rxn3 ∉
      ({halfExp_rxn4} : Finset _) from by decide),
    Finset.sum_singleton]
  fin_cases i <;> simp (config := { decide := true }) <;> ring

/-! ## Connecting to Stochastic.lean

  With the drift equality established, the PopProtocol's RateSpec
  is compatible with the existing Kurtz infrastructure. The key
  connection:

  halfExpPP.toRateSpec.drift = halfExpPP.meanFieldDrift (by meanFieldDrift_eq_drift)
                              = halfExpFieldPP (by halfExpPP_meanFieldDrift_eq)
                              = halfExpField on simplex (by halfExpFieldPP_eq_on_simplex)

  This provides the bridge between the stochastic density-dependent
  process (Kurtz framework) and the deterministic ODE (LPP framework).
-/

theorem halfExpPP_drift_eq :
    halfExpPP.toRateSpec.drift = halfExpFieldPP := by
  rw [← halfExpPP.meanFieldDrift_eq_drift]
  exact halfExpPP_meanFieldDrift_eq

theorem halfExpPP_drift_eq_on_simplex (x : Fin 3 → ℝ) (h : x 0 + x 1 + x 2 = 1) :
    halfExpPP.toRateSpec.drift x = halfExpField x := by
  rw [halfExpPP_drift_eq]
  exact halfExpFieldPP_eq_on_simplex x h

/-! ## Boundary compatibility for halfExpPP

  Even though the protocol is NOT InputsDistinct (due to E+E→G+E),
  the mass-action rates are boundary-compatible on the simplex.

  Key insight: for every reaction, if the post-state would go out of
  bounds, then at least one input species has zero count, hence zero
  mass-action rate. For the E+E reaction specifically: net change is
  (0,-1,+1), so the only out-of-bounds case is x_E = 0, where the
  rate x_E² = 0. -/

theorem halfExpPP_boundaryCompatibleOnSimplex (N : ℕ) (hN : 0 < N) :
    (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).BoundaryCompatibleOnSimplex := by
  refine halfExpPP.toDensityDepCTMC_boundaryCompatibleOnSimplex_of_reaction_rates_zero
    N hN ?_
  intro x hx r hr himpossible
  have hsum : ∑ i, (x i : ℕ) = N := by
    simpa [CTMC.DensityDepCTMC.InSimplex, CTMC.DensityDepCTMC.totalCount] using hx
  simp only [halfExpPP, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · -- R1: F+E → G+E (InputsDistinct)
    by_cases hzero1 : (x (0 : Fin 3) : ℕ) = 0
    · simp [PPReaction.massActionRate, CTMC.DensityDepCTMC.scaledState, hzero1,
        halfExp_rxn1]
    · by_cases hzero2 : (x (1 : Fin 3) : ℕ) = 0
      · simp [PPReaction.massActionRate, CTMC.DensityDepCTMC.scaledState, hzero2,
          halfExp_rxn1]
      · exfalso; apply himpossible
        exact PPReaction.exists_realizing_state_of_inputsDistinct_of_input_counts_pos
          halfExp_rxn1 (show halfExp_rxn1.InputsDistinct from by simp [PPReaction.InputsDistinct, halfExp_rxn1]) x hsum
          (Nat.pos_of_ne_zero hzero1) (Nat.pos_of_ne_zero hzero2)
  · -- R2: F+E → G+G (InputsDistinct)
    by_cases hzero1 : (x (0 : Fin 3) : ℕ) = 0
    · simp [PPReaction.massActionRate, CTMC.DensityDepCTMC.scaledState, hzero1,
        halfExp_rxn2]
    · by_cases hzero2 : (x (1 : Fin 3) : ℕ) = 0
      · simp [PPReaction.massActionRate, CTMC.DensityDepCTMC.scaledState, hzero2,
          halfExp_rxn2]
      · exfalso; apply himpossible
        exact PPReaction.exists_realizing_state_of_inputsDistinct_of_input_counts_pos
          halfExp_rxn2 (show halfExp_rxn2.InputsDistinct from by simp [PPReaction.InputsDistinct, halfExp_rxn2]) x hsum
          (Nat.pos_of_ne_zero hzero1) (Nat.pos_of_ne_zero hzero2)
  · -- R3: E+E → G+E (NOT InputsDistinct — self-reaction)
    by_cases hzero : (x (1 : Fin 3) : ℕ) = 0
    · simp [PPReaction.massActionRate, CTMC.DensityDepCTMC.scaledState, hzero,
        halfExp_rxn3]
    · exfalso; apply himpossible
      have hpos : 0 < (x (1 : Fin 3) : ℕ) := Nat.pos_of_ne_zero hzero
      have hsum3 : (x 0 : ℤ) + (x 1 : ℤ) + (x 2 : ℤ) = N := by
        have := hsum; simp only [Fin.sum_univ_three] at this; omega
      let y : Fin 3 → Fin (N + 1) := fun i =>
        ⟨Int.toNat ((x i : ℤ) + halfExp_rxn3.netChange i), by
          have hbd : 0 ≤ (x i : ℤ) + halfExp_rxn3.netChange i ∧
              (x i : ℤ) + halfExp_rxn3.netChange i ≤ N := by
            fin_cases i <;> simp [halfExp_rxn3, PPReaction.netChange] <;> omega
          exact Nat.lt_succ_of_le (Int.toNat_le.mpr hbd.2)⟩
      exact ⟨y, fun i => by
        have hnn : 0 ≤ (x i : ℤ) + halfExp_rxn3.netChange i := by
          fin_cases i <;> simp [halfExp_rxn3, PPReaction.netChange] <;> omega
        simp [y, Int.toNat_of_nonneg hnn]⟩
  · -- R4: E+G → G+G (InputsDistinct)
    by_cases hzero1 : (x (1 : Fin 3) : ℕ) = 0
    · simp [PPReaction.massActionRate, CTMC.DensityDepCTMC.scaledState, hzero1,
        halfExp_rxn4]
    · by_cases hzero2 : (x (2 : Fin 3) : ℕ) = 0
      · simp [PPReaction.massActionRate, CTMC.DensityDepCTMC.scaledState, hzero2,
          halfExp_rxn4]
      · exfalso; apply himpossible
        exact PPReaction.exists_realizing_state_of_inputsDistinct_of_input_counts_pos
          halfExp_rxn4 (show halfExp_rxn4.InputsDistinct from by simp [PPReaction.InputsDistinct, halfExp_rxn4]) x hsum
          (Nat.pos_of_ne_zero hzero1) (Nat.pos_of_ne_zero hzero2)

/-! ## The ½e⁻¹ system as a MeanFieldSolution for halfExpPP.toRateSpec

  The existing ODE solution halfExpSol satisfies the mean-field ODE
  because halfExpPP.toRateSpec.drift = halfExpField on the simplex,
  and halfExpSol stays on the simplex. -/

noncomputable def halfExpMeanFieldSolution :
    Kurtz.MeanFieldSolution 3 halfExpPP.toRateSpec where
  x₀ := halfExpSol 0
  sol := halfExpSol
  sol_init := rfl
  sol_ode := by
    intro t ht
    have h_simplex : halfExpSol t 0 + halfExpSol t 1 + halfExpSol t 2 = 1 := by
      have := halfExpSol_simplex_sum t; simp only [Fin.sum_univ_three] at this; exact this
    rw [halfExpPP_drift_eq_on_simplex _ h_simplex]
    exact halfExpSol_is_solution t ht

/-! ## Exchanged-order stochastic convergence to ½e⁻¹

  Assuming finite-horizon Kurtz convergence (the stochastic density process
  converges to the ODE solution for each fixed time horizon), the F-component
  of the stochastic process converges to ½e⁻¹ in the exchanged order:

    lim_{t→∞} lim_{N→∞} X̄^N_F(t) = ½e⁻¹

  The proof combines:
  1. Deterministic readout: F(t) → ½e⁻¹ (halfExpSol_F_tendsto)
  2. Kurtz concentration: X̄^N(T) ≈ sol(T) for large N
  3. Triangle inequality on the readout -/

theorem halfExp_exchanged_limit_stochastic
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (X : (N : ℕ) → Kurtz.DensityProcess 3 halfExpPP.toRateSpec N μ)
    (hKurtz : ∀ T > 0, ∀ δ > 0, ∀ η > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      μ {ω | ‖(X N).process T ω - halfExpSol T‖ > δ} ≤ ENNReal.ofReal η)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T ≥ T₀, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      μ {ω | |((X N).process T ω) 0 - Real.exp (-1) / 2| > ε} ≤
        ENNReal.ofReal η := by
  classical
  let ρ : ℝ := ε / 2
  have hρ : 0 < ρ := by positivity
  have htend := halfExpSol_F_tendsto
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨Traw, hTraw⟩ := htend ρ hρ
  let T₀ : ℝ := max Traw 1
  have hT₀_pos : 0 < T₀ := lt_of_lt_of_le zero_lt_one (le_max_right Traw 1)
  refine ⟨T₀, hT₀_pos, ?_⟩
  intro T hT
  have hTraw_le : Traw ≤ T := (le_max_left Traw 1).trans hT
  have hT_pos : 0 < T := hT₀_pos.trans_le hT
  have hode : |halfExpSol_F T - Real.exp (-1) / 2| < ρ := by
    simpa [Real.dist_eq] using hTraw T hTraw_le
  let δ : ℝ := ρ
  obtain ⟨N₀, hN₀⟩ := hKurtz T hT_pos δ hρ η hη
  refine ⟨N₀, fun N hN => ?_⟩
  refine (MeasureTheory.measure_mono ?_).trans (hN₀ N hN)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hnot
  push_neg at hnot
  have hcoord : |((X N).process T ω) 0 - halfExpSol_F T| ≤
      ‖(X N).process T ω - halfExpSol T‖ := by
    rw [show ((X N).process T ω) 0 - halfExpSol_F T =
      ((X N).process T ω - halfExpSol T) 0 from by simp [halfExpSol, Pi.sub_apply]]
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm _ 0
  have : |((X N).process T ω) 0 - Real.exp (-1) / 2| < ε := by
    calc |((X N).process T ω) 0 - Real.exp (-1) / 2|
        = |((X N).process T ω) 0 - halfExpSol_F T +
            (halfExpSol_F T - Real.exp (-1) / 2)| := by ring_nf
      _ ≤ |((X N).process T ω) 0 - halfExpSol_F T| +
            |halfExpSol_F T - Real.exp (-1) / 2| := abs_add_le _ _
      _ ≤ ‖(X N).process T ω - halfExpSol T‖ +
            |halfExpSol_F T - Real.exp (-1) / 2| := by gcongr
      _ ≤ δ + |halfExpSol_F T - Real.exp (-1) / 2| := by gcongr
      _ < ρ + ρ := by dsimp [δ]; linarith
      _ = ε := by dsimp [ρ]; ring
  linarith

/-! ## Additional CTMC building blocks

  These theorems don't require NoAbsorbing and prepare the
  pieces needed for the DensityProcessFamily construction. -/

theorem halfExpPP_conservativeJumps (N : ℕ) (hN : 0 < N) :
    (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).ConservativeJumps :=
  halfExpPP.toDensityDepCTMC_conservativeJumps N hN

/-! ## DriftZeroAtAbsorbingOnSimplex for ½e⁻¹

For positive `N`, absorbing states on the simplex have `E = 0`.
At these states, every mass-action rate involves E as a factor, so drift = 0. -/

private lemma halfExpPP_rate_rxn3Jump_pos_of_E_pos {N : ℕ} (hN : 0 < N)
    (x : Fin 3 → Fin (N + 1))
    (hEpos : 0 < (x (1 : Fin 3) : ℕ)) :
    0 < halfExpPP.toRateSpec.rate halfExp_rxn3.netChange
      ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).scaledState x) := by
  let M := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  have hscaled_nonneg : ∀ i, 0 ≤ M.scaledState x i := by
    intro i
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hEscaled_pos : 0 < M.scaledState x (1 : Fin 3) := by
    exact div_pos (Nat.cast_pos.mpr hEpos) (Nat.cast_pos.mpr hN)
  change 0 < ∑ r ∈ halfExpPP.reactions.filter
      (fun r => r.netChange = halfExp_rxn3.netChange),
    r.massActionRate (M.scaledState x)
  refine Finset.sum_pos' ?nonneg ?pos
  · intro r _hr
    exact mul_nonneg (hscaled_nonneg r.in1) (hscaled_nonneg r.in2)
  · refine ⟨halfExp_rxn3, ?_, ?_⟩
    · simp [halfExpPP]
    · simp [PPReaction.massActionRate, halfExp_rxn3, hEscaled_pos]

private lemma halfExpPP_exists_rxn3_target_of_E_pos {N : ℕ} (hN : 0 < N)
    (x : Fin 3 → Fin (N + 1))
    (hx : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x)
    (hEpos : 0 < (x (1 : Fin 3) : ℕ)) :
    ∃ y : Fin 3 → Fin (N + 1), x ≠ y ∧
      ∀ i, (y i : ℤ) - (x i : ℤ) = halfExp_rxn3.netChange i := by
  have hsum : ∑ i, (x i : ℕ) = N := by
    simpa [CTMC.DensityDepCTMC.InSimplex, CTMC.DensityDepCTMC.totalCount] using hx
  have hsum3 : (x 0 : ℤ) + (x 1 : ℤ) + (x 2 : ℤ) = N := by
    have := hsum
    simp only [Fin.sum_univ_three] at this
    omega
  let y : Fin 3 → Fin (N + 1) := fun i =>
    ⟨Int.toNat ((x i : ℤ) + halfExp_rxn3.netChange i), by
      have hbd : 0 ≤ (x i : ℤ) + halfExp_rxn3.netChange i ∧
          (x i : ℤ) + halfExp_rxn3.netChange i ≤ N := by
        fin_cases i <;> simp [halfExp_rxn3, PPReaction.netChange] <;> omega
      exact Nat.lt_succ_of_le (Int.toNat_le.mpr hbd.2)⟩
  have hy : ∀ i, (y i : ℤ) - (x i : ℤ) = halfExp_rxn3.netChange i := by
    intro i
    have hnn : 0 ≤ (x i : ℤ) + halfExp_rxn3.netChange i := by
      fin_cases i <;> simp [halfExp_rxn3, PPReaction.netChange] <;> omega
    change (Int.toNat ((x i : ℤ) + halfExp_rxn3.netChange i) : ℤ) -
      (x i : ℤ) = halfExp_rxn3.netChange i
    rw [Int.toNat_of_nonneg hnn]
    ring
  refine ⟨y, ?_, hy⟩
  intro hxy
  have hdiff := hy (1 : Fin 3)
  rw [← hxy] at hdiff
  simp [halfExp_rxn3, PPReaction.netChange] at hdiff

private lemma halfExpPP_E_zero_of_absorbingOnSimplex {N : ℕ} (hN : 0 < N)
    (x : Fin 3 → Fin (N + 1))
    (hx : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x)
    (hzero :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.exitRate x = 0) :
    (x (1 : Fin 3) : ℕ) = 0 := by
  let M := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  by_contra hEne
  have hEpos : 0 < (x (1 : Fin 3) : ℕ) := Nat.pos_of_ne_zero hEne
  obtain ⟨y, hxy, hmatch⟩ := halfExpPP_exists_rxn3_target_of_E_pos hN x hx hEpos
  have hrate_pos :
      0 < halfExpPP.toRateSpec.rate halfExp_rxn3.netChange (M.scaledState x) :=
    halfExpPP_rate_rxn3Jump_pos_of_E_pos hN x hEpos
  have hℓ_mem : halfExp_rxn3.netChange ∈ halfExpPP.toRateSpec.jumps := by
    simp [PopProtocol.toRateSpec, halfExpPP]
  have hℓ_filter : halfExp_rxn3.netChange ∈ halfExpPP.toRateSpec.jumps.filter
      (fun ℓ => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i) := by
    exact Finset.mem_filter.mpr ⟨hℓ_mem, hmatch⟩
  have hscaled_nonneg : ∀ i, 0 ≤ M.scaledState x i := by
    intro i
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hoff_pos : 0 < M.offDiagRate x y := by
    rw [CTMC.DensityDepCTMC.offDiagRate, if_neg hxy]
    refine Finset.sum_pos' ?nonneg ?pos
    · intro ℓ hℓ
      exact mul_nonneg (Nat.cast_nonneg _)
        (M.rateSpec.rate_nonneg ℓ (Finset.mem_filter.mp hℓ).1
          (M.scaledState x) hscaled_nonneg)
    · refine ⟨halfExp_rxn3.netChange, hℓ_filter, ?_⟩
      exact mul_pos (Nat.cast_pos.mpr hN) hrate_pos
  have hnot := M.not_absorbing_of_offDiagRate_pos hxy hoff_pos
  exact hnot hzero

theorem halfExpPP_driftZeroAtAbsorbingOnSimplex (N : ℕ) (hN : 0 < N) :
    (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).DriftZeroAtAbsorbingOnSimplex := by
  intro x hx hzero
  let M := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  have hEzero : (x (1 : Fin 3) : ℕ) = 0 :=
    halfExpPP_E_zero_of_absorbingOnSimplex hN x hx hzero
  change halfExpPP.toRateSpec.drift (M.scaledState x) = 0
  rw [halfExpPP_drift_eq]
  ext i
  fin_cases i <;> simp [halfExpFieldPP, CTMC.DensityDepCTMC.scaledState, hEzero]

/-! ## Frozen DensityProcess for ½e⁻¹

Construct the DensityProcess without NoAbsorbing, using the frozen
state readout from DensityDependentAbsorbing.lean. -/

noncomputable def halfExpPP_frozenDensityProcess (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1)) (hinit : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x₀) :
    Kurtz.DensityProcess 3 halfExpPP.toRateSpec N
      ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordMeasure x₀) :=
  (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toFrozenDensityProcess x₀
    (halfExpPP_driftZeroAtAbsorbingOnSimplex N hN)
    (halfExpPP_conservativeJumps N hN)
    hinit

private lemma halfExpPP_jump_coord_sq_sum_le_two_norm_sq
    {ℓ : Fin 3 → ℤ} (hℓ : ℓ ∈ halfExpPP.toRateSpec.jumps)
    (N : ℕ) (hN : 0 < N) :
    (∑ i : Fin 3, ((ℓ i : ℝ) / (N : ℝ)) ^ 2) ≤
      2 * ‖(fun i : Fin 3 => (ℓ i : ℝ) / (N : ℝ))‖ ^ 2 := by
  classical
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hjumps :
      ℓ = halfExp_rxn1.netChange ∨ ℓ = halfExp_rxn2.netChange ∨
        ℓ = halfExp_rxn3.netChange ∨ ℓ = halfExp_rxn4.netChange := by
    simpa [PopProtocol.toRateSpec, halfExpPP] using hℓ
  rcases hjumps with rfl | rfl | rfl | rfl
  · let v : Fin 3 → ℝ :=
      fun i => ((halfExp_rxn1.netChange i : ℤ) : ℝ) / (N : ℝ)
    have hcoord : (1 : ℝ) / (N : ℝ) ≤ ‖v‖ := by
      have h := norm_le_pi_norm v (0 : Fin 3)
      have h0 : ‖v (0 : Fin 3)‖ = (1 : ℝ) / (N : ℝ) := by
        simp [v, halfExp_rxn1, PPReaction.netChange]
      simpa [h0] using h
    have hcoord_sq : ((1 : ℝ) / (N : ℝ)) ^ 2 ≤ ‖v‖ ^ 2 := by
      exact sq_le_sq.mpr (by
        rw [abs_of_nonneg (div_nonneg zero_le_one (le_of_lt hNpos)),
          abs_of_nonneg (norm_nonneg v)]
        exact hcoord)
    have hsum :
        (∑ i : Fin 3, (((halfExp_rxn1.netChange i : ℤ) : ℝ) / (N : ℝ)) ^ 2) =
          2 / (N : ℝ) ^ 2 := by
      simp [Fin.sum_univ_three, halfExp_rxn1, PPReaction.netChange]
      field_simp [hNne]
      ring
    rw [hsum]
    change 2 / (N : ℝ) ^ 2 ≤ 2 * ‖v‖ ^ 2
    calc
      2 / (N : ℝ) ^ 2 = 2 * ((1 : ℝ) / (N : ℝ)) ^ 2 := by
        field_simp [hNne]
      _ ≤ 2 * ‖v‖ ^ 2 := by gcongr
  · let v : Fin 3 → ℝ :=
      fun i => ((halfExp_rxn2.netChange i : ℤ) : ℝ) / (N : ℝ)
    have hcoord : (2 : ℝ) / (N : ℝ) ≤ ‖v‖ := by
      have h := norm_le_pi_norm v (2 : Fin 3)
      have h2 : ‖v (2 : Fin 3)‖ = (2 : ℝ) / (N : ℝ) := by
        simp (config := { decide := true }) [v, halfExp_rxn2, PPReaction.netChange]
        norm_num
      simpa [h2] using h
    have hcoord_sq : ((2 : ℝ) / (N : ℝ)) ^ 2 ≤ ‖v‖ ^ 2 := by
      exact sq_le_sq.mpr (by
        rw [abs_of_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hNpos)),
          abs_of_nonneg (norm_nonneg v)]
        exact hcoord)
    have hsum :
        (∑ i : Fin 3, (((halfExp_rxn2.netChange i : ℤ) : ℝ) / (N : ℝ)) ^ 2) =
          6 / (N : ℝ) ^ 2 := by
      simp [Fin.sum_univ_three, halfExp_rxn2, PPReaction.netChange]
      field_simp [hNne]
      ring
    rw [hsum]
    change 6 / (N : ℝ) ^ 2 ≤ 2 * ‖v‖ ^ 2
    calc
      6 / (N : ℝ) ^ 2 ≤ 8 / (N : ℝ) ^ 2 := by
        exact div_le_div_of_nonneg_right (by norm_num : (6 : ℝ) ≤ 8)
          (sq_nonneg (N : ℝ))
      _ = 2 * ((2 : ℝ) / (N : ℝ)) ^ 2 := by
        field_simp [hNne]
        ring
      _ ≤ 2 * ‖v‖ ^ 2 := by gcongr
  · let v : Fin 3 → ℝ :=
      fun i => ((halfExp_rxn3.netChange i : ℤ) : ℝ) / (N : ℝ)
    have hcoord : (1 : ℝ) / (N : ℝ) ≤ ‖v‖ := by
      have h := norm_le_pi_norm v (1 : Fin 3)
      have h1 : ‖v (1 : Fin 3)‖ = (1 : ℝ) / (N : ℝ) := by
        simp [v, halfExp_rxn3, PPReaction.netChange,
          abs_of_neg (neg_lt_zero.mpr hNpos)]
      simpa [h1] using h
    have hcoord_sq : ((1 : ℝ) / (N : ℝ)) ^ 2 ≤ ‖v‖ ^ 2 := by
      exact sq_le_sq.mpr (by
        rw [abs_of_nonneg (div_nonneg zero_le_one (le_of_lt hNpos)),
          abs_of_nonneg (norm_nonneg v)]
        exact hcoord)
    have hsum :
        (∑ i : Fin 3, (((halfExp_rxn3.netChange i : ℤ) : ℝ) / (N : ℝ)) ^ 2) =
          2 / (N : ℝ) ^ 2 := by
      simp [Fin.sum_univ_three, halfExp_rxn3, PPReaction.netChange]
      field_simp [hNne]
      ring
    rw [hsum]
    change 2 / (N : ℝ) ^ 2 ≤ 2 * ‖v‖ ^ 2
    calc
      2 / (N : ℝ) ^ 2 = 2 * ((1 : ℝ) / (N : ℝ)) ^ 2 := by
        field_simp [hNne]
      _ ≤ 2 * ‖v‖ ^ 2 := by gcongr
  · let v : Fin 3 → ℝ :=
      fun i => ((halfExp_rxn4.netChange i : ℤ) : ℝ) / (N : ℝ)
    have hcoord : (1 : ℝ) / (N : ℝ) ≤ ‖v‖ := by
      have h := norm_le_pi_norm v (1 : Fin 3)
      have h1 : ‖v (1 : Fin 3)‖ = (1 : ℝ) / (N : ℝ) := by
        simp [v, halfExp_rxn4, PPReaction.netChange,
          abs_of_neg (neg_lt_zero.mpr hNpos)]
      simpa [h1] using h
    have hcoord_sq : ((1 : ℝ) / (N : ℝ)) ^ 2 ≤ ‖v‖ ^ 2 := by
      exact sq_le_sq.mpr (by
        rw [abs_of_nonneg (div_nonneg zero_le_one (le_of_lt hNpos)),
          abs_of_nonneg (norm_nonneg v)]
        exact hcoord)
    have hsum :
        (∑ i : Fin 3, (((halfExp_rxn4.netChange i : ℤ) : ℝ) / (N : ℝ)) ^ 2) =
          2 / (N : ℝ) ^ 2 := by
      simp [Fin.sum_univ_three, halfExp_rxn4, PPReaction.netChange]
      field_simp [hNne]
      ring
    rw [hsum]
    change 2 / (N : ℝ) ^ 2 ≤ 2 * ‖v‖ ^ 2
    calc
      2 / (N : ℝ) ^ 2 = 2 * ((1 : ℝ) / (N : ℝ)) ^ 2 := by
        field_simp [hNne]
      _ ≤ 2 * ‖v‖ ^ 2 := by gcongr

private lemma halfExpPP_transition_coord_sq_sum_le_two_norm_sq
    (N : ℕ) (hN : 0 < N)
    (x y : Fin 3 → Fin (N + 1))
    (hpos :
      0 < (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).offDiagRate x y) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    (∑ i : Fin 3, ((M.scaledState y - M.scaledState x) i) ^ 2) ≤
      2 * ‖M.scaledState y - M.scaledState x‖ ^ 2 := by
  intro M
  obtain ⟨ℓ, hℓ, hmatch⟩ := M.exists_jump_of_offDiagRate_pos hpos
  have hscaled := M.scaledState_sub_eq_of_jump hmatch
  rw [hscaled]
  simpa [M] using halfExpPP_jump_coord_sq_sum_le_two_norm_sq hℓ N hN

private lemma halfExpPP_sum_instantCoordQVRate_le_two_instantQVRate
    (N : ℕ) (hN : 0 < N) (x : Fin 3 → Fin (N + 1)) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    (∑ i : Fin 3, M.instantCoordQVRate x i) ≤ 2 * M.instantQVRate x := by
  intro M
  simp only [CTMC.DensityDepCTMC.instantCoordQVRate, CTMC.DensityDepCTMC.instantQVRate]
  rw [Finset.sum_comm]
  calc
    (∑ y : Fin 3 → Fin (M.N + 1),
        ∑ i : Fin 3,
          M.offDiagRate x y * ((M.scaledState y - M.scaledState x) i) ^ 2)
        = ∑ y : Fin 3 → Fin (M.N + 1),
            M.offDiagRate x y *
              (∑ i : Fin 3, ((M.scaledState y - M.scaledState x) i) ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro y _hy
          rw [Finset.mul_sum]
    _ ≤ ∑ y : Fin 3 → Fin (M.N + 1),
          M.offDiagRate x y * (2 * ‖M.scaledState y - M.scaledState x‖ ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro y _hy
          by_cases hzero : M.offDiagRate x y = 0
          · simp [hzero]
          · have hpos : 0 < M.offDiagRate x y :=
              lt_of_le_of_ne (M.offDiagRate_nonneg x y) (Ne.symm hzero)
            exact mul_le_mul_of_nonneg_left
              (by
                simpa [M] using
                  halfExpPP_transition_coord_sq_sum_le_two_norm_sq N hN x y hpos)
              (M.offDiagRate_nonneg x y)
    _ = 2 * ∑ y : Fin 3 → Fin (M.N + 1),
          M.offDiagRate x y * ‖M.scaledState y - M.scaledState x‖ ^ 2 := by
          calc
            (∑ y : Fin 3 → Fin (M.N + 1),
                M.offDiagRate x y * (2 * ‖M.scaledState y - M.scaledState x‖ ^ 2))
                = ∑ y : Fin 3 → Fin (M.N + 1),
                    2 * (M.offDiagRate x y *
                      ‖M.scaledState y - M.scaledState x‖ ^ 2) := by
                    refine Finset.sum_congr rfl ?_
                    intro y _hy
                    ring
            _ = 2 * ∑ y : Fin 3 → Fin (M.N + 1),
                  M.offDiagRate x y *
                    ‖M.scaledState y - M.scaledState x‖ ^ 2 := by
                    rw [Finset.mul_sum]

private def halfExpPP_active {N : ℕ} (x : Fin 3 → Fin (N + 1)) : ℕ :=
  (x (0 : Fin 3) : ℕ) + (x (1 : Fin 3) : ℕ)

private lemma halfExpPP_active_lt_of_offDiagRate_pos
    (N : ℕ) (hN : 0 < N)
    {x y : Fin 3 → Fin (N + 1)}
    (hpos :
      0 < (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).offDiagRate x y) :
    halfExpPP_active y < halfExpPP_active x := by
  let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  obtain ⟨ℓ, hℓ, hmatch⟩ := M.exists_jump_of_offDiagRate_pos hpos
  have hjumps :
      ℓ = halfExp_rxn1.netChange ∨ ℓ = halfExp_rxn2.netChange ∨
        ℓ = halfExp_rxn3.netChange ∨ ℓ = halfExp_rxn4.netChange := by
    simpa [M, PopProtocol.toRateSpec, halfExpPP] using hℓ
  rcases hjumps with hℓeq | hℓeq | hℓeq | hℓeq
  · have h0 := hmatch (0 : Fin 3)
    have h1 := hmatch (1 : Fin 3)
    rw [hℓeq] at h0 h1
    simp [halfExpPP_active, halfExp_rxn1, PPReaction.netChange] at h0 h1 ⊢
    omega
  · have h0 := hmatch (0 : Fin 3)
    have h1 := hmatch (1 : Fin 3)
    rw [hℓeq] at h0 h1
    simp [halfExpPP_active, halfExp_rxn2, PPReaction.netChange] at h0 h1 ⊢
    omega
  · have h0 := hmatch (0 : Fin 3)
    have h1 := hmatch (1 : Fin 3)
    rw [hℓeq] at h0 h1
    simp [halfExpPP_active, halfExp_rxn3, PPReaction.netChange] at h0 h1 ⊢
    omega
  · have h0 := hmatch (0 : Fin 3)
    have h1 := hmatch (1 : Fin 3)
    rw [hℓeq] at h0 h1
    simp [halfExpPP_active, halfExp_rxn4, PPReaction.netChange] at h0 h1 ⊢
    omega

private lemma halfExpPP_absorbing_of_E_zero {N : ℕ} (hN : 0 < N)
    (x : Fin 3 → Fin (N + 1))
    (hE : (x (1 : Fin 3) : ℕ) = 0) :
    (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing x := by
  let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  change M.exitRateAt x = 0
  rw [← M.sum_offDiagRate_eq_exitRateAt x]
  refine Finset.sum_eq_zero fun y _hy => ?_
  by_cases hxy : x = y
  · simp [CTMC.DensityDepCTMC.offDiagRate, hxy]
  · rw [CTMC.DensityDepCTMC.offDiagRate, if_neg hxy]
    refine Finset.sum_eq_zero fun ℓ hℓ => ?_
    have hℓ_mem : ℓ ∈ M.rateSpec.jumps := (Finset.mem_filter.mp hℓ).1
    have hjumps :
        ℓ = halfExp_rxn1.netChange ∨ ℓ = halfExp_rxn2.netChange ∨
          ℓ = halfExp_rxn3.netChange ∨ ℓ = halfExp_rxn4.netChange := by
      simpa [M, PopProtocol.toRateSpec, halfExpPP] using hℓ_mem
    rcases hjumps with hℓeq | hℓeq | hℓeq | hℓeq <;>
      rw [hℓeq] <;>
      (have hEreal : ((x (1 : Fin 3) : ℝ) / (N : ℝ)) = 0 := by
        simp [hE] <;>
        field_simp [ne_of_gt (Nat.cast_pos.mpr hN : (0 : ℝ) < N)]
       apply mul_eq_zero_of_right
       dsimp [M, PopProtocol.toRateSpec]
       refine Finset.sum_eq_zero fun r hr => ?_
       have hr_mem : r ∈ halfExpPP.reactions := (Finset.mem_filter.mp hr).1
       have hcases :
           r = halfExp_rxn1 ∨ r = halfExp_rxn2 ∨
             r = halfExp_rxn3 ∨ r = halfExp_rxn4 := by
         simpa [halfExpPP] using hr_mem
       rcases hcases with rfl | rfl | rfl | rfl <;>
         simp [halfExp_rxn1, halfExp_rxn2, halfExp_rxn3, halfExp_rxn4,
           PPReaction.massActionRate, hEreal])

private lemma halfExpPP_active_le_N_of_inSimplex {N : ℕ} (hN : 0 < N)
    {x : Fin 3 → Fin (N + 1)}
    (hx : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x) :
    halfExpPP_active x ≤ N := by
  have hsum : (x (0 : Fin 3) : ℕ) + (x (1 : Fin 3) : ℕ) +
      (x (2 : Fin 3) : ℕ) = N := by
    simpa [CTMC.DensityDepCTMC.InSimplex, CTMC.DensityDepCTMC.totalCount,
      Fin.sum_univ_three] using hx
  simp [halfExpPP_active]
  omega

private lemma halfExpPP_stateSeq_absorbing_at_N_of_guarded
    {N : ℕ} (hN : 0 < N)
    (seq : ℕ → Fin 3 → Fin (N + 1))
    (hsimplex :
      ∀ n, (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex (seq n))
    (hrate :
      ∀ n,
        ¬(CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
            (seq n) →
          0 < (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).offDiagRate
            (seq n) (seq (n + 1)))
    (hstay :
      ∀ n,
        (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
            (seq n) →
          seq (n + 1) = seq n) :
    (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
      (seq N) := by
  let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  by_contra hN_nonabs
  have hstay_from :
      ∀ k m, k ≤ m → M.toQMatrix.IsAbsorbing (seq k) → seq m = seq k := by
    intro k m hkm habs
    induction hkm with
    | refl => rfl
    | @step m hkm ih =>
        have habs_m : M.toQMatrix.IsAbsorbing (seq m) := by
          simpa [ih] using habs
        calc
          seq (m + 1) = seq m := hstay m habs_m
          _ = seq k := ih
  have hnonabs_le : ∀ k, k ≤ N → ¬M.toQMatrix.IsAbsorbing (seq k) := by
    intro k hk habs
    have hsame : seq N = seq k := hstay_from k N hk habs
    exact hN_nonabs (by simpa [hsame] using habs)
  have hactive_bound :
      ∀ n, n ≤ N → halfExpPP_active (seq n) + n ≤ halfExpPP_active (seq 0) := by
    intro n
    induction n with
    | zero =>
        intro _hn
        simp
    | succ n ih =>
        intro hn_succ
        have hn : n ≤ N := Nat.le_of_succ_le hn_succ
        have hdec : halfExpPP_active (seq (n + 1)) < halfExpPP_active (seq n) := by
          exact halfExpPP_active_lt_of_offDiagRate_pos N hN
            (by simpa [M] using hrate n (hnonabs_le n hn))
        have hih := ih hn
        omega
  have hactive0_le : halfExpPP_active (seq 0) ≤ N := by
    exact halfExpPP_active_le_N_of_inSimplex hN (by simpa [M] using hsimplex 0)
  have hactiveN_zero : halfExpPP_active (seq N) = 0 := by
    have hbound := hactive_bound N le_rfl
    omega
  have hE_ne_zero : (seq N (1 : Fin 3) : ℕ) ≠ 0 := by
    intro hE
    exact hN_nonabs (by
      simpa [M] using halfExpPP_absorbing_of_E_zero hN (seq N) hE)
  have hE_pos : 0 < (seq N (1 : Fin 3) : ℕ) := Nat.pos_of_ne_zero hE_ne_zero
  have hactiveN_pos : 0 < halfExpPP_active (seq N) := by
    change 0 < (seq N (0 : Fin 3) : ℕ) + (seq N (1 : Fin 3) : ℕ)
    exact Nat.add_pos_right _ hE_pos
  omega

private theorem halfExpPP_canonical_stateSeq_absorbing_at_N_ae
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1))
    (hinit : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x₀) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      M.toQMatrix.IsAbsorbing ((M.canonicalPathMap records).stateSeq N) := by
  let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  filter_upwards
    [M.canonicalPathMap_stateSeq_inSimplex_ae_of_conservative x₀
      (by simpa [M] using halfExpPP_conservativeJumps N hN)
      (by simpa [M] using hinit),
     M.toQMatrix.canonicalRecordMeasure_all_next_rate_pos_ae_of_nonabsorbing x₀,
     M.toQMatrix.canonicalRecordMeasure_all_next_state_eq_current_ae_of_absorbing x₀]
    with records hsimplex hrate hstay
  refine halfExpPP_stateSeq_absorbing_at_N_of_guarded hN
    (fun n => (M.canonicalPathMap records).stateSeq n)
    (by simpa [M] using hsimplex) ?_ ?_
  · intro n hnonabs
    let curr : Fin 3 → Fin (N + 1) := (M.canonicalPathMap records).stateSeq n
    let next : Fin 3 → Fin (N + 1) := (M.canonicalPathMap records).stateSeq (n + 1)
    have hcur :
        CTMC.QMatrix.currentStateFromHistory
            (S := Fin 3 → Fin (N + 1)) n (Preorder.frestrictLe n records) =
          curr := by
      simp [curr, M, CTMC.DensityDepCTMC.canonicalPathMap,
        CTMC.QMatrix.currentStateFromHistory_frestrictLe]
    have hq : 0 < M.toQMatrix.rate curr next := by
      have hraw := hrate n (by simpa [hcur, curr, M] using hnonabs)
      simpa [curr, next, M, CTMC.DensityDepCTMC.canonicalPathMap, hcur,
        CTMC.QMatrix.recordTrajectoryToPath_stateSeq] using hraw
    exact M.offDiagRate_pos_of_toQMatrix_rate_pos hq
  · intro n habs
    let curr : Fin 3 → Fin (N + 1) := (M.canonicalPathMap records).stateSeq n
    have hcur :
        CTMC.QMatrix.currentStateFromHistory
            (S := Fin 3 → Fin (N + 1)) n (Preorder.frestrictLe n records) =
          curr := by
      simp [curr, M, CTMC.DensityDepCTMC.canonicalPathMap,
        CTMC.QMatrix.currentStateFromHistory_frestrictLe]
    have hnext_record :
        (records (n + 1)).2 =
          CTMC.QMatrix.currentStateFromHistory
            (S := Fin 3 → Fin (N + 1)) n (Preorder.frestrictLe n records) :=
      hstay n (by simpa [hcur, curr, M] using habs)
    simpa [curr, M, CTMC.DensityDepCTMC.canonicalPathMap, hcur,
      CTMC.QMatrix.recordTrajectoryToPath_stateSeq] using hnext_record

private theorem halfExpPP_canonical_absorbed_from_N_ae
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1))
    (hinit : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x₀) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      (∀ m, N ≤ m →
        (M.canonicalPathMap records).stateSeq m =
          (M.canonicalPathMap records).stateSeq N) ∧
      (∀ m, N ≤ m → (records (m + 1)).1 = 0) := by
  let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  filter_upwards
    [halfExpPP_canonical_stateSeq_absorbing_at_N_ae N hN x₀ hinit,
     M.toQMatrix.canonicalRecordMeasure_all_next_state_eq_current_ae_of_absorbing x₀,
     M.toQMatrix.canonicalRecordMeasure_all_next_holdingTime_eq_zero_ae_of_absorbing x₀]
    with records habsN hstay hhold
  have hstate_from_N :
      ∀ r : ℕ,
        (M.canonicalPathMap records).stateSeq (N + r) =
          (M.canonicalPathMap records).stateSeq N := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
        have habs_r :
            M.toQMatrix.IsAbsorbing
              ((M.canonicalPathMap records).stateSeq (N + r)) := by
          simpa [ih] using habsN
        have hcur :
            CTMC.QMatrix.currentStateFromHistory
                (S := Fin 3 → Fin (N + 1)) (N + r)
                (Preorder.frestrictLe (N + r) records) =
              (M.canonicalPathMap records).stateSeq (N + r) := by
          simp [M, CTMC.DensityDepCTMC.canonicalPathMap,
            CTMC.QMatrix.currentStateFromHistory_frestrictLe]
        have hnext_record :
            (records (N + r + 1)).2 =
              CTMC.QMatrix.currentStateFromHistory
                (S := Fin 3 → Fin (N + 1)) (N + r)
                (Preorder.frestrictLe (N + r) records) :=
          hstay (N + r) (by simpa [hcur] using habs_r)
        have hsucc :
            (M.canonicalPathMap records).stateSeq (N + r + 1) =
              (M.canonicalPathMap records).stateSeq (N + r) := by
          simpa [M, CTMC.DensityDepCTMC.canonicalPathMap, hcur,
            CTMC.QMatrix.recordTrajectoryToPath_stateSeq] using hnext_record
        simpa [Nat.add_assoc] using hsucc.trans ih
  constructor
  · intro m hm
    have hdecomp : N + (m - N) = m := Nat.add_sub_of_le hm
    simpa [hdecomp] using hstate_from_N (m - N)
  · intro m hm
    have hm_state :
        (M.canonicalPathMap records).stateSeq m =
          (M.canonicalPathMap records).stateSeq N := by
      have hdecomp : N + (m - N) = m := Nat.add_sub_of_le hm
      simpa [hdecomp] using hstate_from_N (m - N)
    have habs_m :
        M.toQMatrix.IsAbsorbing ((M.canonicalPathMap records).stateSeq m) := by
      simpa [hm_state] using habsN
    have hcur :
        CTMC.QMatrix.currentStateFromHistory
            (S := Fin 3 → Fin (N + 1)) m (Preorder.frestrictLe m records) =
          (M.canonicalPathMap records).stateSeq m := by
      simp [M, CTMC.DensityDepCTMC.canonicalPathMap,
        CTMC.QMatrix.currentStateFromHistory_frestrictLe]
    exact hhold m (by simpa [hcur] using habs_m)

private noncomputable def halfExpPP_firstAbsIdx
    (N : ℕ) (hN : 0 < N)
    (records :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordΩ)
    (hAbsN :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
        (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap records).stateSeq N)) :
    ℕ := by
  classical
  exact Nat.find
    (p := fun n =>
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
        (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap records).stateSeq n))
    ⟨N, hAbsN⟩

private theorem halfExpPP_firstAbsIdx_spec
    (N : ℕ) (hN : 0 < N)
    (records :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordΩ)
    (hAbsN :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
        (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap records).stateSeq N)) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    M.toQMatrix.IsAbsorbing
      ((M.canonicalPathMap records).stateSeq
        (halfExpPP_firstAbsIdx N hN records hAbsN)) := by
  classical
  let P : ℕ → Prop := fun n =>
    (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
      (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap records).stateSeq n)
  let hP : ∃ n, P n := ⟨N, hAbsN⟩
  simpa [halfExpPP_firstAbsIdx, P, hP] using Nat.find_spec hP

private theorem halfExpPP_firstAbsIdx_le_N
    (N : ℕ) (hN : 0 < N)
    (records :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordΩ)
    (hAbsN :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
        (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap records).stateSeq N)) :
    halfExpPP_firstAbsIdx N hN records hAbsN ≤ N := by
  classical
  let P : ℕ → Prop := fun n =>
    (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
      (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap records).stateSeq n)
  let hP : ∃ n, P n := ⟨N, hAbsN⟩
  simpa [halfExpPP_firstAbsIdx, P, hP] using Nat.find_min' hP hAbsN

private theorem halfExpPP_not_absorbing_before_firstAbsIdx
    (N : ℕ) (hN : 0 < N)
    (records :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordΩ)
    (hAbsN :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
        (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap records).stateSeq N))
    {j : ℕ} (hj : j < halfExpPP_firstAbsIdx N hN records hAbsN) :
    ¬(CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
      (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap records).stateSeq j) := by
  classical
  let P : ℕ → Prop := fun n =>
    (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
      (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap records).stateSeq n)
  let hP : ∃ n, P n := ⟨N, hAbsN⟩
  have hj' : j < Nat.find hP := by
    simpa [halfExpPP_firstAbsIdx, P, hP] using hj
  simpa [P] using Nat.find_min hP hj'

private theorem halfExpPP_absorbed_from_firstAbsIdx
    (N : ℕ) (hN : 0 < N)
    (records :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordΩ)
    (hAbsN :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
        (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap records).stateSeq N))
    (hstayAbs : ∀ n,
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
          (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap records).stateSeq n) →
        ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap records).stateSeq (n + 1) =
          ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap records).stateSeq n)
    (hzeroAbs : ∀ n,
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
          (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap records).stateSeq n) →
        (records (n + 1)).1 = 0) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    let a := halfExpPP_firstAbsIdx N hN records hAbsN
    (∀ m, a ≤ m → (M.canonicalPathMap records).stateSeq m =
        (M.canonicalPathMap records).stateSeq a) ∧
      (∀ m, a ≤ m → (records (m + 1)).1 = 0) := by
  classical
  let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  let a := halfExpPP_firstAbsIdx N hN records hAbsN
  have haAbs : M.toQMatrix.IsAbsorbing ((M.canonicalPathMap records).stateSeq a) := by
    simpa [M, a] using halfExpPP_firstAbsIdx_spec N hN records hAbsN
  have hstate : ∀ m, a ≤ m →
      (M.canonicalPathMap records).stateSeq m =
        (M.canonicalPathMap records).stateSeq a := by
    intro m hm
    induction hm with
    | refl => rfl
    | @step m _ ih =>
        have hmAbs : M.toQMatrix.IsAbsorbing ((M.canonicalPathMap records).stateSeq m) := by
          simpa [ih] using haAbs
        calc
          (M.canonicalPathMap records).stateSeq (m + 1)
              = (M.canonicalPathMap records).stateSeq m := by
                  simpa [M] using hstayAbs m hmAbs
          _ = (M.canonicalPathMap records).stateSeq a := ih
  refine ⟨hstate, ?_⟩
  intro m hm
  have hmAbs : M.toQMatrix.IsAbsorbing ((M.canonicalPathMap records).stateSeq m) := by
    simpa [hstate m hm] using haAbs
  simpa [M] using hzeroAbs m hmAbs

private theorem halfExpPP_clockTail_times_eq_sum_range
    (M : CTMC.DensityDepCTMC d) (records : M.canonicalRecordΩ) (m : ℕ) :
    (M.canonicalPathMap records).times m =
      ∑ k ∈ Finset.range (m + 1), (records (k + 1)).1 := by
  simpa [CTMC.DensityDepCTMC.canonicalPathMap] using
    (CTMC.QMatrix.recordTrajectoryToPath_times
      (S := Fin d → Fin (M.N + 1)) records m)

private theorem halfExpPP_clockTail_sojournTime_eq_record
    (M : CTMC.DensityDepCTMC d) (records : M.canonicalRecordΩ) (k : ℕ) :
    (M.canonicalPathMap records).sojournTime k = (records (k + 1)).1 := by
  simpa [CTMC.DensityDepCTMC.canonicalPathMap] using
    (CTMC.QMatrix.recordTrajectoryToPath_sojournTime
      (S := Fin d → Fin (M.N + 1)) records k)

private theorem halfExpPP_clockTail_sojournStart_eq_sum_range
    (M : CTMC.DensityDepCTMC d) (records : M.canonicalRecordΩ) (a : ℕ) :
    (M.canonicalPathMap records).sojournStart a =
      ∑ k ∈ Finset.range a, (records (k + 1)).1 := by
  cases a with
  | zero =>
      simp [CTMC.CTMCPath.sojournStart]
  | succ a =>
      change (M.canonicalPathMap records).times a =
        ∑ k ∈ Finset.range (a + 1), (records (k + 1)).1
      exact halfExpPP_clockTail_times_eq_sum_range M records a

private theorem halfExpPP_clockTail_currentState_eq_stateSeq
    (M : CTMC.DensityDepCTMC d) (records : M.canonicalRecordΩ) (k : ℕ) :
    CTMC.QMatrix.currentStateFromHistory
        (S := Fin d → Fin (M.N + 1)) k (Preorder.frestrictLe k records) =
      (M.canonicalPathMap records).stateSeq k := by
  simpa [CTMC.DensityDepCTMC.canonicalPathMap] using
    (CTMC.QMatrix.currentStateFromHistory_frestrictLe
      (S := Fin d → Fin (M.N + 1)) records k)

private theorem halfExpPP_times_strict_prefix_before_firstAbsIdx
    (N : ℕ) (hN : 0 < N)
    (records :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordΩ)
    (hAbsN :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
        (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap records).stateSeq N))
    (hhold_pos :
      ∀ n,
        ¬ (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
            (CTMC.QMatrix.currentStateFromHistory
              (S := Fin 3 → Fin (N + 1)) n (Preorder.frestrictLe n records)) →
          0 < (records (n + 1)).1)
    {k : ℕ} (hk : k < halfExpPP_firstAbsIdx N hN records hAbsN) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    ∀ n < k, (M.canonicalPathMap records).times n <
      (M.canonicalPathMap records).times (n + 1) := by
  intro M n hn
  have hn1_lt :
      n + 1 < halfExpPP_firstAbsIdx N hN records hAbsN := by
    omega
  have hnonabs_state :
      ¬ M.toQMatrix.IsAbsorbing ((M.canonicalPathMap records).stateSeq (n + 1)) := by
    simpa [M] using
      halfExpPP_not_absorbing_before_firstAbsIdx N hN records hAbsN hn1_lt
  have hnonabs_cur :
      ¬ M.toQMatrix.IsAbsorbing
          (CTMC.QMatrix.currentStateFromHistory
            (S := Fin 3 → Fin (N + 1)) (n + 1)
            (Preorder.frestrictLe (n + 1) records)) := by
    rw [halfExpPP_clockTail_currentState_eq_stateSeq M records (n + 1)]
    exact hnonabs_state
  have hhold : 0 < (records (n + 2)).1 := by
    simpa [Nat.add_assoc] using hhold_pos (n + 1) hnonabs_cur
  have hsucc :
      (M.canonicalPathMap records).times (n + 1) =
        (M.canonicalPathMap records).times n + (records (n + 2)).1 := by
    simpa [M, CTMC.DensityDepCTMC.canonicalPathMap] using
      CTMC.QMatrix.recordTrajectoryToPath_times_succ
        (S := Fin 3 → Fin (N + 1)) records n
  rw [hsucc]
  linarith

private theorem halfExpPP_time_zero_pos_before_firstAbsIdx
    (N : ℕ) (hN : 0 < N)
    (records :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordΩ)
    (hAbsN :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
        (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap records).stateSeq N))
    (hhold_pos :
      ∀ n,
        ¬ (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
            (CTMC.QMatrix.currentStateFromHistory
              (S := Fin 3 → Fin (N + 1)) n (Preorder.frestrictLe n records)) →
          0 < (records (n + 1)).1)
    (ha_pos : 0 < halfExpPP_firstAbsIdx N hN records hAbsN) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    0 < (M.canonicalPathMap records).times 0 := by
  intro M
  have hnonabs_state :
      ¬ M.toQMatrix.IsAbsorbing ((M.canonicalPathMap records).stateSeq 0) := by
    simpa [M] using
      halfExpPP_not_absorbing_before_firstAbsIdx N hN records hAbsN ha_pos
  have hnonabs_cur :
      ¬ M.toQMatrix.IsAbsorbing
          (CTMC.QMatrix.currentStateFromHistory
            (S := Fin 3 → Fin (N + 1)) 0 (Preorder.frestrictLe 0 records)) := by
    rw [halfExpPP_clockTail_currentState_eq_stateSeq M records 0]
    exact hnonabs_state
  have hhold : 0 < (records 1).1 := hhold_pos 0 hnonabs_cur
  simpa [M, CTMC.DensityDepCTMC.canonicalPathMap] using
    (CTMC.QMatrix.recordTrajectoryToPath_times_zero
      (S := Fin 3 → Fin (N + 1)) records).symm ▸ hhold

private theorem halfExpPP_sum_range_succ_le_absorb_prefix_sum
    {f : ℕ → ℝ} {a m : ℕ}
    (hnonneg_before : ∀ k, k < a → 0 ≤ f k)
    (hzero_tail : ∀ k, a ≤ k → f k = 0) :
    (∑ k ∈ Finset.range (m + 1), f k) ≤
      ∑ k ∈ Finset.range a, f k := by
  classical
  have hsplit :
      (∑ k ∈ Finset.range (m + 1), f k) =
        ∑ k ∈ (Finset.range (m + 1)).filter (fun k => k < a), f k := by
    symm
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro k _hk
    by_cases hka : k < a
    · simp [hka]
    · have hak : a ≤ k := le_of_not_gt hka
      simp [hka, hzero_tail k hak]
  rw [hsplit]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by
      intro k hk
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2)
    (by
      intro k hk _hnot
      exact hnonneg_before k (Finset.mem_range.mp hk))

private theorem halfExpPP_time_le_firstAbsIdx_sojournStart_from_records
    (M : CTMC.DensityDepCTMC d) (records : M.canonicalRecordΩ) (a : ℕ)
    (hhold_nonneg_before : ∀ k, k < a → 0 ≤ (records (k + 1)).1)
    (hhold_zero_tail : ∀ k, a ≤ k → (records (k + 1)).1 = 0) :
    ∀ m, (M.canonicalPathMap records).times m ≤
      (M.canonicalPathMap records).sojournStart a := by
  intro m
  let f : ℕ → ℝ := fun k => (records (k + 1)).1
  have hsum_le :
      (∑ k ∈ Finset.range (m + 1), f k) ≤
        ∑ k ∈ Finset.range a, f k :=
    halfExpPP_sum_range_succ_le_absorb_prefix_sum
      (f := f) hhold_nonneg_before hhold_zero_tail
  calc
    (M.canonicalPathMap records).times m
        = ∑ k ∈ Finset.range (m + 1), f k := by
            simpa [f] using halfExpPP_clockTail_times_eq_sum_range M records m
    _ ≤ ∑ k ∈ Finset.range a, f k := hsum_le
    _ = (M.canonicalPathMap records).sojournStart a := by
            simpa [f] using
              (halfExpPP_clockTail_sojournStart_eq_sum_range M records a).symm

private theorem halfExpPP_time_le_firstAbsIdx_sojournStart
    (M : CTMC.DensityDepCTMC d) (records : M.canonicalRecordΩ) (a : ℕ)
    (hnot_abs_before : ∀ k, k < a →
      ¬ M.toQMatrix.IsAbsorbing ((M.canonicalPathMap records).stateSeq k))
    (hhold_pos : ∀ n,
      ¬ M.toQMatrix.IsAbsorbing
          (CTMC.QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) →
        0 < (records (n + 1)).1)
    (hhold_zero_tail : ∀ k, a ≤ k →
      (M.canonicalPathMap records).sojournTime k = 0) :
    ∀ m, (M.canonicalPathMap records).times m ≤
      (M.canonicalPathMap records).sojournStart a := by
  refine halfExpPP_time_le_firstAbsIdx_sojournStart_from_records
    M records a ?_ ?_
  · intro k hk
    have hcur_nonabs :
        ¬ M.toQMatrix.IsAbsorbing
          (CTMC.QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) k (Preorder.frestrictLe k records)) := by
      rw [halfExpPP_clockTail_currentState_eq_stateSeq M records k]
      exact hnot_abs_before k hk
    exact le_of_lt (hhold_pos k hcur_nonabs)
  · intro k hk
    have h := hhold_zero_tail k hk
    rwa [halfExpPP_clockTail_sojournTime_eq_record M records k] at h

private theorem halfExpPP_no_time_gt_of_firstAbsIdx_sojournStart_le
    (M : CTMC.DensityDepCTMC d) (records : M.canonicalRecordΩ) (a : ℕ)
    (hnot_abs_before : ∀ k, k < a →
      ¬ M.toQMatrix.IsAbsorbing ((M.canonicalPathMap records).stateSeq k))
    (hhold_pos : ∀ n,
      ¬ M.toQMatrix.IsAbsorbing
          (CTMC.QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) →
        0 < (records (n + 1)).1)
    (hhold_zero_tail : ∀ k, a ≤ k →
      (M.canonicalPathMap records).sojournTime k = 0)
    {t : ℝ} (ht : (M.canonicalPathMap records).sojournStart a ≤ t) :
    ∀ m, ¬ t < (M.canonicalPathMap records).times m := by
  intro m htm
  have hm := halfExpPP_time_le_firstAbsIdx_sojournStart
    M records a hnot_abs_before hhold_pos hhold_zero_tail m
  linarith

private theorem halfExpPP_frozenStateAt_eq_stateSeq_of_firstAbsIdx_tail
    (M : CTMC.DensityDepCTMC d) (records : M.canonicalRecordΩ) (a : ℕ)
    (hnot_abs_before : ∀ k, k < a →
      ¬ M.toQMatrix.IsAbsorbing ((M.canonicalPathMap records).stateSeq k))
    (hhold_pos : ∀ n,
      ¬ M.toQMatrix.IsAbsorbing
          (CTMC.QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) →
        0 < (records (n + 1)).1)
    (hstate_tail : ∀ m, a ≤ m →
      (M.canonicalPathMap records).stateSeq m =
        (M.canonicalPathMap records).stateSeq a)
    (hhold_zero_tail : ∀ k, a ≤ k →
      (M.canonicalPathMap records).sojournTime k = 0)
    (hnext_ne : ∀ n,
      ¬ M.toQMatrix.IsAbsorbing
          (CTMC.QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) →
        (records (n + 1)).2 ≠
          CTMC.QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records))
    {t : ℝ} (htail : (M.canonicalPathMap records).sojournStart a ≤ t) :
    (M.canonicalPathMap records).frozenStateAt t =
      (M.canonicalPathMap records).stateSeq a := by
  classical
  let path := M.canonicalPathMap records
  have hno : ∀ m, ¬ t < path.times m := by
    simpa [path] using
      halfExpPP_no_time_gt_of_firstAbsIdx_sojournStart_le
        M records a hnot_abs_before hhold_pos hhold_zero_tail htail
  have hstable : path.stateSeq a = path.stateSeq (a + 1) := by
    simpa [path] using (hstate_tail (a + 1) (Nat.le_succ a)).symm
  have hmin : ∀ k ∈ Finset.range a,
      path.stateSeq k ≠ path.stateSeq (k + 1) := by
    intro k hk hsame
    have hklt : k < a := Finset.mem_range.mp hk
    have hcur :
        CTMC.QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) k (Preorder.frestrictLe k records) =
          path.stateSeq k := by
      simpa [path] using halfExpPP_clockTail_currentState_eq_stateSeq M records k
    have hnonabs_cur :
        ¬ M.toQMatrix.IsAbsorbing
          (CTMC.QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) k (Preorder.frestrictLe k records)) := by
      rw [hcur]
      exact hnot_abs_before k hklt
    have hnext_state :
        path.stateSeq (k + 1) = (records (k + 1)).2 := by
      simpa [path, CTMC.DensityDepCTMC.canonicalPathMap,
        CTMC.QMatrix.recordTrajectoryToPath_stateSeq]
    have hrecord_eq :
        (records (k + 1)).2 =
          CTMC.QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) k (Preorder.frestrictLe k records) := by
      calc
        (records (k + 1)).2 = path.stateSeq (k + 1) := hnext_state.symm
        _ = path.stateSeq k := hsame.symm
        _ = CTMC.QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) k
            (Preorder.frestrictLe k records) := hcur.symm
    exact hnext_ne k hnonabs_cur hrecord_eq
  exact path.frozenStateAt_eq_stateSeq_of_first_stable t a hno hstable hmin

private theorem halfExpPP_frozenMartingalePart_tail_eq_start
    (M : CTMC.DensityDepCTMC d) (records : M.canonicalRecordΩ) (a : ℕ)
    (hnot_abs_before : ∀ k, k < a →
      ¬ M.toQMatrix.IsAbsorbing ((M.canonicalPathMap records).stateSeq k))
    (hhold_pos : ∀ n,
      ¬ M.toQMatrix.IsAbsorbing
          (CTMC.QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) →
        0 < (records (n + 1)).1)
    (hstate_tail : ∀ m, a ≤ m →
      (M.canonicalPathMap records).stateSeq m =
        (M.canonicalPathMap records).stateSeq a)
    (hhold_zero_tail : ∀ k, a ≤ k →
      (M.canonicalPathMap records).sojournTime k = 0)
    (hnext_ne : ∀ n,
      ¬ M.toQMatrix.IsAbsorbing
          (CTMC.QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) →
        (records (n + 1)).2 ≠
          CTMC.QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records))
    (hdrift_abs :
      M.rateSpec.drift (M.scaledState ((M.canonicalPathMap records).stateSeq a)) = 0)
    {s : ℝ} (htail : (M.canonicalPathMap records).sojournStart a ≤ s) :
    M.frozenMartingalePart M.canonicalPathMap s records =
      M.frozenMartingalePart M.canonicalPathMap
        ((M.canonicalPathMap records).sojournStart a) records := by
  classical
  let path := M.canonicalPathMap records
  have hstart_nonneg : 0 ≤ path.sojournStart a := by
    have hsum :
        0 ≤ ∑ k ∈ Finset.range a, (records (k + 1)).1 := by
      refine Finset.sum_nonneg ?_
      intro k hk
      have hklt : k < a := Finset.mem_range.mp hk
      have hcur_nonabs :
          ¬ M.toQMatrix.IsAbsorbing
            (CTMC.QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) k (Preorder.frestrictLe k records)) := by
        rw [halfExpPP_clockTail_currentState_eq_stateSeq M records k]
        exact hnot_abs_before k hklt
      exact le_of_lt (hhold_pos k hcur_nonabs)
    simpa [path] using
      (by
        simpa using
          (halfExpPP_clockTail_sojournStart_eq_sum_range M records a).symm ▸ hsum)
  have hs_nonneg : 0 ≤ s := le_trans hstart_nonneg htail
  have hstate_s :
      path.frozenStateAt s = path.stateSeq a :=
    halfExpPP_frozenStateAt_eq_stateSeq_of_firstAbsIdx_tail
      M records a hnot_abs_before hhold_pos hstate_tail hhold_zero_tail
      hnext_ne htail
  have hstate_start :
      path.frozenStateAt (path.sojournStart a) = path.stateSeq a :=
    halfExpPP_frozenStateAt_eq_stateSeq_of_firstAbsIdx_tail
      M records a hnot_abs_before hhold_pos hstate_tail hhold_zero_tail
      hnext_ne le_rfl
  have hdensity_s :
      M.frozenDensityProcess M.canonicalPathMap s records =
        M.scaledState (path.stateSeq a) := by
    ext i
    simp [CTMC.DensityDepCTMC.frozenDensityProcess,
      CTMC.DensityDepCTMC.scaledState, path, hstate_s]
  have hdensity_start :
      M.frozenDensityProcess M.canonicalPathMap (path.sojournStart a) records =
        M.scaledState (path.stateSeq a) := by
    ext i
    simp [CTMC.DensityDepCTMC.frozenDensityProcess,
      CTMC.DensityDepCTMC.scaledState, path, hstate_start]
  ext i
  let f : ℝ → ℝ := fun u =>
    (M.rateSpec.drift (M.frozenDensityProcess M.canonicalPathMap u records)) i
  have hsubset :
      Set.Icc (0 : ℝ) (path.sojournStart a) ⊆ Set.Icc (0 : ℝ) s := by
    intro u hu
    exact ⟨hu.1, le_trans hu.2 htail⟩
  have hzero_diff : ∀ u ∈ Set.Icc (0 : ℝ) s \ Set.Icc (0 : ℝ) (path.sojournStart a),
      f u = 0 := by
    intro u hu
    have htail_u : path.sojournStart a ≤ u := by
      have hu0 : 0 ≤ u := hu.1.1
      have hnot_small : ¬ (0 ≤ u ∧ u ≤ path.sojournStart a) := hu.2
      exact le_of_not_gt fun hlt =>
        hnot_small ⟨hu0, le_of_lt hlt⟩
    have hstate_u :
        path.frozenStateAt u = path.stateSeq a :=
      halfExpPP_frozenStateAt_eq_stateSeq_of_firstAbsIdx_tail
        M records a hnot_abs_before hhold_pos hstate_tail hhold_zero_tail
        hnext_ne htail_u
    have hdensity_u :
        M.frozenDensityProcess M.canonicalPathMap u records =
          M.scaledState (path.stateSeq a) := by
      ext j
      simp [CTMC.DensityDepCTMC.frozenDensityProcess,
        CTMC.DensityDepCTMC.scaledState, path, hstate_u]
    simpa [f, hdensity_u] using congr_fun hdrift_abs i
  have hintegral :
      (∫ u in Set.Icc (0 : ℝ) s, f u) =
        ∫ u in Set.Icc (0 : ℝ) (path.sojournStart a), f u := by
    exact MeasureTheory.setIntegral_eq_of_subset_of_forall_diff_eq_zero
      measurableSet_Icc hsubset hzero_diff
  simp only [CTMC.DensityDepCTMC.frozenMartingalePart, Pi.sub_apply]
  rw [hdensity_s, hdensity_start]
  change
      M.scaledState (path.stateSeq a) i -
          M.frozenInitialCondition M.canonicalPathMap records i -
        (∫ u in Set.Icc (0 : ℝ) s, f u) =
      M.scaledState (path.stateSeq a) i -
          M.frozenInitialCondition M.canonicalPathMap records i -
        (∫ u in Set.Icc (0 : ℝ) (path.sojournStart a), f u)
  rw [hintegral]

private theorem halfExpPP_exists_instantQVRate_bound_uniform :
    ∃ C > 0, ∀ (N : ℕ) (hN : 0 < N)
      (x : Fin 3 → Fin (N + 1)),
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).instantQVRate x ≤
        C / (N : ℝ) := by
  obtain ⟨B, hBpos, hB⟩ :=
    halfExpPP.toRateSpec.exists_rate_bound_on_ball 1 zero_lt_one
  refine ⟨B * (halfExpPP.toRateSpec.jumps.card : ℝ) *
      halfExpPP.toRateSpec.jumpNormBound ^ 2 + 1, by positivity, ?_⟩
  intro N hN x
  let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  let b := (M.rateSpec.jumpNormBound / (M.N : ℝ)) ^ 2
  let a : (Fin 3 → ℤ) → ℝ :=
    fun ℓ => (M.N : ℝ) * M.rateSpec.rate ℓ (M.scaledState x)
  have hNpos : 0 < (M.N : ℝ) := Nat.cast_pos.mpr M.hN
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    exact sq_nonneg _
  have ha_nonneg : ∀ ℓ ∈ M.rateSpec.jumps, 0 ≤ a ℓ := by
    intro ℓ hℓ
    dsimp [a]
    apply mul_nonneg (Nat.cast_nonneg _)
    exact M.rateSpec.rate_nonneg ℓ hℓ (M.scaledState x) fun i =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hsum_rate :
      (∑ ℓ ∈ M.rateSpec.jumps, M.rateSpec.rate ℓ (M.scaledState x)) ≤
        (M.rateSpec.jumps.card : ℝ) * B := by
    calc
      ∑ ℓ ∈ M.rateSpec.jumps, M.rateSpec.rate ℓ (M.scaledState x)
          ≤ ∑ _ℓ ∈ M.rateSpec.jumps, B := by
            apply Finset.sum_le_sum
            intro ℓ hℓ
            exact (le_abs_self _).trans
              (hB ℓ hℓ (M.scaledState x) (M.scaledState_norm_le x))
      _ = (M.rateSpec.jumps.card : ℝ) * B := by
            rw [Finset.sum_const, nsmul_eq_mul]
  have hmain :
      (∑ y : Fin 3 → Fin (M.N + 1),
        M.offDiagRate x y * ‖M.scaledState y - M.scaledState x‖ ^ 2) ≤
        (B * (M.rateSpec.jumps.card : ℝ) *
            M.rateSpec.jumpNormBound ^ 2 + 1) / (M.N : ℝ) := by
    calc
      ∑ y : Fin 3 → Fin (M.N + 1),
          M.offDiagRate x y * ‖M.scaledState y - M.scaledState x‖ ^ 2
          ≤ ∑ y : Fin 3 → Fin (M.N + 1),
              ∑ ℓ ∈ M.rateSpec.jumps.filter
                (fun ℓ : Fin 3 → ℤ => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i),
                  a ℓ * b := by
            exact Finset.sum_le_sum fun y _ =>
              (M.offDiagRate_mul_scaledState_sub_sq_le x y).trans_eq (by simp [a, b])
      _ = ∑ y : Fin 3 → Fin (M.N + 1),
              ∑ ℓ ∈ M.rateSpec.jumps,
                if (∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i) then a ℓ * b else 0 := by
            apply Finset.sum_congr rfl
            intro y _
            rw [Finset.sum_filter]
      _ = ∑ ℓ ∈ M.rateSpec.jumps,
              ∑ y : Fin 3 → Fin (M.N + 1),
                if (∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i) then a ℓ * b else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ ℓ ∈ M.rateSpec.jumps,
              ∑ y ∈ (Finset.univ : Finset (Fin 3 → Fin (M.N + 1))).filter
                (fun y : Fin 3 → Fin (M.N + 1) =>
                  ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i), a ℓ * b := by
            apply Finset.sum_congr rfl
            intro ℓ _
            rw [Finset.sum_filter]
      _ ≤ ∑ ℓ ∈ M.rateSpec.jumps, a ℓ * b := by
            apply Finset.sum_le_sum
            intro ℓ hℓ
            exact M.sum_matchingStates_const_le x ℓ
              (mul_nonneg (ha_nonneg ℓ hℓ) hb_nonneg)
      _ = ((M.N : ℝ) * ∑ ℓ ∈ M.rateSpec.jumps,
            M.rateSpec.rate ℓ (M.scaledState x)) * b := by
            simp [a, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      _ ≤ ((M.N : ℝ) * ((M.rateSpec.jumps.card : ℝ) * B)) * b := by
            gcongr
      _ = B * (M.rateSpec.jumps.card : ℝ) * M.rateSpec.jumpNormBound ^ 2 /
            (M.N : ℝ) := by
            dsimp [b]
            field_simp [ne_of_gt hNpos]
      _ ≤ (B * (M.rateSpec.jumps.card : ℝ) *
              M.rateSpec.jumpNormBound ^ 2 + 1) / (M.N : ℝ) := by
            gcongr
            linarith
  simpa [CTMC.DensityDepCTMC.instantQVRate, M, CTMC.DensityDepCTMC.mk] using hmain

private theorem measurable_canonicalFrozenInstantQVRate_setIntegral
    (M : CTMC.DensityDepCTMC d) (T : ℝ) :
    Measurable (fun records : M.canonicalRecordΩ =>
      ∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s)) := by
  have hjoint : MeasureTheory.StronglyMeasurable
      (fun p : M.canonicalRecordΩ × ℝ =>
        M.instantQVRate ((M.canonicalPathMap p.1).frozenStateAt p.2)) :=
    ((Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) => M.instantQVRate x)).comp
        (M.measurable_prod_canonicalPathMap_frozenStateAt.comp measurable_swap)).stronglyMeasurable
  exact (hjoint.integral_prod_right'
    (ν := MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 T))).measurable

private theorem measurable_canonicalFrozenInstantCoordQVRate_setIntegral
    (M : CTMC.DensityDepCTMC d) (i : Fin d) (T : ℝ) :
    Measurable (fun records : M.canonicalRecordΩ =>
      ∫ s in Set.Icc (0 : ℝ) T,
        M.instantCoordQVRate ((M.canonicalPathMap records).frozenStateAt s) i) := by
  have hjoint : MeasureTheory.StronglyMeasurable
      (fun p : M.canonicalRecordΩ × ℝ =>
        M.instantCoordQVRate ((M.canonicalPathMap p.1).frozenStateAt p.2) i) :=
    ((Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) => M.instantCoordQVRate x i)).comp
        (M.measurable_prod_canonicalPathMap_frozenStateAt.comp measurable_swap)).stronglyMeasurable
  exact (hjoint.integral_prod_right'
    (ν := MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 T))).measurable

private theorem integrable_canonicalFrozenInstantCoordQVRate_setIntegral
    (M : CTMC.DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (T : ℝ) (hT : 0 ≤ T) :
    MeasureTheory.Integrable
      (fun records : M.canonicalRecordΩ =>
        ∫ s in Set.Icc (0 : ℝ) T,
          M.instantCoordQVRate ((M.canonicalPathMap records).frozenStateAt s) i)
      (M.canonicalRecordMeasure x₀) := by
  obtain ⟨C, _hC, hC⟩ := M.exists_instantCoordQVRate_bound i
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun records : M.canonicalRecordΩ =>
        ∫ s in Set.Icc (0 : ℝ) T,
          M.instantCoordQVRate ((M.canonicalPathMap records).frozenStateAt s) i)
      (M.canonicalRecordMeasure x₀) :=
    (measurable_canonicalFrozenInstantCoordQVRate_setIntegral M i T).aestronglyMeasurable
  refine MeasureTheory.Integrable.of_bound hmeas (C / (M.N : ℝ) * T) ?_
  filter_upwards with records
  have hnonneg :
      0 ≤ ∫ s in Set.Icc (0 : ℝ) T,
        M.instantCoordQVRate ((M.canonicalPathMap records).frozenStateAt s) i := by
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun s _ =>
      M.instantCoordQVRate_nonneg _ i
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have h_vol : MeasureTheory.volume.real (Set.Icc (0 : ℝ) T) = T := by
    rw [_root_.MeasureTheory.Measure.real_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ T - 0)]
    ring
  calc
    ∫ s in Set.Icc (0 : ℝ) T,
        M.instantCoordQVRate ((M.canonicalPathMap records).frozenStateAt s) i
        ≤ ‖∫ s in Set.Icc (0 : ℝ) T,
            M.instantCoordQVRate ((M.canonicalPathMap records).frozenStateAt s) i‖ :=
          le_abs_self _
    _ ≤ C / (M.N : ℝ) * MeasureTheory.volume.real (Set.Icc (0 : ℝ) T) :=
          MeasureTheory.norm_setIntegral_le_of_norm_le_const
            measure_Icc_lt_top (fun s _hs => by
              rw [Real.norm_eq_abs, abs_of_nonneg (M.instantCoordQVRate_nonneg _ i)]
              exact hC _)
    _ = C / (M.N : ℝ) * T := by rw [h_vol]

private theorem integrable_canonicalFrozenInstantQVRate_setIntegral
    (M : CTMC.DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (hT : 0 ≤ T) :
    MeasureTheory.Integrable
      (fun records : M.canonicalRecordΩ =>
        ∫ s in Set.Icc (0 : ℝ) T,
          M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
      (M.canonicalRecordMeasure x₀) := by
  obtain ⟨C, _hC, hC⟩ := M.exists_instantQVRate_bound
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun records : M.canonicalRecordΩ =>
        ∫ s in Set.Icc (0 : ℝ) T,
          M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
      (M.canonicalRecordMeasure x₀) :=
    (measurable_canonicalFrozenInstantQVRate_setIntegral M T).aestronglyMeasurable
  refine MeasureTheory.Integrable.of_bound hmeas (C / (M.N : ℝ) * T) ?_
  filter_upwards with records
  have hnonneg :
      0 ≤ ∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s) := by
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun s _ =>
      M.instantQVRate_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have h_vol : MeasureTheory.volume.real (Set.Icc (0 : ℝ) T) = T := by
    rw [_root_.MeasureTheory.Measure.real_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ T - 0)]
    ring
  calc
    ∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s)
        ≤ ‖∫ s in Set.Icc (0 : ℝ) T,
            M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s)‖ :=
          le_abs_self _
    _ ≤ C / (M.N : ℝ) * MeasureTheory.volume.real (Set.Icc (0 : ℝ) T) :=
          MeasureTheory.norm_setIntegral_le_of_norm_le_const
            measure_Icc_lt_top (fun s _hs => by
              rw [Real.norm_eq_abs, abs_of_nonneg (M.instantQVRate_nonneg _)]
              exact hC _)
    _ = C / (M.N : ℝ) * T := by rw [h_vol]

private theorem halfExpPP_sum_frozenInstantCoordQVRate_setIntegral_le_two
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1)) (T : ℝ) (hT : 0 ≤ T) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    (∑ i : Fin 3,
      ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantCoordQVRate ((M.canonicalPathMap records).frozenStateAt s) i)
        ∂M.canonicalRecordMeasure x₀) ≤
    2 * ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
      M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
      ∂M.canonicalRecordMeasure x₀ := by
  intro M
  let μ := M.canonicalRecordMeasure x₀
  let Qc : Fin 3 → M.canonicalRecordΩ → ℝ := fun i records =>
    ∫ s in Set.Icc (0 : ℝ) T,
      M.instantCoordQVRate ((M.canonicalPathMap records).frozenStateAt s) i
  let Q : M.canonicalRecordΩ → ℝ := fun records =>
    ∫ s in Set.Icc (0 : ℝ) T,
      M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s)
  have hQc_int : ∀ i : Fin 3, MeasureTheory.Integrable (Qc i) μ := by
    intro i
    simpa [Qc, μ, M] using
      integrable_canonicalFrozenInstantCoordQVRate_setIntegral M x₀ i T hT
  have hQ_int : MeasureTheory.Integrable Q μ := by
    obtain ⟨C, _hC, hC⟩ := M.exists_instantQVRate_bound
    have hmeas : MeasureTheory.AEStronglyMeasurable
        (fun records : M.canonicalRecordΩ =>
          ∫ s in Set.Icc (0 : ℝ) T,
            M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
        μ :=
      (measurable_canonicalFrozenInstantQVRate_setIntegral M T).aestronglyMeasurable
    refine MeasureTheory.Integrable.of_bound hmeas (C / (M.N : ℝ) * T) ?_
    filter_upwards with records
    have hnonneg :
        0 ≤ ∫ s in Set.Icc (0 : ℝ) T,
          M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s) := by
      exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun s _ =>
        M.instantQVRate_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    have h_vol : MeasureTheory.volume.real (Set.Icc (0 : ℝ) T) = T := by
      rw [_root_.MeasureTheory.Measure.real_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ T - 0)]
      ring
    calc
      ∫ s in Set.Icc (0 : ℝ) T,
          M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s)
          ≤ ‖∫ s in Set.Icc (0 : ℝ) T,
              M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s)‖ :=
            le_abs_self _
      _ ≤ C / (M.N : ℝ) * MeasureTheory.volume.real (Set.Icc (0 : ℝ) T) :=
            MeasureTheory.norm_setIntegral_le_of_norm_le_const
              measure_Icc_lt_top (fun s _hs => by
                rw [Real.norm_eq_abs, abs_of_nonneg (M.instantQVRate_nonneg _)]
                exact hC _)
      _ = C / (M.N : ℝ) * T := by rw [h_vol]
  have hsum_int : MeasureTheory.Integrable (fun records => ∑ i : Fin 3, Qc i records) μ :=
    MeasureTheory.integrable_finsetSum Finset.univ fun i _ => hQc_int i
  have htwoQ_int : MeasureTheory.Integrable (fun records : M.canonicalRecordΩ =>
      2 * Q records) μ := hQ_int.const_mul 2
  have hpoint :
      (fun records : M.canonicalRecordΩ => ∑ i : Fin 3, Qc i records)
        ≤ᵐ[μ] fun records => 2 * Q records := by
    filter_upwards with records
    have hcoord : ∀ s : ℝ,
        (∑ i : Fin 3,
          M.instantCoordQVRate ((M.canonicalPathMap records).frozenStateAt s) i) ≤
        2 * M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s) := by
      intro s
      simpa [M] using
        halfExpPP_sum_instantCoordQVRate_le_two_instantQVRate
          N hN ((M.canonicalPathMap records).frozenStateAt s)
    have hcoord_int_on : ∀ i : Fin 3, MeasureTheory.IntegrableOn
        (fun s : ℝ =>
          M.instantCoordQVRate ((M.canonicalPathMap records).frozenStateAt s) i)
        (Set.Icc (0 : ℝ) T) := by
      intro i
      obtain ⟨C, _hC, hC⟩ := M.exists_instantCoordQVRate_bound i
      have hmeas : Measurable (fun s : ℝ =>
          M.instantCoordQVRate ((M.canonicalPathMap records).frozenStateAt s) i) := by
        have hpair : Measurable (fun s : ℝ => (s, records)) :=
          Measurable.prodMk measurable_id measurable_const
        exact (Measurable.of_discrete
          (f := fun x : Fin 3 → Fin (M.N + 1) =>
            M.instantCoordQVRate x i)).comp
              (M.measurable_prod_canonicalPathMap_frozenStateAt.comp hpair)
      refine MeasureTheory.IntegrableOn.of_bound measure_Icc_lt_top
        hmeas.aestronglyMeasurable (C / (M.N : ℝ)) ?_
      filter_upwards with s
      rw [Real.norm_eq_abs, abs_of_nonneg (M.instantCoordQVRate_nonneg _ i)]
      exact hC _
    have htwoQ_int_on : MeasureTheory.IntegrableOn
        (fun s : ℝ =>
          2 * M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
        (Set.Icc (0 : ℝ) T) := by
      obtain ⟨C, _hC, hC⟩ := M.exists_instantQVRate_bound
      have hmeas : Measurable (fun s : ℝ =>
          2 * M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s)) := by
        have hpair : Measurable (fun s : ℝ => (s, records)) :=
          Measurable.prodMk measurable_id measurable_const
        exact measurable_const.mul
          ((Measurable.of_discrete
            (f := fun x : Fin 3 → Fin (M.N + 1) =>
              M.instantQVRate x)).comp
                (M.measurable_prod_canonicalPathMap_frozenStateAt.comp hpair))
      refine MeasureTheory.IntegrableOn.of_bound measure_Icc_lt_top
        hmeas.aestronglyMeasurable (2 * (C / (M.N : ℝ))) ?_
      filter_upwards with s
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (M.instantQVRate_nonneg _))]
      exact mul_le_mul_of_nonneg_left (hC _) (by norm_num)
    calc
      (∑ i : Fin 3, Qc i records)
          = ∫ s in Set.Icc (0 : ℝ) T,
              ∑ i : Fin 3,
                M.instantCoordQVRate ((M.canonicalPathMap records).frozenStateAt s) i := by
              change (∑ i : Fin 3,
                  ∫ s, M.instantCoordQVRate
                    ((M.canonicalPathMap records).frozenStateAt s) i
                    ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T))) =
                ∫ s, (∑ i : Fin 3,
                  M.instantCoordQVRate
                    ((M.canonicalPathMap records).frozenStateAt s) i)
                  ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T))
              rw [MeasureTheory.integral_finsetSum Finset.univ]
              intro i _
              exact hcoord_int_on i
      _ ≤ ∫ s in Set.Icc (0 : ℝ) T,
            2 * M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s) := by
            exact MeasureTheory.setIntegral_mono_on
              (by
                change MeasureTheory.Integrable
                  (fun s : ℝ => ∑ i : Fin 3,
                    M.instantCoordQVRate
                      ((M.canonicalPathMap records).frozenStateAt s) i)
                  (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T))
                exact MeasureTheory.integrable_finsetSum Finset.univ
                  fun i _ => hcoord_int_on i)
              htwoQ_int_on
              measurableSet_Icc (fun s _hs => hcoord s)
      _ = 2 * Q records := by
            rw [MeasureTheory.integral_const_mul]
  have hmono := MeasureTheory.integral_mono_ae hsum_int htwoQ_int hpoint
  calc
    (∑ i : Fin 3, ∫ records, Qc i records ∂μ)
        = ∫ records, ∑ i : Fin 3, Qc i records ∂μ := by
            rw [MeasureTheory.integral_finsetSum Finset.univ]
            intro i _
            exact hQc_int i
    _ ≤ ∫ records, 2 * Q records ∂μ := hmono
    _ = 2 * ∫ records, Q records ∂μ := by rw [MeasureTheory.integral_const_mul]
    _ = 2 * ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
        ∂M.canonicalRecordMeasure x₀ := by
          simp [Q, μ]

private theorem halfExpPP_sum_clockTruncatedCoordQV_integral_le_two_vector
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1)) (T : ℝ) (k : ℕ) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    (∑ i : Fin 3,
      ∫ records,
        (let hist := Preorder.frestrictLe k records
         let x : Fin 3 → Fin (N + 1) :=
          CTMC.QMatrix.currentStateFromHistory
            (S := Fin 3 → Fin (N + 1)) k hist
         M.instantCoordQVRate x i *
          min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist))
        ∂M.canonicalRecordMeasure x₀) ≤
      2 * ∫ records,
        (let hist := Preorder.frestrictLe k records
         let x : Fin 3 → Fin (N + 1) :=
          CTMC.QMatrix.currentStateFromHistory
            (S := Fin 3 → Fin (N + 1)) k hist
         M.instantQVRate x *
          min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist))
        ∂M.canonicalRecordMeasure x₀ := by
  intro M
  let μ := M.canonicalRecordMeasure x₀
  let X : M.canonicalRecordΩ → Fin 3 → Fin (N + 1) := fun records =>
    CTMC.QMatrix.currentStateFromHistory
      (S := Fin 3 → Fin (N + 1)) k (Preorder.frestrictLe k records)
  let A : M.canonicalRecordΩ → ℝ := fun records =>
    min (records (k + 1)).1
      (CTMC.QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records))
  let C : Fin 3 → M.canonicalRecordΩ → ℝ := fun i records =>
    M.instantCoordQVRate (X records) i * A records
  let V : M.canonicalRecordΩ → ℝ := fun records =>
    M.instantQVRate (X records) * A records
  change (∑ i : Fin 3, ∫ records, C i records ∂μ) ≤
    2 * ∫ records, V records ∂μ
  have hC_int : ∀ i : Fin 3, MeasureTheory.Integrable (C i) μ := by
    intro i
    simpa [C, X, A, μ] using
      M.integrable_clockTruncatedCoordQVIncrement x₀ T i k
  have hV_int : MeasureTheory.Integrable V μ := by
    simpa [V, X, A, μ] using
      M.integrable_clockTruncatedQVIncrement x₀ T k
  have hsumC_int : MeasureTheory.Integrable
      (fun records => ∑ i : Fin 3, C i records) μ :=
    MeasureTheory.integrable_finsetSum Finset.univ fun i _ => hC_int i
  have htwoV_int : MeasureTheory.Integrable
      (fun records : M.canonicalRecordΩ => 2 * V records) μ :=
    hV_int.const_mul 2
  have hpoint :
      (fun records : M.canonicalRecordΩ => ∑ i : Fin 3, C i records)
        ≤ᵐ[μ] fun records => 2 * V records := by
    filter_upwards
      [M.toQMatrix.canonicalRecordMeasure_all_next_holdingTime_nonneg_ae x₀]
      with records hhold
    have hA_nonneg : 0 ≤ A records := by
      dsimp [A]
      exact le_min (hhold k)
        (CTMC.QMatrix.historyClockRemaining_nonneg T k (Preorder.frestrictLe k records))
    calc
      (∑ i : Fin 3, C i records)
          = (∑ i : Fin 3, M.instantCoordQVRate (X records) i) * A records := by
            simp [C, Finset.sum_mul]
      _ ≤ (2 * M.instantQVRate (X records)) * A records := by
            exact mul_le_mul_of_nonneg_right
              (by
                simpa [M] using
                  halfExpPP_sum_instantCoordQVRate_le_two_instantQVRate
                    N hN (X records))
              hA_nonneg
      _ = 2 * V records := by ring
  calc
    (∑ i : Fin 3, ∫ records, C i records ∂μ)
        = ∫ records, (∑ i : Fin 3, C i records) ∂μ := by
            rw [MeasureTheory.integral_finsetSum Finset.univ]
            intro i _hi
            exact hC_int i
    _ ≤ ∫ records, 2 * V records ∂μ :=
          MeasureTheory.integral_mono_ae hsumC_int htwoV_int hpoint
    _ = 2 * ∫ records, V records ∂μ := by
          rw [MeasureTheory.integral_const_mul]

private theorem halfExpPP_clockTruncatedQV_integrand_eq_zero_ae_of_ge_absorb
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1))
    (hinit : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x₀)
    (T : ℝ) {k : ℕ} (hk : N ≤ k) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    (fun records : M.canonicalRecordΩ =>
      (let hist := Preorder.frestrictLe k records
       let x : Fin 3 → Fin (N + 1) :=
        CTMC.QMatrix.currentStateFromHistory
          (S := Fin 3 → Fin (N + 1)) k hist
       M.instantQVRate x *
        min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist)))
      =ᵐ[M.canonicalRecordMeasure x₀] fun _ => 0 := by
  intro M
  filter_upwards
    [halfExpPP_canonical_stateSeq_absorbing_at_N_ae N hN x₀ hinit,
     halfExpPP_canonical_absorbed_from_N_ae N hN x₀ hinit]
    with records habsN habsFrom
  have hstatek :
      (M.canonicalPathMap records).stateSeq k =
        (M.canonicalPathMap records).stateSeq N :=
    habsFrom.1 k hk
  have hcur :
      CTMC.QMatrix.currentStateFromHistory
          (S := Fin 3 → Fin (N + 1)) k (Preorder.frestrictLe k records) =
        (M.canonicalPathMap records).stateSeq k := by
    simp [M, CTMC.DensityDepCTMC.canonicalPathMap,
      CTMC.QMatrix.currentStateFromHistory_frestrictLe]
  have hxabs :
      M.toQMatrix.IsAbsorbing
        (CTMC.QMatrix.currentStateFromHistory
          (S := Fin 3 → Fin (N + 1)) k (Preorder.frestrictLe k records)) := by
    rw [hcur, hstatek]
    exact habsN
  have hqv :
      M.instantQVRate
        (CTMC.QMatrix.currentStateFromHistory
          (S := Fin 3 → Fin (N + 1)) k (Preorder.frestrictLe k records)) = 0 := by
    exact M.instantQVRate_eq_zero_of_exitRateAt_zero
      (by simpa [CTMC.DensityDepCTMC.exitRateAt] using hxabs)
  have hqv_records : M.instantQVRate (records k).2 = 0 := by
    simpa [M, CTMC.DensityDepCTMC.canonicalPathMap,
      CTMC.QMatrix.currentStateFromHistory_frestrictLe,
      CTMC.QMatrix.recordTrajectoryToPath_stateSeq] using hqv
  simp [hqv_records]

private theorem halfExpPP_clockTruncatedQV_integral_eq_zero_of_ge_absorb
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1))
    (hinit : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x₀)
    (T : ℝ) {k : ℕ} (hk : N ≤ k) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    ∫ records,
      (let hist := Preorder.frestrictLe k records
       let x : Fin 3 → Fin (N + 1) :=
        CTMC.QMatrix.currentStateFromHistory
          (S := Fin 3 → Fin (N + 1)) k hist
       M.instantQVRate x *
        min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist))
      ∂M.canonicalRecordMeasure x₀ = 0 := by
  intro M
  exact MeasureTheory.integral_eq_zero_of_ae
    (halfExpPP_clockTruncatedQV_integrand_eq_zero_ae_of_ge_absorb
      N hN x₀ hinit T hk)

private theorem halfExpPP_sum_clockTruncatedQV_integral_range_succ_absorb_eq_range
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1))
    (hinit : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x₀)
    (T : ℝ) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    (∑ k ∈ Finset.range (N + 1),
      ∫ records,
        (let hist := Preorder.frestrictLe k records
         let x : Fin 3 → Fin (N + 1) :=
          CTMC.QMatrix.currentStateFromHistory
            (S := Fin 3 → Fin (N + 1)) k hist
         M.instantQVRate x *
          min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist))
        ∂M.canonicalRecordMeasure x₀) =
      ∑ k ∈ Finset.range N,
        ∫ records,
          (let hist := Preorder.frestrictLe k records
           let x : Fin 3 → Fin (N + 1) :=
            CTMC.QMatrix.currentStateFromHistory
              (S := Fin 3 → Fin (N + 1)) k hist
           M.instantQVRate x *
            min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist))
          ∂M.canonicalRecordMeasure x₀ := by
  intro M
  rw [Finset.sum_range_succ]
  have hzero :
      ∫ records,
        (let hist := Preorder.frestrictLe N records
         let x : Fin 3 → Fin (N + 1) :=
          CTMC.QMatrix.currentStateFromHistory
            (S := Fin 3 → Fin (N + 1)) N hist
         M.instantQVRate x *
          min (records (N + 1)).1 (CTMC.QMatrix.historyClockRemaining T N hist))
        ∂M.canonicalRecordMeasure x₀ = 0 := by
    simpa [M] using
      halfExpPP_clockTruncatedQV_integral_eq_zero_of_ge_absorb
        N hN x₀ hinit T (le_rfl : N ≤ N)
  rw [hzero, add_zero]

private theorem halfExpPP_truncatedJumpSq_integrand_eq_zero_ae_of_ge_absorb
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1))
    (hinit : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x₀)
    (T : ℝ) {k : ℕ} (hk : N ≤ k) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    (fun records : M.canonicalRecordΩ =>
      M.truncatedJumpSqIncrementFromHistory T k
        (Preorder.frestrictLe k records) (records (k + 1)))
      =ᵐ[M.canonicalRecordMeasure x₀] fun _ => 0 := by
  intro M
  filter_upwards
    [halfExpPP_canonical_stateSeq_absorbing_at_N_ae N hN x₀ hinit,
     halfExpPP_canonical_absorbed_from_N_ae N hN x₀ hinit,
     M.toQMatrix.canonicalRecordMeasure_all_next_state_eq_current_ae_of_absorbing x₀]
    with records habsN habsFrom hstay
  have hstatek :
      (M.canonicalPathMap records).stateSeq k =
        (M.canonicalPathMap records).stateSeq N :=
    habsFrom.1 k hk
  have hcur :
      CTMC.QMatrix.currentStateFromHistory
          (S := Fin 3 → Fin (N + 1)) k (Preorder.frestrictLe k records) =
        (M.canonicalPathMap records).stateSeq k := by
    simp [M, CTMC.DensityDepCTMC.canonicalPathMap,
      CTMC.QMatrix.currentStateFromHistory_frestrictLe]
  have hxabs :
      M.toQMatrix.IsAbsorbing
        (CTMC.QMatrix.currentStateFromHistory
          (S := Fin 3 → Fin (N + 1)) k (Preorder.frestrictLe k records)) := by
    rw [hcur, hstatek]
    exact habsN
  have hnext :
      (records (k + 1)).2 =
        CTMC.QMatrix.currentStateFromHistory
          (S := Fin 3 → Fin (N + 1)) k (Preorder.frestrictLe k records) :=
    hstay k hxabs
  simp [CTMC.DensityDepCTMC.truncatedJumpSqIncrementFromHistory, hnext]

private theorem halfExpPP_truncatedJumpSq_integral_eq_zero_of_ge_absorb
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1))
    (hinit : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x₀)
    (T : ℝ) {k : ℕ} (hk : N ≤ k) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    ∫ records,
      M.truncatedJumpSqIncrementFromHistory T k
        (Preorder.frestrictLe k records) (records (k + 1))
      ∂M.canonicalRecordMeasure x₀ = 0 := by
  intro M
  exact MeasureTheory.integral_eq_zero_of_ae
    (halfExpPP_truncatedJumpSq_integrand_eq_zero_ae_of_ge_absorb
      N hN x₀ hinit T hk)

private theorem halfExpPP_sum_truncatedJumpSq_integral_range_succ_absorb_eq_range
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1))
    (hinit : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x₀)
    (T : ℝ) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    (∑ k ∈ Finset.range (N + 1),
      ∫ records,
        M.truncatedJumpSqIncrementFromHistory T k
          (Preorder.frestrictLe k records) (records (k + 1))
        ∂M.canonicalRecordMeasure x₀) =
      ∑ k ∈ Finset.range N,
        ∫ records,
          M.truncatedJumpSqIncrementFromHistory T k
            (Preorder.frestrictLe k records) (records (k + 1))
          ∂M.canonicalRecordMeasure x₀ := by
  intro M
  rw [Finset.sum_range_succ]
  have hzero :
      ∫ records,
        M.truncatedJumpSqIncrementFromHistory T N
          (Preorder.frestrictLe N records) (records (N + 1))
        ∂M.canonicalRecordMeasure x₀ = 0 := by
    simpa [M] using
      halfExpPP_truncatedJumpSq_integral_eq_zero_of_ge_absorb
        N hN x₀ hinit T (le_rfl : N ≤ N)
  rw [hzero, add_zero]

private theorem norm_sub_sq_le_four_thirds_add_four
    {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x - y‖ ^ 2 ≤ (4 / 3 : ℝ) * ‖x‖ ^ 2 + 4 * ‖y‖ ^ 2 := by
  have htri : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
  have htri_sq : ‖x - y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := by
    exact sq_le_sq'
      (by nlinarith [norm_nonneg (x - y), norm_nonneg x, norm_nonneg y])
      htri
  have halg : (‖x‖ + ‖y‖) ^ 2 ≤
      (4 / 3 : ℝ) * ‖x‖ ^ 2 + 4 * ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x‖ - 3 * ‖y‖)]
  exact htri_sq.trans halg

private theorem norm_affine_sq_le_max_sq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ‖(1 - θ) • x + θ • y‖ ^ 2 ≤ max (‖x‖ ^ 2) (‖y‖ ^ 2) := by
  let R : ℝ := max ‖x‖ ‖y‖
  have hR_nonneg : 0 ≤ R := by
    exact (norm_nonneg x).trans (le_max_left _ _)
  have hxR : ‖x‖ ≤ R := le_max_left _ _
  have hyR : ‖y‖ ≤ R := le_max_right _ _
  have hθ01 : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  have hnorm_le : ‖(1 - θ) • x + θ • y‖ ≤ R := by
    calc
      ‖(1 - θ) • x + θ • y‖
          ≤ ‖(1 - θ) • x‖ + ‖θ • y‖ := norm_add_le _ _
      _ = (1 - θ) * ‖x‖ + θ * ‖y‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg hθ01, abs_of_nonneg hθ0]
      _ ≤ (1 - θ) * R + θ * R := by
            gcongr
      _ = R := by ring
  have hsq_le : ‖(1 - θ) • x + θ • y‖ ^ 2 ≤ R ^ 2 := by
    exact sq_le_sq' ((neg_nonpos.mpr hR_nonneg).trans (norm_nonneg _)) hnorm_le
  have hR_sq :
      R ^ 2 = max (‖x‖ ^ 2) (‖y‖ ^ 2) := by
    by_cases hxy : ‖x‖ ≤ ‖y‖
    · have hsxy : ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 :=
        sq_le_sq' ((neg_nonpos.mpr (norm_nonneg y)).trans (norm_nonneg x)) hxy
      simp [R, max_eq_right hxy, max_eq_right hsxy]
    · have hyx : ‖y‖ ≤ ‖x‖ := le_of_not_ge hxy
      have hsyx : ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 :=
        sq_le_sq' ((neg_nonpos.mpr (norm_nonneg x)).trans (norm_nonneg y)) hyx
      simp [R, max_eq_left hyx, max_eq_left hsyx]
  simpa [hR_sq] using hsq_le

private lemma halfExpPP_affineParameter
    {l r s : ℝ} (hlr : l ≤ r) (hls : l ≤ s) (hsr : s ≤ r) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ s = (1 - θ) * l + θ * r := by
  by_cases hrl : r = l
  · subst r
    have hs : s = l := le_antisymm hsr hls
    refine ⟨0, by norm_num, by norm_num, ?_⟩
    subst s
    ring
  · have hne_lr : l ≠ r := fun h => hrl h.symm
    have hlt : l < r := lt_of_le_of_ne hlr hne_lr
    have hden_pos : 0 < r - l := sub_pos.mpr hlt
    refine ⟨(s - l) / (r - l), ?_, ?_, ?_⟩
    · exact div_nonneg (sub_nonneg.mpr hls) (le_of_lt hden_pos)
    · have hsubl : s - l ≤ r - l := by linarith
      have hle := div_le_div_of_nonneg_right hsubl (le_of_lt hden_pos)
      simpa [div_self hden_pos.ne'] using hle
    · field_simp [hden_pos.ne']
      ring

private noncomputable def halfExpPP_clockSkeletonVec
    (M : CTMC.DensityDepCTMC 3) (T : ℝ) (k : ℕ)
    (records : M.canonicalRecordΩ) : Fin 3 → ℝ :=
  fun i : Fin 3 => M.canonicalFrozenClockTruncatedMartingale T i k records

private noncomputable def halfExpPP_clockSkeletonSupSq
    (M : CTMC.DensityDepCTMC 3) (T : ℝ)
    (records : M.canonicalRecordΩ) : ℝ :=
  (Finset.range (M.N + 2)).sup'
    (by simp)
    (fun k => ‖halfExpPP_clockSkeletonVec M T k records‖ ^ 2)

private noncomputable def halfExpPP_sumTruncatedJumpSq
    (M : CTMC.DensityDepCTMC 3) (T : ℝ)
    (records : M.canonicalRecordΩ) : ℝ :=
  ∑ k ∈ Finset.range (M.N + 1),
    M.truncatedJumpSqIncrementFromHistory T k
      (Preorder.frestrictLe k records) (records (k + 1))

private theorem halfExpPP_sumTruncatedJumpSq_nonneg
    (M : CTMC.DensityDepCTMC 3) (T : ℝ)
    (records : M.canonicalRecordΩ) :
    0 ≤ halfExpPP_sumTruncatedJumpSq M T records := by
  classical
  unfold halfExpPP_sumTruncatedJumpSq
  refine Finset.sum_nonneg ?_
  intro k _hk
  by_cases hle :
      (records (k + 1)).1 ≤
        CTMC.QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records)
  · simp [CTMC.DensityDepCTMC.truncatedJumpSqIncrementFromHistory,
      Set.indicator, hle]
  · simp [CTMC.DensityDepCTMC.truncatedJumpSqIncrementFromHistory,
      Set.indicator, hle]

private theorem halfExpPP_clockSkeletonSupSq_nonneg
    (M : CTMC.DensityDepCTMC 3) (T : ℝ)
    (records : M.canonicalRecordΩ) :
    0 ≤ halfExpPP_clockSkeletonSupSq M T records := by
  classical
  unfold halfExpPP_clockSkeletonSupSq
  exact (sq_nonneg ‖halfExpPP_clockSkeletonVec M T 0 records‖).trans
    (Finset.le_sup'
      (s := Finset.range (M.N + 2))
      (f := fun k => ‖halfExpPP_clockSkeletonVec M T k records‖ ^ 2)
      (Finset.mem_range.mpr (by omega)))

private theorem halfExpPP_clockSkeletonVec_sq_le_sup
    (M : CTMC.DensityDepCTMC 3) (T : ℝ)
    (records : M.canonicalRecordΩ) {k : ℕ}
    (hk : k ∈ Finset.range (M.N + 2)) :
    ‖halfExpPP_clockSkeletonVec M T k records‖ ^ 2 ≤
      halfExpPP_clockSkeletonSupSq M T records := by
  classical
  simpa [halfExpPP_clockSkeletonSupSq] using
    Finset.le_sup'
      (s := Finset.range (M.N + 2))
      (f := fun k => ‖halfExpPP_clockSkeletonVec M T k records‖ ^ 2)
      hk

private theorem halfExpPP_clockSkeletonSupSq_le_affineBridgeBound
    (M : CTMC.DensityDepCTMC 3) (T : ℝ)
    (records : M.canonicalRecordΩ) :
    halfExpPP_clockSkeletonSupSq M T records ≤
      (4 / 3 : ℝ) * halfExpPP_clockSkeletonSupSq M T records +
        4 * halfExpPP_sumTruncatedJumpSq M T records := by
  have hA := halfExpPP_clockSkeletonSupSq_nonneg M T records
  have hJ := halfExpPP_sumTruncatedJumpSq_nonneg M T records
  nlinarith

private theorem halfExpPP_locate_time_liveCell_or_absorbedTail
    (N : ℕ) (hN : 0 < N) (T s : ℝ)
    (records :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordΩ)
    (hAbsN :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
        (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap records).stateSeq N))
    (hs : 0 ≤ s ∧ s ≤ T) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    let path := M.canonicalPathMap records
    let a := halfExpPP_firstAbsIdx N hN records hAbsN
    (∃ k, k < a ∧
      path.sojournStart k ≤ s ∧
      s < path.sojournStart (k + 1) ∧
      s ≤ min T (path.sojournStart (k + 1))) ∨
      path.sojournStart a ≤ s := by
  classical
  let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  let path := M.canonicalPathMap records
  let a := halfExpPP_firstAbsIdx N hN records hAbsN
  by_cases htail : path.sojournStart a ≤ s
  · exact Or.inr htail
  · have hslt_a : s < path.sojournStart a := lt_of_not_ge htail
    have hex : ∃ n : ℕ, n ≤ a ∧ s < path.sojournStart n :=
      ⟨a, le_rfl, hslt_a⟩
    let n : ℕ := Nat.find hex
    have hn_le_a : n ≤ a := by
      simpa [n] using (Nat.find_spec hex).1
    have hn_slt : s < path.sojournStart n := by
      simpa [n] using (Nat.find_spec hex).2
    have hn_ne_zero : n ≠ 0 := by
      intro hzero
      have hslt0 : s < 0 := by
        simpa [hzero] using hn_slt
      linarith
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn_ne_zero
    let k : ℕ := n - 1
    have hk_succ : k + 1 = n := by
      dsimp [k]
      exact Nat.succ_pred_eq_of_pos hn_pos
    have hk_lt_n : k < n := by
      dsimp [k]
      omega
    have hk_lt_a : k < a := by omega
    have hmin := Nat.find_min hex hk_lt_n
    have hstart_le : path.sojournStart k ≤ s := by
      refine le_of_not_gt ?_
      intro hslt_k
      exact hmin ⟨by omega, hslt_k⟩
    have hs_le_next : s ≤ path.sojournStart (k + 1) := by
      simpa [hk_succ] using le_of_lt hn_slt
    exact Or.inl ⟨k, hk_lt_a, hstart_le, by simpa [hk_succ] using hn_slt,
      le_min hs.2 hs_le_next⟩

private theorem halfExpPP_times_le_of_prefix
    {S : Type*} (path : CTMC.CTMCPath S) {a b K : ℕ}
    (hab : a ≤ b) (hbK : b ≤ K)
    (hstrict_prefix : ∀ n < K, path.times n < path.times (n + 1)) :
    path.times a ≤ path.times b := by
  induction hab with
  | refl => exact le_rfl
  | step hab ih =>
      exact le_trans (ih (Nat.le_of_succ_le hbK))
        (le_of_lt (hstrict_prefix _ (Nat.lt_of_succ_le hbK)))

private theorem halfExpPP_jumpCount_eq_of_live_sojourn
    {S : Type*} (path : CTMC.CTMCPath S)
    {k : ℕ} {s : ℝ}
    (hstrict_prefix : ∀ n < k, path.times n < path.times (n + 1))
    (hstart : path.sojournStart k ≤ s)
    (hend : s < path.sojournStart (k + 1)) :
    path.jumpCount s = k := by
  classical
  rw [path.jumpCount_eq_iff s k]
  left
  constructor
  · cases k with
    | zero =>
        simpa [CTMC.CTMCPath.sojournStart] using hend
    | succ k =>
        simpa [CTMC.CTMCPath.sojournStart] using hend
  · intro j hj
    cases j with
    | zero =>
        have htime0_le : path.times 0 ≤ s := by
          cases k with
          | zero => omega
          | succ k =>
              have hle : path.sojournStart 1 ≤ path.sojournStart (Nat.succ k) := by
                simpa [CTMC.CTMCPath.sojournStart] using
                  halfExpPP_times_le_of_prefix path
                    (Nat.zero_le k) (Nat.le_succ k) hstrict_prefix
              exact le_trans hle hstart
        exact not_lt.mpr htime0_le
    | succ j =>
        have hle_succ : path.times (j + 1) ≤ path.sojournStart k := by
          cases k with
          | zero => omega
          | succ k =>
              simpa [CTMC.CTMCPath.sojournStart] using
                halfExpPP_times_le_of_prefix path
                  (by omega : j + 1 ≤ k) (Nat.le_succ k) hstrict_prefix
        exact not_lt.mpr (le_trans hle_succ hstart)

private theorem halfExpPP_frozenMartingalePart_live_eq_clockTruncated
    (N : ℕ) (hN : 0 < N) (s : ℝ)
    (records :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordΩ)
    (k : ℕ)
    (hstrict : ∀ n,
      (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).times n <
      ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).times (n + 1)))
    (hpos :
      0 < ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).times 0)
    (hseq :
      ∀ m ≤ k,
        (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex
          (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
            records).stateSeq m))
    (hs0 : 0 ≤ s)
    (hstart :
      ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).sojournStart k ≤ s)
    (hend :
      s < ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).sojournStart (k + 1)) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    let path := M.canonicalPathMap records
    M.frozenMartingalePart M.canonicalPathMap s records =
      fun i : Fin 3 => M.frozenClockTruncatedMartingale path i s (k + 1) := by
  classical
  let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  let path := M.canonicalPathMap records
  have hcount : path.jumpCount s = k := by
    exact halfExpPP_jumpCount_eq_of_live_sojourn path
      (fun n _hn => hstrict n) hstart hend
  have hfuture : ∃ n, s < path.times n := by
    refine ⟨k, ?_⟩
    cases k with
    | zero =>
        simpa [path, CTMC.CTMCPath.sojournStart] using hend
    | succ k =>
        simpa [path, CTMC.CTMCPath.sojournStart] using hend
  have hBC : M.BoundaryCompatibleOnSimplex := by
    simpa [M] using halfExpPP_boundaryCompatibleOnSimplex N hN
  have hDrift : ∀ m ≤ path.jumpCount s,
      M.generatorDrift (path.stateSeq m) =
        M.rateSpec.drift (M.scaledState (path.stateSeq m)) := by
    intro m hm
    exact M.generatorDrift_eq_rateSpec_drift_of_boundaryCompatibleOnSimplex
      hBC (by
        exact hseq m (by simpa [hcount] using hm))
  ext i
  have h :=
    M.frozenClockTruncatedMartingale_jumpCount_succ_eq_frozenMartingalePart
      path hstrict hpos hs0 hfuture hDrift i
  simpa [M, path, hcount] using h.symm

private theorem halfExpPP_frozenDensityProcess_at_live_start_eq_scaledState
    (M : CTMC.DensityDepCTMC 3) (records : M.canonicalRecordΩ)
    (k : ℕ)
    (hstrict : ∀ n,
      (M.canonicalPathMap records).times n <
        (M.canonicalPathMap records).times (n + 1))
    (hstart_lt_end :
      (M.canonicalPathMap records).sojournStart k <
        (M.canonicalPathMap records).sojournStart (k + 1)) :
    M.frozenDensityProcess M.canonicalPathMap
        ((M.canonicalPathMap records).sojournStart k) records =
      M.scaledState ((M.canonicalPathMap records).stateSeq k) := by
  classical
  let path := M.canonicalPathMap records
  have hcount : path.jumpCount (path.sojournStart k) = k := by
    exact halfExpPP_jumpCount_eq_of_live_sojourn path
      (fun n _hn => hstrict n) le_rfl hstart_lt_end
  have hfuture : ∃ n, path.sojournStart k < path.times n := by
    refine ⟨k, ?_⟩
    cases k with
    | zero =>
        simpa [path, CTMC.CTMCPath.sojournStart] using hstart_lt_end
    | succ k =>
        simpa [path, CTMC.CTMCPath.sojournStart] using hstart_lt_end
  have hstate :
      path.frozenStateAt (path.sojournStart k) = path.stateSeq k := by
    have hcur :=
      CTMC.DensityDepCTMC.frozenStateAt_eq_stateSeq_jumpCount_of_mem_currentSojourn
        path hstrict (T := path.sojournStart k) (t := path.sojournStart k)
        hfuture
        (by simp [hcount])
    simpa [hcount] using hcur
  ext i
  simp [CTMC.DensityDepCTMC.frozenDensityProcess,
    CTMC.DensityDepCTMC.scaledState, path, hstate]

private theorem halfExpPP_frozenStateAt_eq_stateSeq_of_mem_sojournInterval
    {S : Type*} (path : CTMC.CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (n : ℕ) {t : ℝ} (ht : t ∈ path.sojournInterval n) :
    path.frozenStateAt t = path.stateSeq n := by
  have hfuture : ∃ m, t < path.times m := by
    exact ⟨n, by
      simpa [CTMC.CTMCPath.sojournInterval, CTMC.CTMCPath.sojournEnd] using ht.2⟩
  rw [path.frozenStateAt_eq_stateAt_of_lt_times t hfuture]
  exact path.stateAt_eq_stateSeq_of_mem_sojournInterval hstrict n ht

private noncomputable def halfExpPP_clockCellLeftLimit
    (M : CTMC.DensityDepCTMC 3) (T : ℝ) (k : ℕ)
    (records : M.canonicalRecordΩ) : Fin 3 → ℝ :=
  let path := M.canonicalPathMap records
  let t0 := path.sojournStart k
  let t1 := min T (path.sojournStart (k + 1))
  M.frozenMartingalePart M.canonicalPathMap t0 records -
    (t1 - t0) •
      M.rateSpec.drift (M.frozenDensityProcess M.canonicalPathMap t0 records)

private noncomputable def halfExpPP_strictCompletionThrough
    {S : Type*} (path : CTMC.CTMCPath S) (n : ℕ) : CTMC.CTMCPath S where
  init := path.init
  jumps := fun k => path.jumps k
  times := fun k => if hk : k ≤ n then path.times k else path.times n + (k - n : ℝ)

private theorem halfExpPP_strictCompletionThrough_stateSeq_eq
    {S : Type*} (path : CTMC.CTMCPath S) (n m : ℕ) :
    (halfExpPP_strictCompletionThrough path n).stateSeq m = path.stateSeq m := by
  cases m <;> rfl

private theorem halfExpPP_strictCompletionThrough_sojournStart_eq_of_le
    {S : Type*} (path : CTMC.CTMCPath S) (n m : ℕ) (hm : m ≤ n) :
    (halfExpPP_strictCompletionThrough path n).sojournStart m =
      path.sojournStart m := by
  cases m with
  | zero => rfl
  | succ m =>
      have hm' : m ≤ n := Nat.le_of_succ_le hm
      simp [halfExpPP_strictCompletionThrough, hm']

private theorem halfExpPP_strictCompletionThrough_sojournStart_succ_eq
    {S : Type*} (path : CTMC.CTMCPath S) (n : ℕ) :
    (halfExpPP_strictCompletionThrough path n).sojournStart (n + 1) =
      path.sojournStart (n + 1) := by
  simp [CTMC.CTMCPath.sojournStart, halfExpPP_strictCompletionThrough]

private theorem halfExpPP_strictCompletionThrough_sojournTime_eq_of_lt
    {S : Type*} (path : CTMC.CTMCPath S) {n m : ℕ} (hm : m < n) :
    (halfExpPP_strictCompletionThrough path n).sojournTime m =
      path.sojournTime m := by
  cases m with
  | zero =>
      have hn : 0 ≤ n := Nat.zero_le n
      simp [CTMC.CTMCPath.sojournTime, halfExpPP_strictCompletionThrough, hn]
  | succ m =>
      have hm_le : m ≤ n := by omega
      have hms_le : m + 1 ≤ n := le_of_lt hm
      simp [CTMC.CTMCPath.sojournTime, halfExpPP_strictCompletionThrough,
        hm_le, hms_le]

private theorem halfExpPP_strictCompletionThrough_sojournTime_eq_of_le
    {S : Type*} (path : CTMC.CTMCPath S) {n m : ℕ} (hm : m ≤ n) :
    (halfExpPP_strictCompletionThrough path n).sojournTime m =
      path.sojournTime m := by
  cases m with
  | zero =>
      have hn : 0 ≤ n := Nat.zero_le n
      simp [CTMC.CTMCPath.sojournTime, halfExpPP_strictCompletionThrough, hn]
  | succ m =>
      have hm_le : m ≤ n := by omega
      have hms_le : m + 1 ≤ n := hm
      simp [CTMC.CTMCPath.sojournTime, halfExpPP_strictCompletionThrough,
        hm_le, hms_le]

private theorem halfExpPP_strictCompletionThrough_strict
    {S : Type*} (path : CTMC.CTMCPath S) (n : ℕ)
    (hpos0 : 0 < path.times 0)
    (hstrict_prefix : ∀ k < n, path.times k < path.times (k + 1)) :
    0 < (halfExpPP_strictCompletionThrough path n).times 0 ∧
      ∀ k,
        (halfExpPP_strictCompletionThrough path n).times k <
          (halfExpPP_strictCompletionThrough path n).times (k + 1) := by
  constructor
  · simp [halfExpPP_strictCompletionThrough, hpos0]
  · intro k
    by_cases hk1 : k + 1 ≤ n
    · have hk : k ≤ n := Nat.le_trans (Nat.le_succ k) hk1
      have hklt : k < n := Nat.lt_of_succ_le hk1
      simpa [halfExpPP_strictCompletionThrough, hk, hk1] using
        hstrict_prefix k hklt
    · by_cases hk : k ≤ n
      · have hkeq : k = n := by
          have hnlt : ¬ k < n := by
            simpa [Nat.succ_le_iff] using hk1
          exact le_antisymm hk (Nat.le_of_not_gt hnlt)
        subst k
        simp [halfExpPP_strictCompletionThrough]
      · have hsub_succ : (k + 1 - n : ℕ) = (k - n) + 1 := by omega
        simp [halfExpPP_strictCompletionThrough, hk, hk1, hsub_succ]

private theorem halfExpPP_strictCompletionThrough_frozenStateAt_eq_of_lt_succ
    {S : Type*} (path : CTMC.CTMCPath S) (n : ℕ) {t : ℝ}
    (ht : t < path.sojournStart (n + 1)) :
    (halfExpPP_strictCompletionThrough path n).frozenStateAt t =
      path.frozenStateAt t := by
  classical
  let path' := halfExpPP_strictCompletionThrough path n
  have ht_time : t < path.times n := by
    simpa [CTMC.CTMCPath.sojournStart] using ht
  let hex : ∃ m : ℕ, t < path.times m := ⟨n, ht_time⟩
  let m : ℕ := Nat.find hex
  have hm_le_n : m ≤ n := by
    simpa [m, hex] using Nat.find_min' hex ht_time
  have hm_time : t < path.times m := by
    simpa [m, hex] using Nat.find_spec hex
  have hm_time' : t < path'.times m := by
    simpa [path', halfExpPP_strictCompletionThrough, hm_le_n] using hm_time
  have hmin : ∀ j ∈ Finset.range m, ¬ t < path.times j := by
    intro j hj
    exact Nat.find_min hex (Finset.mem_range.mp hj)
  have hmin' : ∀ j ∈ Finset.range m, ¬ t < path'.times j := by
    intro j hj htj
    have hj_le_n : j ≤ n := le_trans (le_of_lt (Finset.mem_range.mp hj)) hm_le_n
    have htj_path : t < path.times j := by
      simpa [path', halfExpPP_strictCompletionThrough, hj_le_n] using htj
    exact hmin j hj htj_path
  have hstate' :
      path'.frozenStateAt t = path'.stateSeq m :=
    path'.frozenStateAt_eq_stateSeq_of_first_time_gt t m hm_time' hmin'
  have hstate :
      path.frozenStateAt t = path.stateSeq m :=
    path.frozenStateAt_eq_stateSeq_of_first_time_gt t m hm_time hmin
  rw [hstate', hstate, halfExpPP_strictCompletionThrough_stateSeq_eq]

private theorem halfExpPP_strictCompletionThrough_frozenMartingalePart_eq_of_lt_succ
    (M : CTMC.DensityDepCTMC 3) (records : M.canonicalRecordΩ)
    (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs_lt : s < (M.canonicalPathMap records).sojournStart (n + 1)) :
    M.frozenMartingalePart M.canonicalPathMap s records =
      M.frozenMartingalePart
        (fun _ : Unit =>
          halfExpPP_strictCompletionThrough (M.canonicalPathMap records) n)
        s Unit.unit := by
  classical
  let path := M.canonicalPathMap records
  let path' := halfExpPP_strictCompletionThrough path n
  have hstate_eq : ∀ t : ℝ, t ≤ s → path'.frozenStateAt t = path.frozenStateAt t := by
    intro t ht
    exact halfExpPP_strictCompletionThrough_frozenStateAt_eq_of_lt_succ
      path n (lt_of_le_of_lt ht hs_lt)
  have hstate_s : path'.frozenStateAt s = path.frozenStateAt s :=
    hstate_eq s le_rfl
  have hstate_0 : path'.frozenStateAt 0 = path.frozenStateAt 0 :=
    hstate_eq 0 hs0
  ext i
  simp only [CTMC.DensityDepCTMC.frozenMartingalePart,
    CTMC.DensityDepCTMC.frozenDensityProcess,
    CTMC.DensityDepCTMC.frozenInitialCondition, Pi.sub_apply]
  have hintegral :
      (∫ t in Set.Icc (0 : ℝ) s,
          (M.rateSpec.drift
            (fun j : Fin 3 => (↑(path.frozenStateAt t j) : ℝ) / ↑M.N)) i) =
        ∫ t in Set.Icc (0 : ℝ) s,
          (M.rateSpec.drift
            (fun j : Fin 3 => (↑(path'.frozenStateAt t j) : ℝ) / ↑M.N)) i := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro t ht
    have ht_le_s : t ≤ s := ht.2
    simpa [hstate_eq t ht_le_s]
  change
      (↑((path.frozenStateAt s i) : ℕ) : ℝ) / ↑M.N -
            (↑((path.frozenStateAt 0 i) : ℕ) : ℝ) / ↑M.N -
          ∫ t in Set.Icc (0 : ℝ) s,
            (M.rateSpec.drift
              (fun j : Fin 3 => (↑(path.frozenStateAt t j) : ℝ) / ↑M.N)) i =
        (↑((path'.frozenStateAt s i) : ℕ) : ℝ) / ↑M.N -
            (↑((path'.frozenStateAt 0 i) : ℕ) : ℝ) / ↑M.N -
          ∫ t in Set.Icc (0 : ℝ) s,
            (M.rateSpec.drift
              (fun j : Fin 3 => (↑(path'.frozenStateAt t j) : ℝ) / ↑M.N)) i
  rw [hstate_s, hstate_0, hintegral]

private theorem halfExpPP_strictCompletionThrough_frozenTimeCompensated_eq
    (M : CTMC.DensityDepCTMC 3)
    (path : CTMC.CTMCPath (Fin 3 → Fin (M.N + 1)))
    (i : Fin 3) (n : ℕ) :
    M.frozenTimeCompensatedJumpMartingale
        (halfExpPP_strictCompletionThrough path n) i n =
      M.frozenTimeCompensatedJumpMartingale path i n := by
  classical
  simp only [CTMC.DensityDepCTMC.frozenTimeCompensatedJumpMartingale]
  have hscaled :
      M.scaledJumpSum (halfExpPP_strictCompletionThrough path n) n i =
        M.scaledJumpSum path n i := by
    simp only [CTMC.DensityDepCTMC.scaledJumpSum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [halfExpPP_strictCompletionThrough_stateSeq_eq,
      halfExpPP_strictCompletionThrough_stateSeq_eq]
  have hsum :
      (∑ k ∈ Finset.range n,
          M.generatorDrift
              ((halfExpPP_strictCompletionThrough path n).stateSeq k) i *
            (halfExpPP_strictCompletionThrough path n).sojournTime k) =
        ∑ k ∈ Finset.range n,
          M.generatorDrift (path.stateSeq k) i * path.sojournTime k := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < n := Finset.mem_range.mp hk
    rw [halfExpPP_strictCompletionThrough_stateSeq_eq,
      halfExpPP_strictCompletionThrough_sojournTime_eq_of_lt path hklt]
  rw [hscaled, hsum]

private theorem halfExpPP_strictCompletionThrough_frozenTimeCompensated_eq_succ
    (M : CTMC.DensityDepCTMC 3)
    (path : CTMC.CTMCPath (Fin 3 → Fin (M.N + 1)))
    (i : Fin 3) (n : ℕ) :
    M.frozenTimeCompensatedJumpMartingale
        (halfExpPP_strictCompletionThrough path n) i (n + 1) =
      M.frozenTimeCompensatedJumpMartingale path i (n + 1) := by
  classical
  let path' := halfExpPP_strictCompletionThrough path n
  have hbase :
      M.frozenTimeCompensatedJumpMartingale path' i n =
        M.frozenTimeCompensatedJumpMartingale path i n := by
    simpa [path'] using
      halfExpPP_strictCompletionThrough_frozenTimeCompensated_eq M path i n
  have hinc' := M.frozenTimeCompensatedJumpMartingale_succ_sub path' i n
  have hinc := M.frozenTimeCompensatedJumpMartingale_succ_sub path i n
  have hinc_eq :
      M.frozenTimeCompensatedJumpMartingale path' i (n + 1) -
          M.frozenTimeCompensatedJumpMartingale path' i n =
        M.frozenTimeCompensatedJumpMartingale path i (n + 1) -
          M.frozenTimeCompensatedJumpMartingale path i n := by
    rw [hinc', hinc]
    have hs0 : path'.stateSeq n = path.stateSeq n := by
      simpa [path'] using
        halfExpPP_strictCompletionThrough_stateSeq_eq path n n
    have hs1 : path'.stateSeq (n + 1) = path.stateSeq (n + 1) := by
      simpa [path'] using
        halfExpPP_strictCompletionThrough_stateSeq_eq path n (n + 1)
    have ht : path'.sojournTime n = path.sojournTime n := by
      simpa [path'] using
        halfExpPP_strictCompletionThrough_sojournTime_eq_of_le path (n := n)
          (m := n) le_rfl
    have hj : path'.jumps n = path.jumps n := by
      simpa [CTMC.CTMCPath.stateSeq_succ] using hs1
    simp [hs0, hj, ht]
  linarith

private theorem halfExpPP_sojournStart_nonneg_of_prefix
    {S : Type*} (path : CTMC.CTMCPath S) (k : ℕ)
    (hpos : 0 < path.times 0)
    (hstrict_prefix : ∀ n < k, path.times n < path.times (n + 1)) :
    0 ≤ path.sojournStart k := by
  cases k with
  | zero =>
      simp [CTMC.CTMCPath.sojournStart]
  | succ k =>
      have hmono : path.times 0 ≤ path.times k := by
        exact halfExpPP_times_le_of_prefix path
          (Nat.zero_le k) (Nat.le_succ k) hstrict_prefix
      simpa [CTMC.CTMCPath.sojournStart] using le_trans (le_of_lt hpos) hmono

private theorem halfExpPP_frozenDensityProcess_at_live_start_eq_scaledState_prefix
    (M : CTMC.DensityDepCTMC 3) (records : M.canonicalRecordΩ)
    (k : ℕ)
    (hstrict_prefix : ∀ n < k,
      (M.canonicalPathMap records).times n <
        (M.canonicalPathMap records).times (n + 1))
    (hpos : 0 < (M.canonicalPathMap records).times 0)
    (hstart_lt_end :
      (M.canonicalPathMap records).sojournStart k <
        (M.canonicalPathMap records).sojournStart (k + 1)) :
    M.frozenDensityProcess M.canonicalPathMap
        ((M.canonicalPathMap records).sojournStart k) records =
      M.scaledState ((M.canonicalPathMap records).stateSeq k) := by
  classical
  let path := M.canonicalPathMap records
  let path' := halfExpPP_strictCompletionThrough path k
  have hcomp := halfExpPP_strictCompletionThrough_strict
    path k hpos hstrict_prefix
  have hstart_eq :
      path'.sojournStart k = path.sojournStart k := by
    simpa [path'] using
      halfExpPP_strictCompletionThrough_sojournStart_eq_of_le path k k le_rfl
  have hmem' :
      path.sojournStart k ∈ path'.sojournInterval k := by
    rw [← hstart_eq]
    cases k with
    | zero =>
        refine ⟨by simp [CTMC.CTMCPath.sojournStart], ?_⟩
        simpa [CTMC.CTMCPath.sojournStart, CTMC.CTMCPath.sojournEnd] using hcomp.1
    | succ k =>
        refine ⟨by simp [CTMC.CTMCPath.sojournStart], ?_⟩
        simpa [CTMC.CTMCPath.sojournStart, CTMC.CTMCPath.sojournEnd] using hcomp.2 k
  have hstate' :
      path'.frozenStateAt (path.sojournStart k) = path'.stateSeq k :=
    halfExpPP_frozenStateAt_eq_stateSeq_of_mem_sojournInterval
      path' hcomp.2 k hmem'
  have hstate_transfer :
      path'.frozenStateAt (path.sojournStart k) =
        path.frozenStateAt (path.sojournStart k) :=
    halfExpPP_strictCompletionThrough_frozenStateAt_eq_of_lt_succ
      path k hstart_lt_end
  have hstate :
      path.frozenStateAt (path.sojournStart k) = path.stateSeq k := by
    rw [← hstate_transfer, hstate',
      halfExpPP_strictCompletionThrough_stateSeq_eq]
  ext i
  simp [CTMC.DensityDepCTMC.frozenDensityProcess,
    CTMC.DensityDepCTMC.scaledState, path, hstate]

private theorem halfExpPP_biUnion_sojournInterval_range_eq_Ico_sojournStart
    {S : Type*} (path : CTMC.CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) (n : ℕ) :
    (⋃ k ∈ Finset.range n, path.sojournInterval k) =
      Set.Ico (0 : ℝ) (path.sojournStart n) := by
  induction n with
  | zero =>
      ext t
      simp
  | succ n ih =>
      ext t
      constructor
      · intro ht
        simp only [Set.mem_iUnion, exists_prop] at ht
        obtain ⟨k, hk, htk⟩ := ht
        have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rcases Nat.lt_or_eq_of_le hk_le with hk_lt | hk_eq
        · have htU : t ∈ ⋃ k ∈ Finset.range n, path.sojournInterval k := by
            simp only [Set.mem_iUnion, exists_prop]
            exact ⟨k, Finset.mem_range.mpr hk_lt, htk⟩
          have htI : t ∈ Set.Ico (0 : ℝ) (path.sojournStart n) := by
            rw [ih] at htU
            exact htU
          have hstart_le_end : path.sojournStart n ≤ path.sojournEnd n := by
            simpa [CTMC.CTMCPath.sojournTime, sub_nonneg] using
              path.sojournTime_nonneg hstrict hpos n
          exact ⟨htI.1, by
            have hlt_end : t < path.sojournEnd n :=
              lt_of_lt_of_le htI.2 hstart_le_end
            simpa [CTMC.CTMCPath.sojournEnd, CTMC.CTMCPath.sojournStart] using hlt_end⟩
        · subst k
          have hstart_nonneg : 0 ≤ path.sojournStart n :=
            path.sojournStart_nonneg hstrict hpos n
          exact ⟨le_trans hstart_nonneg htk.1, by
            simpa [CTMC.CTMCPath.sojournInterval, CTMC.CTMCPath.sojournEnd,
              CTMC.CTMCPath.sojournStart] using htk.2⟩
      · intro ht
        simp only [Set.mem_iUnion, exists_prop]
        by_cases hlt : t < path.sojournStart n
        · have htI : t ∈ Set.Ico (0 : ℝ) (path.sojournStart n) := ⟨ht.1, hlt⟩
          have htU : t ∈ ⋃ k ∈ Finset.range n, path.sojournInterval k := by
            rw [ih]
            exact htI
          simp only [Set.mem_iUnion, exists_prop] at htU
          obtain ⟨k, hk, htk⟩ := htU
          exact ⟨k, Finset.mem_range.mpr
            (Nat.lt_succ_of_lt (Finset.mem_range.mp hk)), htk⟩
        · have hge : path.sojournStart n ≤ t := le_of_not_gt hlt
          have htk : t ∈ path.sojournInterval n := by
            constructor
            · exact hge
            · simpa [CTMC.CTMCPath.sojournInterval, CTMC.CTMCPath.sojournEnd,
                CTMC.CTMCPath.sojournStart] using ht.2
          exact ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), htk⟩

private theorem canonical_positive_sojourn_prefix_strict
    (M : CTMC.DensityDepCTMC d) (records : M.canonicalRecordΩ)
    (hhold_pos : ∀ n,
      ¬M.toQMatrix.IsAbsorbing
          (CTMC.QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) →
        0 < (records (n + 1)).1)
    (hstate_abs : ∀ n,
      M.toQMatrix.IsAbsorbing
          (CTMC.QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) →
        (records (n + 1)).2 =
          CTMC.QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records))
    (hhold_zero : ∀ n,
      M.toQMatrix.IsAbsorbing
          (CTMC.QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) →
        (records (n + 1)).1 = 0)
    {k : ℕ} (hkpos : 0 < (M.canonicalPathMap records).sojournTime k) :
    0 < (M.canonicalPathMap records).times 0 ∧
      ∀ m < k,
        (M.canonicalPathMap records).times m <
          (M.canonicalPathMap records).times (m + 1) := by
  classical
  let path := M.canonicalPathMap records
  have hstate_abs_path : ∀ n,
      M.toQMatrix.IsAbsorbing (path.stateSeq n) →
        path.stateSeq (n + 1) = path.stateSeq n := by
    intro n hn
    have h := hstate_abs n (by
      simpa [path, CTMC.DensityDepCTMC.canonicalPathMap,
        CTMC.QMatrix.currentStateFromHistory_frestrictLe] using hn)
    simpa [path, CTMC.DensityDepCTMC.canonicalPathMap,
      CTMC.QMatrix.recordTrajectoryToPath_stateSeq,
      CTMC.QMatrix.currentStateFromHistory_frestrictLe] using h
  have hhold_zero_path : ∀ n,
      M.toQMatrix.IsAbsorbing (path.stateSeq n) →
        path.sojournTime n = 0 := by
    intro n hn
    have h := hhold_zero n (by
      simpa [path, CTMC.DensityDepCTMC.canonicalPathMap,
        CTMC.QMatrix.currentStateFromHistory_frestrictLe] using hn)
    simpa [path, CTMC.DensityDepCTMC.canonicalPathMap,
      CTMC.QMatrix.recordTrajectoryToPath_sojournTime] using h
  have hsoj_pos_of_le : ∀ j ≤ k, 0 < path.sojournTime j := by
    intro j hjk
    by_contra hnot
    have habs_j : M.toQMatrix.IsAbsorbing (path.stateSeq j) := by
      by_contra hnon
      have hp := hhold_pos j (by
        simpa [path, CTMC.DensityDepCTMC.canonicalPathMap,
          CTMC.QMatrix.currentStateFromHistory_frestrictLe] using hnon)
      have hp_path : 0 < path.sojournTime j := by
        simpa [path, CTMC.DensityDepCTMC.canonicalPathMap,
          CTMC.QMatrix.recordTrajectoryToPath_sojournTime] using hp
      exact hnot hp_path
    have hconst_ge : ∀ n, j ≤ n → path.stateSeq n = path.stateSeq j := by
      intro n hjn
      induction n with
      | zero =>
          have hj0 : j = 0 := Nat.eq_zero_of_le_zero hjn
          subst j
          rfl
      | succ n ih =>
          by_cases hle : j ≤ n
          · have ihn := ih hle
            have habs_n : M.toQMatrix.IsAbsorbing (path.stateSeq n) := by
              simpa [ihn] using habs_j
            simpa [ihn] using hstate_abs_path n habs_n
          · have hj : j = n + 1 := by omega
            subst j
            rfl
    have hconst : path.stateSeq k = path.stateSeq j := hconst_ge k hjk
    have habs_k : M.toQMatrix.IsAbsorbing (path.stateSeq k) := by
      simpa [hconst] using habs_j
    have hzero_k := hhold_zero_path k habs_k
    exact (ne_of_gt hkpos) hzero_k
  constructor
  · have h0 := hsoj_pos_of_le 0 (Nat.zero_le k)
    simpa [path, CTMC.CTMCPath.sojournTime] using h0
  · intro m hm
    have hsucc : 0 < path.sojournTime (m + 1) :=
      hsoj_pos_of_le (m + 1) (Nat.succ_le_of_lt hm)
    simpa [path, CTMC.CTMCPath.sojournTime] using hsucc

private theorem halfExpPP_frozenMartingalePart_sq_le_cell_endpoint_max_of_affine
    (M : CTMC.DensityDepCTMC 3) (T : ℝ) (records : M.canonicalRecordΩ)
    (k : ℕ) (s θ : ℝ) (L : Fin 3 → ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (haff :
      M.frozenMartingalePart M.canonicalPathMap s records =
        (1 - θ) • halfExpPP_clockSkeletonVec M T k records + θ • L) :
    ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2
      ≤ max
          (‖halfExpPP_clockSkeletonVec M T k records‖ ^ 2)
          (‖L‖ ^ 2) := by
  simpa [haff] using
    norm_affine_sq_le_max_sq
      (halfExpPP_clockSkeletonVec M T k records) L hθ0 hθ1

private theorem halfExpPP_clockCellLeftLimit_sq_le_nextSkeleton_add_jumpSq
    (M : CTMC.DensityDepCTMC 3) (T : ℝ) (records : M.canonicalRecordΩ)
    (k : ℕ)
    (hdefect :
      ‖halfExpPP_clockSkeletonVec M T (k + 1) records -
          halfExpPP_clockCellLeftLimit M T k records‖ ^ 2
        ≤ M.truncatedJumpSqIncrementFromHistory T k
          (Preorder.frestrictLe k records) (records (k + 1))) :
    ‖halfExpPP_clockCellLeftLimit M T k records‖ ^ 2
      ≤ (4 / 3 : ℝ) *
          ‖halfExpPP_clockSkeletonVec M T (k + 1) records‖ ^ 2
        + 4 * M.truncatedJumpSqIncrementFromHistory T k
          (Preorder.frestrictLe k records) (records (k + 1)) := by
  let Z := halfExpPP_clockSkeletonVec M T (k + 1) records
  let L := halfExpPP_clockCellLeftLimit M T k records
  have hmain := norm_sub_sq_le_four_thirds_add_four (E := Fin 3 → ℝ) Z (Z - L)
  have hrewrite : Z - (Z - L) = L := by
    ext i
    simp [Z, L]
  have hmain' :
      ‖L‖ ^ 2 ≤ (4 / 3 : ℝ) * ‖Z‖ ^ 2 + 4 * ‖Z - L‖ ^ 2 := by
    simpa [hrewrite] using hmain
  have hdef :
      ‖Z - L‖ ^ 2 ≤ M.truncatedJumpSqIncrementFromHistory T k
          (Preorder.frestrictLe k records) (records (k + 1)) := by
    simpa [Z, L] using hdefect
  nlinarith

private theorem halfExpPP_clockSkeletonVec_eq_frozenTimeCompensated
    (M : CTMC.DensityDepCTMC 3) (T : ℝ) (records : M.canonicalRecordΩ)
    (k : ℕ)
    (hstrict_prefix : ∀ n < k, (M.canonicalPathMap records).times n <
      (M.canonicalPathMap records).times (n + 1))
    (hpos : 0 < (M.canonicalPathMap records).times 0)
    (hstart : (M.canonicalPathMap records).sojournStart k ≤ T) :
    halfExpPP_clockSkeletonVec M T k records =
      fun i : Fin 3 =>
        M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i k := by
  classical
  let path := M.canonicalPathMap records
  ext i
  have hpath :
      halfExpPP_clockSkeletonVec M T k records i =
        M.frozenClockTruncatedMartingale path i T k := by
    simpa [halfExpPP_clockSkeletonVec, path] using
      (M.frozenClockTruncatedMartingale_canonicalPathMap_eq T i k records).symm
  rw [hpath]
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hend_le_T : path.sojournEnd k ≤ T := by
        simpa [CTMC.CTMCPath.sojournEnd, CTMC.CTMCPath.sojournStart] using hstart
      have hstart_le_end : path.sojournStart k ≤ path.sojournEnd k := by
        cases k with
        | zero =>
            simpa [CTMC.CTMCPath.sojournStart, CTMC.CTMCPath.sojournEnd]
              using le_of_lt hpos
        | succ k =>
            have hkstrict : path.times k < path.times (k + 1) :=
              hstrict_prefix k (by omega)
            simpa [CTMC.CTMCPath.sojournStart, CTMC.CTMCPath.sojournEnd]
              using le_of_lt hkstrict
      have hprev : path.sojournStart k ≤ T :=
        le_trans hstart_le_end hend_le_T
      have hpath_prev :
          halfExpPP_clockSkeletonVec M T k records i =
            M.frozenClockTruncatedMartingale path i T k := by
        simpa [halfExpPP_clockSkeletonVec, path] using
          (M.frozenClockTruncatedMartingale_canonicalPathMap_eq T i k records).symm
      have ih' := ih
        (fun n hn => hstrict_prefix n (Nat.lt_trans hn (Nat.lt_succ_self k)))
        hprev hpath_prev
      have hsoj_le :
          path.sojournTime k ≤ max 0 (T - path.sojournStart k) := by
        rw [max_eq_right]
        · simp only [CTMC.CTMCPath.sojournTime]
          linarith
        · linarith
      have hmin :
          min (path.sojournTime k) (max 0 (T - path.sojournStart k)) =
            path.sojournTime k := min_eq_left hsoj_le
      have htrunc :
          M.truncatedCenteredCoordIncrement (path.stateSeq k) i
              (max 0 (T - path.sojournStart k))
              (path.sojournTime k, path.stateSeq (k + 1)) =
            (M.scaledState (path.stateSeq (k + 1)) -
                M.scaledState (path.stateSeq k)) i -
              M.generatorDrift (path.stateSeq k) i * path.sojournTime k := by
        simp [CTMC.DensityDepCTMC.truncatedCenteredCoordIncrement, hsoj_le, hmin]
      have htime_sub :=
        M.frozenTimeCompensatedJumpMartingale_succ_sub path i k
      calc
        M.frozenClockTruncatedMartingale path i T (k + 1)
            = M.frozenClockTruncatedMartingale path i T k +
                M.truncatedCenteredCoordIncrement (path.stateSeq k) i
                  (max 0 (T - path.sojournStart k))
                  (path.sojournTime k, path.stateSeq (k + 1)) := by
                rw [M.frozenClockTruncatedMartingale_succ]
        _ = M.frozenTimeCompensatedJumpMartingale path i k +
              ((M.scaledState (path.stateSeq (k + 1)) -
                  M.scaledState (path.stateSeq k)) i -
                M.generatorDrift (path.stateSeq k) i * path.sojournTime k) := by
                rw [ih', htrunc]
        _ = M.frozenTimeCompensatedJumpMartingale path i (k + 1) := by
                linarith

private theorem halfExpPP_clockSkeletonVec_eq_frozenTimeCompensated_weak
    (M : CTMC.DensityDepCTMC 3) (T : ℝ) (records : M.canonicalRecordΩ)
    (k : ℕ)
    (hstrict_prefix : ∀ n, n + 1 < k →
      (M.canonicalPathMap records).times n <
        (M.canonicalPathMap records).times (n + 1))
    (hpos : 0 < (M.canonicalPathMap records).times 0)
    (hstart : (M.canonicalPathMap records).sojournStart k ≤ T) :
    halfExpPP_clockSkeletonVec M T k records =
      fun i : Fin 3 =>
        M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i k := by
  classical
  let path := M.canonicalPathMap records
  ext i
  have hpath :
      halfExpPP_clockSkeletonVec M T k records i =
        M.frozenClockTruncatedMartingale path i T k := by
    simpa [halfExpPP_clockSkeletonVec, path] using
      (M.frozenClockTruncatedMartingale_canonicalPathMap_eq T i k records).symm
  rw [hpath]
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hend_le_T : path.sojournEnd k ≤ T := by
        simpa [CTMC.CTMCPath.sojournEnd, CTMC.CTMCPath.sojournStart] using hstart
      have hstart_le_end : path.sojournStart k ≤ path.sojournEnd k := by
        cases k with
        | zero =>
            simpa [CTMC.CTMCPath.sojournStart, CTMC.CTMCPath.sojournEnd]
              using le_of_lt hpos
        | succ k =>
            have hkstrict : path.times k < path.times (k + 1) :=
              hstrict_prefix k (by omega)
            simpa [CTMC.CTMCPath.sojournStart, CTMC.CTMCPath.sojournEnd]
              using le_of_lt hkstrict
      have hprev : path.sojournStart k ≤ T :=
        le_trans hstart_le_end hend_le_T
      have hpath_prev :
          halfExpPP_clockSkeletonVec M T k records i =
            M.frozenClockTruncatedMartingale path i T k := by
        simpa [halfExpPP_clockSkeletonVec, path] using
          (M.frozenClockTruncatedMartingale_canonicalPathMap_eq T i k records).symm
      have ih' := ih
        (fun n hn => hstrict_prefix n (Nat.lt_trans hn (Nat.lt_succ_self k)))
        hprev hpath_prev
      have hsoj_le :
          path.sojournTime k ≤ max 0 (T - path.sojournStart k) := by
        rw [max_eq_right]
        · simp only [CTMC.CTMCPath.sojournTime]
          linarith
        · linarith
      have hmin :
          min (path.sojournTime k) (max 0 (T - path.sojournStart k)) =
            path.sojournTime k := min_eq_left hsoj_le
      have htrunc :
          M.truncatedCenteredCoordIncrement (path.stateSeq k) i
              (max 0 (T - path.sojournStart k))
              (path.sojournTime k, path.stateSeq (k + 1)) =
            (M.scaledState (path.stateSeq (k + 1)) -
                M.scaledState (path.stateSeq k)) i -
              M.generatorDrift (path.stateSeq k) i * path.sojournTime k := by
        simp [CTMC.DensityDepCTMC.truncatedCenteredCoordIncrement, hsoj_le, hmin]
      have htime_sub :=
        M.frozenTimeCompensatedJumpMartingale_succ_sub path i k
      calc
        M.frozenClockTruncatedMartingale path i T (k + 1)
            = M.frozenClockTruncatedMartingale path i T k +
                M.truncatedCenteredCoordIncrement (path.stateSeq k) i
                  (max 0 (T - path.sojournStart k))
                  (path.sojournTime k, path.stateSeq (k + 1)) := by
                rw [M.frozenClockTruncatedMartingale_succ]
        _ = M.frozenTimeCompensatedJumpMartingale path i k +
              ((M.scaledState (path.stateSeq (k + 1)) -
                  M.scaledState (path.stateSeq k)) i -
                M.generatorDrift (path.stateSeq k) i * path.sojournTime k) := by
                rw [ih', htrunc]
        _ = M.frozenTimeCompensatedJumpMartingale path i (k + 1) := by
                linarith

private theorem integral_sum_truncatedJumpSq_eq_integral_sum_clockTruncatedQV
    (M : CTMC.DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (n : ℕ) :
    ∫ records,
        (∑ k ∈ Finset.range n,
          M.truncatedJumpSqIncrementFromHistory T k
            (Preorder.frestrictLe k records) (records (k + 1)))
        ∂M.canonicalRecordMeasure x₀ =
      ∫ records,
        (∑ k ∈ Finset.range n,
          (let hist := Preorder.frestrictLe k records
           let x : Fin d → Fin (M.N + 1) :=
            CTMC.QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) k hist
           M.instantQVRate x *
            min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist)))
        ∂M.canonicalRecordMeasure x₀ := by
  exact (M.integral_sum_truncatedJumpSqIncrement_eq_sum_clockQVIntegral
    x₀ T n).trans
      (M.integral_sum_clockTruncatedQVIncrement_eq_sum_clockQVIntegral
        x₀ T n).symm

private theorem integral_sum_clockTruncatedQV_eq_sum_integral
    (M : CTMC.DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (n : ℕ) :
    ∫ records,
        (∑ k ∈ Finset.range n,
          (let hist := Preorder.frestrictLe k records
           let x : Fin d → Fin (M.N + 1) :=
            CTMC.QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) k hist
           M.instantQVRate x *
            min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist)))
        ∂M.canonicalRecordMeasure x₀ =
      ∑ k ∈ Finset.range n,
        ∫ records,
          (let hist := Preorder.frestrictLe k records
           let x : Fin d → Fin (M.N + 1) :=
            CTMC.QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) k hist
           M.instantQVRate x *
            min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist))
          ∂M.canonicalRecordMeasure x₀ := by
  rw [MeasureTheory.integral_finset_sum]
  intro k _hk
  exact M.integrable_clockTruncatedQVIncrement x₀ T k

private theorem instantQVRate_pos_of_nonabsorbing
    (M : CTMC.DensityDepCTMC d) {x : Fin d → Fin (M.N + 1)}
    (h : ¬M.toQMatrix.IsAbsorbing x) :
    0 < M.instantQVRate x := by
  have hexit : 0 < M.exitRateAt x :=
    M.toQMatrix.exitRate_pos_of_nonabsorbing h
  have hsum : 0 < ∑ y : Fin d → Fin (M.N + 1), M.offDiagRate x y := by
    simpa [CTMC.DensityDepCTMC.sum_offDiagRate_eq_exitRateAt] using hexit
  obtain ⟨y, _hy_mem, hy_pos⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (s := Finset.univ)
      (f := fun y : Fin d → Fin (M.N + 1) => M.offDiagRate x y)
      (fun y _ => M.offDiagRate_nonneg x y)).mp hsum
  have hxy : x ≠ y := by
    intro hxy
    have hz : M.offDiagRate x y = 0 := by
      simp [CTMC.DensityDepCTMC.offDiagRate, hxy]
    linarith
  have hscaled_ne : M.scaledState y ≠ M.scaledState x := by
    intro hscaled
    apply hxy
    ext i
    have hi := congr_fun hscaled i
    have hNpos : (0 : ℝ) < M.N := Nat.cast_pos.mpr M.hN
    simp [CTMC.DensityDepCTMC.scaledState] at hi
    field_simp [ne_of_gt hNpos] at hi
    exact_mod_cast hi.symm
  have hnorm_pos : 0 < ‖M.scaledState y - M.scaledState x‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hscaled_ne)
  simp only [CTMC.DensityDepCTMC.instantQVRate]
  refine Finset.sum_pos' ?nonneg ?pos
  · intro z _hz
    exact mul_nonneg (M.offDiagRate_nonneg x z)
      (sq_nonneg ‖M.scaledState z - M.scaledState x‖)
  · exact ⟨y, Finset.mem_univ y,
      mul_pos hy_pos (sq_pos_of_pos hnorm_pos)⟩

private theorem frozenQV_energy_pos_of_first_holding
    (M : CTMC.DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1))
    (records : M.canonicalRecordΩ) {T : ℝ} (hT : 0 < T)
    (hrecord0_state : (records 0).2 = x₀)
    (hhold : 0 < (records 1).1)
    (hqv0 : 0 < M.instantQVRate x₀) :
    0 < ∫ s in Set.Icc (0 : ℝ) T,
      M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s) := by
  let τ : ℝ := (records 1).1
  let δ : ℝ := min T τ / 2
  have hmin_pos : 0 < min T τ := lt_min hT hhold
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    linarith
  have hδ_le_T : δ ≤ T := by
    have hmin_le : min T τ ≤ T := min_le_left T τ
    dsimp [δ]
    linarith
  have hδ_lt_τ : δ < τ := by
    have hmin_le : min T τ ≤ τ := min_le_right T τ
    dsimp [δ]
    linarith
  let f : ℝ → ℝ := fun s =>
    M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s)
  have hf_meas : Measurable f := by
    have hpair : Measurable (fun s : ℝ => (s, records)) :=
      Measurable.prodMk measurable_id measurable_const
    exact (Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) => M.instantQVRate x)).comp
        (M.measurable_prod_canonicalPathMap_frozenStateAt.comp hpair)
  obtain ⟨C, _hC_pos, hC⟩ := M.exists_instantQVRate_bound
  have hf_int : MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) T)
      MeasureTheory.volume := by
    refine MeasureTheory.IntegrableOn.of_bound measure_Icc_lt_top
      hf_meas.aestronglyMeasurable (C / (M.N : ℝ)) ?_
    filter_upwards with s
    rw [Real.norm_eq_abs, abs_of_nonneg (M.instantQVRate_nonneg _)]
    exact hC _
  have hf_nonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)] f := by
    filter_upwards with s
    exact M.instantQVRate_nonneg _
  have hsubset :
      Set.Icc (0 : ℝ) δ ⊆ Function.support f ∩ Set.Icc (0 : ℝ) T := by
    intro s hs
    have hs_lt_τ : s < τ := lt_of_le_of_lt hs.2 hδ_lt_τ
    have hs_time : s < (M.canonicalPathMap records).times 0 := by
      simpa [τ, CTMC.DensityDepCTMC.canonicalPathMap,
        CTMC.QMatrix.recordTrajectoryToPath_times_zero] using hs_lt_τ
    have hstate : (M.canonicalPathMap records).frozenStateAt s = x₀ := by
      rw [(M.canonicalPathMap records).frozenStateAt_before_first s hs_time]
      simpa [CTMC.DensityDepCTMC.canonicalPathMap,
        CTMC.QMatrix.recordTrajectoryToPath_init] using hrecord0_state
    have hf_pos : 0 < f s := by
      simpa [f, hstate] using hqv0
    exact ⟨ne_of_gt hf_pos, ⟨hs.1, le_trans hs.2 hδ_le_T⟩⟩
  have hvol_real :
      MeasureTheory.volume.real (Set.Icc (0 : ℝ) δ) = δ := by
    rw [_root_.MeasureTheory.Measure.real_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ δ - 0)]
    ring
  have hvol_pos : 0 < MeasureTheory.volume (Set.Icc (0 : ℝ) δ) := by
    have hreal_pos : 0 < MeasureTheory.volume.real (Set.Icc (0 : ℝ) δ) := by
      rw [hvol_real]
      exact hδ_pos
    have hfinite : MeasureTheory.volume (Set.Icc (0 : ℝ) δ) ≠ ⊤ :=
      ne_of_lt measure_Icc_lt_top
    have hne : MeasureTheory.volume (Set.Icc (0 : ℝ) δ) ≠ 0 :=
      (MeasureTheory.measureReal_ne_zero_iff hfinite).mp hreal_pos.ne'
    exact lt_of_le_of_ne zero_le' (Ne.symm hne)
  have hsupport_pos :
      0 < MeasureTheory.volume (Function.support f ∩ Set.Icc (0 : ℝ) T) :=
    lt_of_lt_of_le hvol_pos (_root_.MeasureTheory.measure_mono hsubset)
  simpa [f] using
    (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hf_nonneg hf_int).2
      hsupport_pos

private theorem halfExpPP_frozenQV_energy_expectation_pos_of_nonabsorbing
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1))
    (_hinit : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x₀)
    {T : ℝ} (hT : 0 < T)
    (hNonabs :
      ¬(CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing x₀) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    0 < ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
      M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
      ∂M.canonicalRecordMeasure x₀ := by
  let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  let μ := M.canonicalRecordMeasure x₀
  let energy : M.canonicalRecordΩ → ℝ := fun records =>
    ∫ s in Set.Icc (0 : ℝ) T,
      M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s)
  have henergy_nonneg : 0 ≤ᵐ[μ] energy := by
    filter_upwards with records
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun s _hs =>
      M.instantQVRate_nonneg _
  have henergy_meas : Measurable energy := by
    simpa [energy, M] using measurable_canonicalFrozenInstantQVRate_setIntegral M T
  obtain ⟨C, _hC_pos, hC⟩ := M.exists_instantQVRate_bound
  have hpointwise : ∀ records : M.canonicalRecordΩ,
      energy records ≤ C / (M.N : ℝ) * T := by
    intro records
    have h_vol : MeasureTheory.volume.real (Set.Icc (0 : ℝ) T) = T := by
      rw [_root_.MeasureTheory.Measure.real_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ T - 0)]
      ring
    calc
      energy records
          ≤ ‖energy records‖ := le_abs_self _
      _ ≤ C / (M.N : ℝ) * MeasureTheory.volume.real (Set.Icc (0 : ℝ) T) :=
          MeasureTheory.norm_setIntegral_le_of_norm_le_const
            measure_Icc_lt_top (fun s _hs => by
              rw [Real.norm_eq_abs, abs_of_nonneg (M.instantQVRate_nonneg _)]
              exact hC _)
      _ = C / (M.N : ℝ) * T := by rw [h_vol]
  have hconst_nonneg : 0 ≤ C / (M.N : ℝ) * T := by positivity
  have henergy_int : MeasureTheory.Integrable energy μ := by
    refine (MeasureTheory.integrable_const (C / (M.N : ℝ) * T)).mono'
      henergy_meas.aestronglyMeasurable ?_
    filter_upwards with records
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ energy records by
      exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun s _hs =>
        M.instantQVRate_nonneg _)]
    exact hpointwise records
  have hqv0 : 0 < M.instantQVRate x₀ :=
    instantQVRate_pos_of_nonabsorbing M hNonabs
  have henergy_pos_ae : ∀ᵐ records ∂μ, 0 < energy records := by
    filter_upwards
      [M.toQMatrix.canonicalRecordMeasure_record_zero_eq_init_ae x₀,
        M.toQMatrix.canonicalRecordMeasure_all_next_holdingTime_pos_ae_of_nonabsorbing x₀]
      with records hrecord0 hpos
    have hrecord0_state : (records 0).2 = x₀ := by
      simpa using congrArg Prod.snd hrecord0
    have hcur0 :
        CTMC.QMatrix.currentStateFromHistory
            (S := Fin 3 → Fin (N + 1)) 0 (Preorder.frestrictLe 0 records) = x₀ := by
      simpa [CTMC.QMatrix.currentStateFromHistory] using hrecord0_state
    have hhold : 0 < (records 1).1 :=
      hpos 0 (by simpa [hcur0, M] using hNonabs)
    simpa [energy] using
      frozenQV_energy_pos_of_first_holding M x₀ records hT hrecord0_state hhold hqv0
  have hsupport_pos : 0 < μ (Function.support energy) := by
    have hfreq : ∃ᵐ records ∂μ, energy records ≠ 0 :=
      henergy_pos_ae.frequently.mono fun _ hpos => ne_of_gt hpos
    have hne : μ {records | energy records ≠ 0} ≠ 0 :=
      MeasureTheory.frequently_ae_iff.mp hfreq
    exact lt_of_le_of_ne zero_le' (Ne.symm (by simpa [Function.support] using hne))
  exact (MeasureTheory.integral_pos_iff_support_of_nonneg_ae
    henergy_nonneg henergy_int).2 hsupport_pos

/-- Residual stochastic input: uniform continuous-time Doob L2 estimate for
the frozen martingale of this concrete absorbing PP. -/
def halfExpPPFrozenDoobL2 (A : ℝ) : Prop :=
  ∀ (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1))
    (_hinit : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x₀),
    ∀ T > 0,
      let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      A * ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
        ∂M.canonicalRecordMeasure x₀

/-- Endpoint bridge for the concrete frozen half-`exp` protocol: at completed
sojourn boundaries the frozen residual is exactly the clock-time compensated
jump martingale. -/
private theorem halfExpPP_frozenMartingalePart_at_sojournStart_eq_frozenTimeCompensated
    (N : ℕ) (hN : 0 < N)
    (path : CTMC.CTMCPath (Fin 3 → Fin (N + 1)))
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) (n : ℕ)
    (hseq :
      ∀ k < n,
        (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex
          (path.stateSeq k)) :
    let M : CTMC.DensityDepCTMC 3 :=
      CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    M.frozenMartingalePart (fun _ : Unit => path) (path.sojournStart n) Unit.unit =
      fun i => M.frozenTimeCompensatedJumpMartingale path i n := by
  let M : CTMC.DensityDepCTMC 3 :=
    CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  have hBC : M.BoundaryCompatibleOnSimplex := by
    simpa [M] using halfExpPP_boundaryCompatibleOnSimplex N hN
  have hDrift : ∀ k < n,
      M.generatorDrift (path.stateSeq k) =
        M.rateSpec.drift (M.scaledState (path.stateSeq k)) := by
    intro k hk
    exact M.generatorDrift_eq_rateSpec_drift_of_boundaryCompatibleOnSimplex
      hBC (by simpa [M] using hseq k hk)
  simpa [M] using
    M.frozenMartingalePart_at_sojournStart_eq_frozenTimeCompensated
      path hstrict hpos n hDrift

private theorem halfExpPP_clockCellLeftLimit_eq_skeleton_sub_drift
    (N : ℕ) (hN : 0 < N) (T : ℝ)
    (records :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordΩ)
    (k : ℕ)
    (hstrict : ∀ n,
      (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).times n <
      ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).times (n + 1)))
    (hpos :
      0 < ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).times 0)
    (hseq :
      ∀ m ≤ k,
        (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex
          (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
            records).stateSeq m))
    (hstart_lt_end :
      ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).sojournStart k <
      ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).sojournStart (k + 1))
    (hstart_le_T :
      ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).sojournStart k ≤ T) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    let path := M.canonicalPathMap records
    halfExpPP_clockCellLeftLimit M T k records =
      halfExpPP_clockSkeletonVec M T k records -
        (min T (path.sojournStart (k + 1)) - path.sojournStart k) •
          M.generatorDrift (path.stateSeq k) := by
  classical
  let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  let path := M.canonicalPathMap records
  have hseq_lt : ∀ m < k, M.InSimplex (path.stateSeq m) := by
    intro m hm
    exact hseq m (le_of_lt hm)
  have hseq_k : M.InSimplex (path.stateSeq k) := hseq k le_rfl
  have hEndpoint :
      M.frozenMartingalePart M.canonicalPathMap (path.sojournStart k) records =
        halfExpPP_clockSkeletonVec M T k records := by
    have hstart_eq :=
      halfExpPP_frozenMartingalePart_at_sojournStart_eq_frozenTimeCompensated
        N hN path hstrict hpos k hseq_lt
    have hskel :=
      halfExpPP_clockSkeletonVec_eq_frozenTimeCompensated
        M T records k (fun n _hn => hstrict n) hpos hstart_le_T
    exact hstart_eq.trans hskel.symm
  have hdensity :
      M.frozenDensityProcess M.canonicalPathMap (path.sojournStart k) records =
        M.scaledState (path.stateSeq k) := by
    exact
      halfExpPP_frozenDensityProcess_at_live_start_eq_scaledState
        M records k hstrict hstart_lt_end
  have hBC : M.BoundaryCompatibleOnSimplex := by
    simpa [M] using halfExpPP_boundaryCompatibleOnSimplex N hN
  have hdrift :
      M.rateSpec.drift
          (M.frozenDensityProcess M.canonicalPathMap (path.sojournStart k) records) =
        M.generatorDrift (path.stateSeq k) := by
    rw [hdensity]
    exact
      (M.generatorDrift_eq_rateSpec_drift_of_boundaryCompatibleOnSimplex
        hBC hseq_k).symm
  ext i
  simp only [halfExpPP_clockCellLeftLimit, Pi.sub_apply, Pi.smul_apply]
  rw [hEndpoint]
  rw [show
      (M.rateSpec.drift
          (M.frozenDensityProcess M.canonicalPathMap (path.sojournStart k) records)) i =
        M.generatorDrift (path.stateSeq k) i from congr_fun hdrift i]

private theorem halfExpPP_clockCellLeftLimit_eq_skeleton_sub_drift_prefix
    (N : ℕ) (hN : 0 < N) (T : ℝ)
    (records :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordΩ)
    (k : ℕ)
    (hstrict_prefix : ∀ n < k,
      (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).times n <
      ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).times (n + 1)))
    (hpos :
      0 < ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).times 0)
    (hseq :
      ∀ m ≤ k,
        (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex
          (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
            records).stateSeq m))
    (hstart_lt_end :
      ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).sojournStart k <
      ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).sojournStart (k + 1))
    (hstart_le_T :
      ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).sojournStart k ≤ T) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    let path := M.canonicalPathMap records
    halfExpPP_clockCellLeftLimit M T k records =
      halfExpPP_clockSkeletonVec M T k records -
        (min T (path.sojournStart (k + 1)) - path.sojournStart k) •
          M.generatorDrift (path.stateSeq k) := by
  classical
  let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  let path := M.canonicalPathMap records
  let path' := halfExpPP_strictCompletionThrough path k
  have hcomp := halfExpPP_strictCompletionThrough_strict
    path k hpos hstrict_prefix
  have hs0 : 0 ≤ path.sojournStart k :=
    halfExpPP_sojournStart_nonneg_of_prefix path k hpos hstrict_prefix
  have hstart_eq :
      path'.sojournStart k = path.sojournStart k := by
    simpa [path'] using
      halfExpPP_strictCompletionThrough_sojournStart_eq_of_le path k k le_rfl
  have hseq_lt' :
      ∀ m < k, M.InSimplex (path'.stateSeq m) := by
    intro m hm
    have hstate :
        path'.stateSeq m = path.stateSeq m := by
      simpa [path'] using
        halfExpPP_strictCompletionThrough_stateSeq_eq path k m
    simpa [path', hstate] using hseq m (le_of_lt hm)
  have hEndpoint' :
      M.frozenMartingalePart (fun _ : Unit => path')
          (path.sojournStart k) Unit.unit =
        fun i : Fin 3 =>
          M.frozenTimeCompensatedJumpMartingale path' i k := by
    have h :=
      halfExpPP_frozenMartingalePart_at_sojournStart_eq_frozenTimeCompensated
        N hN path' hcomp.2 hcomp.1 k (by simpa [M] using hseq_lt')
    simpa [M, path', hstart_eq] using h
  have hEndpointTransfer :
      M.frozenMartingalePart M.canonicalPathMap (path.sojournStart k) records =
        M.frozenMartingalePart (fun _ : Unit => path')
          (path.sojournStart k) Unit.unit :=
    halfExpPP_strictCompletionThrough_frozenMartingalePart_eq_of_lt_succ
      M records k hs0 hstart_lt_end
  have hskel :
      halfExpPP_clockSkeletonVec M T k records =
        fun i : Fin 3 =>
          M.frozenTimeCompensatedJumpMartingale path i k := by
    simpa [M, path] using
      halfExpPP_clockSkeletonVec_eq_frozenTimeCompensated
        M T records k hstrict_prefix hpos hstart_le_T
  have hEndpoint :
      M.frozenMartingalePart M.canonicalPathMap (path.sojournStart k) records =
        halfExpPP_clockSkeletonVec M T k records := by
    calc
      M.frozenMartingalePart M.canonicalPathMap (path.sojournStart k) records
          = M.frozenMartingalePart (fun _ : Unit => path')
              (path.sojournStart k) Unit.unit := hEndpointTransfer
      _ = (fun i : Fin 3 =>
            M.frozenTimeCompensatedJumpMartingale path' i k) := hEndpoint'
      _ = (fun i : Fin 3 =>
            M.frozenTimeCompensatedJumpMartingale path i k) := by
            ext i
            exact halfExpPP_strictCompletionThrough_frozenTimeCompensated_eq
              M path i k
      _ = halfExpPP_clockSkeletonVec M T k records := hskel.symm
  have hdensity :
      M.frozenDensityProcess M.canonicalPathMap (path.sojournStart k) records =
        M.scaledState (path.stateSeq k) := by
    exact
      halfExpPP_frozenDensityProcess_at_live_start_eq_scaledState_prefix
        M records k hstrict_prefix hpos hstart_lt_end
  have hBC : M.BoundaryCompatibleOnSimplex := by
    simpa [M] using halfExpPP_boundaryCompatibleOnSimplex N hN
  have hdrift :
      M.rateSpec.drift
          (M.frozenDensityProcess M.canonicalPathMap (path.sojournStart k) records) =
        M.generatorDrift (path.stateSeq k) := by
    rw [hdensity]
    exact
      (M.generatorDrift_eq_rateSpec_drift_of_boundaryCompatibleOnSimplex
        hBC (hseq k le_rfl)).symm
  ext i
  simp only [halfExpPP_clockCellLeftLimit, Pi.sub_apply, Pi.smul_apply]
  rw [hEndpoint]
  rw [show
      (M.rateSpec.drift
          (M.frozenDensityProcess M.canonicalPathMap (path.sojournStart k) records)) i =
        M.generatorDrift (path.stateSeq k) i from congr_fun hdrift i]

private theorem halfExpPP_min_T_next_sojournStart_sub_eq_min_sojournTime_remaining
    {S : Type*} (path : CTMC.CTMCPath S) (T : ℝ) (k : ℕ)
    (hstart_le_T : path.sojournStart k ≤ T) :
    min T (path.sojournStart (k + 1)) - path.sojournStart k =
      min (path.sojournTime k) (max 0 (T - path.sojournStart k)) := by
  have hnext_sub :
      path.sojournStart (k + 1) - path.sojournStart k =
        path.sojournTime k := by
    cases k <;> simp [CTMC.CTMCPath.sojournTime]
  have hrem_nonneg : 0 ≤ T - path.sojournStart k := by
    linarith
  rw [max_eq_right hrem_nonneg]
  by_cases hnext_le_T : path.sojournStart (k + 1) ≤ T
  · have hsoj_le : path.sojournTime k ≤ T - path.sojournStart k := by
      linarith
    rw [min_eq_right hnext_le_T, min_eq_left hsoj_le]
    exact hnext_sub
  · have hT_le_next : T ≤ path.sojournStart (k + 1) :=
      le_of_lt (lt_of_not_ge hnext_le_T)
    have hrem_le_soj : T - path.sojournStart k ≤ path.sojournTime k := by
      linarith
    rw [min_eq_left hT_le_next, min_eq_right hrem_le_soj]

private theorem sum_range_le_prefix_of_nonneg_zero_tail
    {f : ℕ → ℝ} (n a : ℕ)
    (hnonneg : ∀ k, 0 ≤ f k)
    (hzero_tail : ∀ k, a ≤ k → f k = 0) :
    (∑ k ∈ Finset.range n, f k) ≤ ∑ k ∈ Finset.range a, f k := by
  classical
  by_cases hna : n ≤ a
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro k hk
        exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hna))
      (by
        intro k _hk _hnot
        exact hnonneg k)
  · have han : a ≤ n := le_of_not_ge hna
    have hsplit :
        (∑ k ∈ Finset.range n, f k) =
          ∑ k ∈ (Finset.range n).filter (fun k => k < a), f k := by
      symm
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro k _hk
      by_cases hka : k < a
      · simp [hka]
      · have hak : a ≤ k := le_of_not_gt hka
        simp [hka, hzero_tail k hak]
    have hfilter :
        (Finset.range n).filter (fun k => k < a) = Finset.range a := by
      ext k
      constructor
      · intro hk
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
      · intro hk
        have hka : k < a := Finset.mem_range.mp hk
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (lt_of_lt_of_le hka han), hka⟩
    rw [hsplit, hfilter]

private theorem frozenClockTruncatedQV_sum_jumpCount_succ_eq_setIntegral
    (M : CTMC.DensityDepCTMC d)
    (path : CTMC.CTMCPath (Fin d → Fin (M.N + 1)))
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) {T : ℝ} (hT : 0 ≤ T)
    (hfuture : ∃ n, T < path.times n) :
    (∑ k ∈ Finset.range (path.jumpCount T + 1),
        M.instantQVRate (path.stateSeq k) *
          min (path.sojournTime k) (max 0 (T - path.sojournStart k))) =
      ∫ t in Set.Icc (0 : ℝ) T,
        M.instantQVRate (path.frozenStateAt t) := by
  classical
  let j := path.jumpCount T
  let F : (Fin d → Fin (M.N + 1)) → ℝ := fun x => M.instantQVRate x
  have hcompleted :
      (∑ k ∈ Finset.range j,
          M.instantQVRate (path.stateSeq k) *
            min (path.sojournTime k) (max 0 (T - path.sojournStart k))) =
        ∑ k ∈ Finset.range j,
          M.instantQVRate (path.stateSeq k) * path.sojournTime k := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < j := Finset.mem_range.mp hk
    have hend : path.sojournEnd k ≤ T := by
      simpa [CTMC.CTMCPath.sojournEnd, j] using
        path.times_le_of_lt_jumpCount hfuture hklt
    have hstart_le_end : path.sojournStart k ≤ path.sojournEnd k := by
      simpa [CTMC.CTMCPath.sojournTime, sub_nonneg] using
        path.sojournTime_nonneg hstrict hpos k
    have hT_start_nonneg : 0 ≤ T - path.sojournStart k := by
      linarith
    have hsoj_le :
        path.sojournTime k ≤ max 0 (T - path.sojournStart k) := by
      rw [max_eq_right hT_start_nonneg]
      simp only [CTMC.CTMCPath.sojournTime]
      linarith
    rw [min_eq_left hsoj_le]
  have hstart_j_le : path.sojournStart j ≤ T := by
    simpa [j] using path.sojournStart_jumpCount_le_of_exists hT hfuture
  have helapsed_nonneg : 0 ≤ T - path.sojournStart j := by
    linarith
  have hclock_j :
      max 0 (T - path.sojournStart j) = path.currentSojournElapsed T := by
    simp [CTMC.CTMCPath.currentSojournElapsed, j, max_eq_right helapsed_nonneg]
  have hcur_le :
      path.currentSojournElapsed T ≤ path.sojournTime j :=
    path.currentSojournElapsed_le_sojournTime hfuture
  have hmin_cur :
      min (path.sojournTime j) (max 0 (T - path.sojournStart j)) =
        path.currentSojournElapsed T := by
    rw [hclock_j]
    exact min_eq_right hcur_le
  have hclock :=
    M.frozen_sum_observable_mul_sojournTime_add_currentSojourn_eq_setIntegral
      path hstrict hpos F hT hfuture
  calc
    (∑ k ∈ Finset.range (path.jumpCount T + 1),
        M.instantQVRate (path.stateSeq k) *
          min (path.sojournTime k) (max 0 (T - path.sojournStart k)))
        =
      (∑ k ∈ Finset.range j,
          M.instantQVRate (path.stateSeq k) *
            min (path.sojournTime k) (max 0 (T - path.sojournStart k))) +
        M.instantQVRate (path.stateSeq j) *
          min (path.sojournTime j) (max 0 (T - path.sojournStart j)) := by
          simp [j, Finset.sum_range_succ]
    _ =
      (∑ k ∈ Finset.range j,
          M.instantQVRate (path.stateSeq k) * path.sojournTime k) +
        M.instantQVRate (path.stateSeq j) *
          path.currentSojournElapsed T := by
          rw [hcompleted, hmin_cur]
    _ =
      (∑ k ∈ Finset.range (path.jumpCount T),
          F (path.stateSeq k) * path.sojournTime k) +
        F (path.stateSeq (path.jumpCount T)) *
          path.currentSojournElapsed T := by
          simp [F, j]
    _ = ∫ t in Set.Icc (0 : ℝ) T,
        M.instantQVRate (path.frozenStateAt t) := by
          simpa [F] using hclock

private theorem frozenClockTruncatedQV_sum_range_le_setIntegral
    (M : CTMC.DensityDepCTMC d)
    (path : CTMC.CTMCPath (Fin d → Fin (M.N + 1)))
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) {T : ℝ} (hT : 0 ≤ T)
    (hfuture : ∃ n, T < path.times n) (n : ℕ) :
    (∑ k ∈ Finset.range n,
        M.instantQVRate (path.stateSeq k) *
          min (path.sojournTime k) (max 0 (T - path.sojournStart k))) ≤
      ∫ t in Set.Icc (0 : ℝ) T,
        M.instantQVRate (path.frozenStateAt t) := by
  classical
  let j := path.jumpCount T
  let f : ℕ → ℝ := fun k =>
    M.instantQVRate (path.stateSeq k) *
      min (path.sojournTime k) (max 0 (T - path.sojournStart k))
  have hnonneg : ∀ k, 0 ≤ f k := by
    intro k
    dsimp [f]
    exact mul_nonneg (M.instantQVRate_nonneg _)
      (le_min (path.sojournTime_nonneg hstrict hpos k) (le_max_left _ _))
  have hzero_tail : ∀ k, j + 1 ≤ k → f k = 0 := by
    intro k hk
    have hj_lt_k : j < k := Nat.lt_of_succ_le hk
    have hT_lt_start : T < path.sojournStart k := by
      have hT_lt_end_j : T < path.sojournEnd j := by
        simpa [CTMC.CTMCPath.sojournEnd, j] using
          path.lt_times_jumpCount_of_exists hfuture
      have hend_le_start :
          path.sojournEnd j ≤ path.sojournStart k :=
        path.sojournEnd_le_sojournStart_of_lt hstrict hj_lt_k
      exact lt_of_lt_of_le hT_lt_end_j hend_le_start
    have hrem_nonpos : T - path.sojournStart k ≤ 0 := by linarith
    have hmax : max 0 (T - path.sojournStart k) = 0 :=
      max_eq_left hrem_nonpos
    have hmin : min (path.sojournTime k) (max 0 (T - path.sojournStart k)) = 0 := by
      rw [hmax]
      exact min_eq_right (path.sojournTime_nonneg hstrict hpos k)
    simp [f, hmin]
  have hprefix :
      (∑ k ∈ Finset.range n, f k) ≤
        ∑ k ∈ Finset.range (j + 1), f k :=
    sum_range_le_prefix_of_nonneg_zero_tail n (j + 1) hnonneg hzero_tail
  have hfull :
      (∑ k ∈ Finset.range (j + 1), f k) =
        ∫ t in Set.Icc (0 : ℝ) T,
          M.instantQVRate (path.frozenStateAt t) := by
    simpa [f, j] using
      frozenClockTruncatedQV_sum_jumpCount_succ_eq_setIntegral
        M path hstrict hpos hT hfuture
  exact hprefix.trans_eq hfull

private theorem halfExpPP_clockCellLeftLimit_defect_le_truncatedJumpSq
    (N : ℕ) (hN : 0 < N) (T : ℝ)
    (records :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordΩ)
    (k : ℕ)
    (hstrict_prefix : ∀ n < k,
      (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).times n <
      ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).times (n + 1)))
    (hpos :
      0 < ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).times 0)
    (hseq :
      ∀ m ≤ k,
        (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex
          (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
            records).stateSeq m))
    (hstart_lt_end :
      ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).sojournStart k <
      ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).sojournStart (k + 1))
    (hstart_le_T :
      ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).sojournStart k ≤ T) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    ‖halfExpPP_clockSkeletonVec M T (k + 1) records -
        halfExpPP_clockCellLeftLimit M T k records‖ ^ 2
      ≤ M.truncatedJumpSqIncrementFromHistory T k
        (Preorder.frestrictLe k records) (records (k + 1)) := by
  classical
  let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  let path := M.canonicalPathMap records
  let hist := Preorder.frestrictLe k records
  let J : Fin 3 → ℝ :=
    M.scaledState (path.stateSeq (k + 1)) - M.scaledState (path.stateSeq k)
  have hcell :
      halfExpPP_clockCellLeftLimit M T k records =
        halfExpPP_clockSkeletonVec M T k records -
          (min T (path.sojournStart (k + 1)) - path.sojournStart k) •
            M.generatorDrift (path.stateSeq k) := by
    simpa [M, path] using
      halfExpPP_clockCellLeftLimit_eq_skeleton_sub_drift_prefix
        N hN T records k hstrict_prefix hpos hseq hstart_lt_end hstart_le_T
  have hinc :
      halfExpPP_clockSkeletonVec M T (k + 1) records -
          halfExpPP_clockSkeletonVec M T k records =
        fun i : Fin 3 =>
          M.truncatedCenteredCoordIncrementFromHistory T k i
            hist (records (k + 1)) := by
    ext i
    have h :=
      M.canonicalFrozenClockTruncatedMartingale_succ_sub T i k records
    simpa [halfExpPP_clockSkeletonVec, hist, Pi.sub_apply] using h
  have hremaining :
      CTMC.QMatrix.historyClockRemaining T k hist =
        max 0 (T - path.sojournStart k) := by
    simp [hist, path, M, CTMC.QMatrix.historyClockRemaining,
      CTMC.QMatrix.historySojournStart_frestrictLe,
      CTMC.DensityDepCTMC.canonicalPathMap]
  have hdelta :
      min T (path.sojournStart (k + 1)) - path.sojournStart k =
        min (path.sojournTime k) (max 0 (T - path.sojournStart k)) :=
    halfExpPP_min_T_next_sojournStart_sub_eq_min_sojournTime_remaining
      path T k hstart_le_T
  by_cases hle :
      (records (k + 1)).1 ≤ CTMC.QMatrix.historyClockRemaining T k hist
  · have hle_path :
        path.sojournTime k ≤ max 0 (T - path.sojournStart k) := by
      simpa [hist, hremaining,
        (halfExpPP_clockTail_sojournTime_eq_record M records k).symm] using hle
    have hdelta_eq :
        min T (path.sojournStart (k + 1)) - path.sojournStart k =
          path.sojournTime k := by
      rw [hdelta, min_eq_left hle_path]
    have hdiff :
        halfExpPP_clockSkeletonVec M T (k + 1) records -
            halfExpPP_clockCellLeftLimit M T k records = J := by
      ext i
      have hinc_i := congr_fun hinc i
      have hinc_i' :
          halfExpPP_clockSkeletonVec M T (k + 1) records i -
              halfExpPP_clockSkeletonVec M T k records i =
            M.truncatedCenteredCoordIncrementFromHistory T k i
              hist (records (k + 1)) := by
        simpa [Pi.sub_apply] using hinc_i
      have hif_true :
          (records (k + 1)).1 ≤ 0 ∨
            (records (k + 1)).1 ≤
              T - (CTMC.QMatrix.recordTrajectoryToPath records).sojournStart k := by
        simpa [hist, path, M, CTMC.QMatrix.historyClockRemaining,
          CTMC.QMatrix.historySojournStart_frestrictLe,
          CTMC.DensityDepCTMC.canonicalPathMap] using hle
      have hmin_record :
          min (records (k + 1)).1
              (max 0 (T -
                (CTMC.QMatrix.recordTrajectoryToPath records).sojournStart k)) =
            (records (k + 1)).1 := by
        have hle_record :
            (records (k + 1)).1 ≤
              max 0 (T -
                (CTMC.QMatrix.recordTrajectoryToPath records).sojournStart k) := by
          simpa [hist, path, M, CTMC.QMatrix.historyClockRemaining,
            CTMC.QMatrix.historySojournStart_frestrictLe,
            CTMC.DensityDepCTMC.canonicalPathMap] using hle
        exact min_eq_left hle_record
      have hmin_history :
          min (records (k + 1)).1
              (CTMC.QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records)) =
            (records (k + 1)).1 :=
        min_eq_left hle
      have htrunc_i :
          M.truncatedCenteredCoordIncrementFromHistory T k i
              hist (records (k + 1)) =
            J i - M.generatorDrift (path.stateSeq k) i * path.sojournTime k := by
        simp [CTMC.DensityDepCTMC.truncatedCenteredCoordIncrementFromHistory,
          CTMC.DensityDepCTMC.truncatedCenteredCoordIncrement, hle,
          hmin_history, J, hist, path, M, CTMC.DensityDepCTMC.canonicalPathMap,
          CTMC.QMatrix.currentStateFromHistory_frestrictLe,
          CTMC.QMatrix.recordTrajectoryToPath_stateSeq,
          CTMC.QMatrix.recordTrajectoryToPath_sojournTime]
      calc
        (halfExpPP_clockSkeletonVec M T (k + 1) records -
            halfExpPP_clockCellLeftLimit M T k records) i
            =
          (halfExpPP_clockSkeletonVec M T (k + 1) records i -
              halfExpPP_clockSkeletonVec M T k records i) +
            (min T (path.sojournStart (k + 1)) - path.sojournStart k) *
              M.generatorDrift (path.stateSeq k) i := by
              rw [hcell]
              simp [sub_eq_add_neg]
              ring
        _ =
          M.truncatedCenteredCoordIncrementFromHistory T k i
              hist (records (k + 1)) +
            (min T (path.sojournStart (k + 1)) - path.sojournStart k) *
              M.generatorDrift (path.stateSeq k) i := by
              rw [hinc_i']
        _ = J i := by
              rw [htrunc_i, hdelta_eq]
              ring
    have hrhs :
        M.truncatedJumpSqIncrementFromHistory T k
            (Preorder.frestrictLe k records) (records (k + 1)) =
          ‖J‖ ^ 2 := by
      simp [CTMC.DensityDepCTMC.truncatedJumpSqIncrementFromHistory, hle,
        J, hist, path, M, CTMC.DensityDepCTMC.canonicalPathMap,
        CTMC.QMatrix.currentStateFromHistory_frestrictLe,
        CTMC.QMatrix.recordTrajectoryToPath_stateSeq]
    change
      ‖halfExpPP_clockSkeletonVec M T (k + 1) records -
          halfExpPP_clockCellLeftLimit M T k records‖ ^ 2
        ≤ M.truncatedJumpSqIncrementFromHistory T k
          (Preorder.frestrictLe k records) (records (k + 1))
    simpa [hdiff, hrhs]
  · have hnot_path :
        ¬ path.sojournTime k ≤ max 0 (T - path.sojournStart k) := by
      simpa [hist, hremaining,
        (halfExpPP_clockTail_sojournTime_eq_record M records k).symm] using hle
    have hrem_le :
        max 0 (T - path.sojournStart k) ≤ path.sojournTime k :=
      le_of_not_ge hnot_path
    have hdelta_eq :
        min T (path.sojournStart (k + 1)) - path.sojournStart k =
          max 0 (T - path.sojournStart k) := by
      rw [hdelta, min_eq_right hrem_le]
    have hdiff :
        halfExpPP_clockSkeletonVec M T (k + 1) records -
            halfExpPP_clockCellLeftLimit M T k records = 0 := by
      ext i
      have hinc_i := congr_fun hinc i
      have hinc_i' :
          halfExpPP_clockSkeletonVec M T (k + 1) records i -
              halfExpPP_clockSkeletonVec M T k records i =
            M.truncatedCenteredCoordIncrementFromHistory T k i
              hist (records (k + 1)) := by
        simpa [Pi.sub_apply] using hinc_i
      have hif_false :
          ¬ ((records (k + 1)).1 ≤ 0 ∨
            (records (k + 1)).1 ≤
              T - (CTMC.QMatrix.recordTrajectoryToPath records).sojournStart k) := by
        simpa [hist, path, M, CTMC.QMatrix.historyClockRemaining,
          CTMC.QMatrix.historySojournStart_frestrictLe,
          CTMC.DensityDepCTMC.canonicalPathMap] using hle
      have hmin_remaining :
          min (records (k + 1)).1
              (max 0 (T -
                (CTMC.QMatrix.recordTrajectoryToPath records).sojournStart k)) =
            max 0 (T -
              (CTMC.QMatrix.recordTrajectoryToPath records).sojournStart k) := by
        have hrem_le_record :
            max 0 (T -
                (CTMC.QMatrix.recordTrajectoryToPath records).sojournStart k) ≤
              (records (k + 1)).1 := by
          simpa [path, M, CTMC.DensityDepCTMC.canonicalPathMap,
            CTMC.QMatrix.recordTrajectoryToPath_sojournTime] using hrem_le
        exact min_eq_right hrem_le_record
      have hmin_history :
          min (records (k + 1)).1
              (CTMC.QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records)) =
            CTMC.QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records) :=
        min_eq_right (le_of_not_ge hle)
      have htrunc_i :
          M.truncatedCenteredCoordIncrementFromHistory T k i
              hist (records (k + 1)) =
            -M.generatorDrift (path.stateSeq k) i *
              max 0 (T - path.sojournStart k) := by
        simp [CTMC.DensityDepCTMC.truncatedCenteredCoordIncrementFromHistory,
          CTMC.DensityDepCTMC.truncatedCenteredCoordIncrement, hle,
          hmin_history, hremaining, hif_false, hmin_remaining, hist, path, M,
          CTMC.DensityDepCTMC.canonicalPathMap,
          CTMC.QMatrix.currentStateFromHistory_frestrictLe,
          CTMC.QMatrix.recordTrajectoryToPath_stateSeq,
          CTMC.QMatrix.recordTrajectoryToPath_sojournTime]
      calc
        (halfExpPP_clockSkeletonVec M T (k + 1) records -
            halfExpPP_clockCellLeftLimit M T k records) i
            =
          (halfExpPP_clockSkeletonVec M T (k + 1) records i -
              halfExpPP_clockSkeletonVec M T k records i) +
            (min T (path.sojournStart (k + 1)) - path.sojournStart k) *
              M.generatorDrift (path.stateSeq k) i := by
              rw [hcell]
              simp [sub_eq_add_neg]
              ring
        _ =
          M.truncatedCenteredCoordIncrementFromHistory T k i
              hist (records (k + 1)) +
            (min T (path.sojournStart (k + 1)) - path.sojournStart k) *
              M.generatorDrift (path.stateSeq k) i := by
              rw [hinc_i']
        _ = 0 := by
              rw [htrunc_i, hdelta_eq]
              ring
    have hrhs :
        M.truncatedJumpSqIncrementFromHistory T k
            (Preorder.frestrictLe k records) (records (k + 1)) = 0 := by
      simp [CTMC.DensityDepCTMC.truncatedJumpSqIncrementFromHistory, hle,
        hist, path, M, CTMC.DensityDepCTMC.canonicalPathMap,
        CTMC.QMatrix.currentStateFromHistory_frestrictLe,
        CTMC.QMatrix.recordTrajectoryToPath_stateSeq]
    change
      ‖halfExpPP_clockSkeletonVec M T (k + 1) records -
          halfExpPP_clockCellLeftLimit M T k records‖ ^ 2
        ≤ M.truncatedJumpSqIncrementFromHistory T k
          (Preorder.frestrictLe k records) (records (k + 1))
    simpa [hdiff, hrhs]

private theorem halfExpPP_frozenMartingalePart_live_affine
    (N : ℕ) (hN : 0 < N) (T s : ℝ)
    (records :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordΩ)
    (k : ℕ)
    (hstrict_prefix : ∀ n < k,
      (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).times n <
      ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).times (n + 1)))
    (hpos :
      0 < ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).times 0)
    (hseq :
      ∀ m ≤ k,
        (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex
          (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
            records).stateSeq m))
    (hstart_le_s :
      ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).sojournStart k ≤ s)
    (hs_lt_next :
      s < ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).sojournStart (k + 1))
    (hs_le_min :
      s ≤ min T
        (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
          records).sojournStart (k + 1))) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      M.frozenMartingalePart M.canonicalPathMap s records =
        (1 - θ) • halfExpPP_clockSkeletonVec M T k records +
          θ • halfExpPP_clockCellLeftLimit M T k records := by
  classical
  let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  let path := M.canonicalPathMap records
  let r : ℝ := min T (path.sojournStart (k + 1))
  have hs0 : 0 ≤ s := by
    have hstart_nonneg : 0 ≤ path.sojournStart k :=
      halfExpPP_sojournStart_nonneg_of_prefix path k hpos hstrict_prefix
    exact le_trans hstart_nonneg hstart_le_s
  have hstart_lt_end : path.sojournStart k < path.sojournStart (k + 1) :=
    lt_of_le_of_lt hstart_le_s hs_lt_next
  have hstart_le_T : path.sojournStart k ≤ T := by
    exact le_trans hstart_le_s (le_trans hs_le_min (min_le_left _ _))
  have hstart_le_r : path.sojournStart k ≤ r := by
    exact le_min hstart_le_T (le_of_lt hstart_lt_end)
  obtain ⟨θ, hθ0, hθ1, hs_aff⟩ :=
    halfExpPP_affineParameter
      (l := path.sojournStart k) (r := r) (s := s)
      hstart_le_r hstart_le_s hs_le_min
  refine ⟨θ, hθ0, hθ1, ?_⟩
  have hcount : path.jumpCount s = k := by
    exact halfExpPP_jumpCount_eq_of_live_sojourn path
      hstrict_prefix hstart_le_s hs_lt_next
  have hBC : M.BoundaryCompatibleOnSimplex := by
    simpa [M] using halfExpPP_boundaryCompatibleOnSimplex N hN
  have hskel :
      halfExpPP_clockSkeletonVec M T k records =
        fun i : Fin 3 =>
          M.frozenTimeCompensatedJumpMartingale path i k := by
    simpa [M, path] using
      halfExpPP_clockSkeletonVec_eq_frozenTimeCompensated
        M T records k hstrict_prefix hpos hstart_le_T
  have hcell :
      halfExpPP_clockCellLeftLimit M T k records =
        halfExpPP_clockSkeletonVec M T k records -
          (r - path.sojournStart k) • M.generatorDrift (path.stateSeq k) := by
    simpa [M, path, r] using
      halfExpPP_clockCellLeftLimit_eq_skeleton_sub_drift_prefix
        N hN T records k hstrict_prefix hpos hseq hstart_lt_end hstart_le_T
  have hs_sub :
      s - path.sojournStart k = θ * (r - path.sojournStart k) := by
    rw [hs_aff]
    ring
  ext i
  have happly :
      M.frozenMartingalePart M.canonicalPathMap s records i =
        M.frozenTimeCompensatedJumpMartingale path i k -
          M.generatorDrift (path.stateSeq k) i *
            (s - path.sojournStart k) := by
    let path' := halfExpPP_strictCompletionThrough path k
    have hcomp := halfExpPP_strictCompletionThrough_strict
      path k hpos hstrict_prefix
    have hstart_eq :
        path'.sojournStart k = path.sojournStart k := by
      simpa [path'] using
        halfExpPP_strictCompletionThrough_sojournStart_eq_of_le path k k le_rfl
    have hnext_eq :
        path'.sojournStart (k + 1) = path.sojournStart (k + 1) := by
      simpa [path'] using
        halfExpPP_strictCompletionThrough_sojournStart_succ_eq path k
    have hstart_le_s' : path'.sojournStart k ≤ s := by
      simpa [hstart_eq] using hstart_le_s
    have hs_lt_next' : s < path'.sojournStart (k + 1) := by
      rw [hnext_eq]
      exact hs_lt_next
    have hcount' : path'.jumpCount s = k := by
      exact halfExpPP_jumpCount_eq_of_live_sojourn path'
        (fun n _hn => hcomp.2 n) hstart_le_s' hs_lt_next'
    have hfuture' : ∃ n, s < path'.times n := by
      refine ⟨k, ?_⟩
      have hs_time : s < path.times k := by
        simpa [CTMC.CTMCPath.sojournStart] using hs_lt_next
      have htime_eq : path'.times k = path.times k := by
        simp [path', halfExpPP_strictCompletionThrough]
      rw [htime_eq]
      exact hs_time
    have hDrift' : ∀ m ≤ path'.jumpCount s,
        M.generatorDrift (path'.stateSeq m) =
          M.rateSpec.drift (M.scaledState (path'.stateSeq m)) := by
      intro m hm
      have hmle : m ≤ k := by
        simpa [hcount'] using hm
      have hstate : path'.stateSeq m = path.stateSeq m := by
        simpa [path'] using
          halfExpPP_strictCompletionThrough_stateSeq_eq path k m
      exact M.generatorDrift_eq_rateSpec_drift_of_boundaryCompatibleOnSimplex
        hBC (by simpa [hstate] using hseq m hmle)
    have htransfer :
        M.frozenMartingalePart M.canonicalPathMap s records =
          M.frozenMartingalePart (fun _ : Unit => path') s Unit.unit :=
      halfExpPP_strictCompletionThrough_frozenMartingalePart_eq_of_lt_succ
        M records k hs0 hs_lt_next
    have h :=
      M.frozenMartingalePart_apply_eq_frozenTimeCompensated_sub_current
        path' hcomp.2 hcomp.1 hs0 hfuture' hDrift' i
    have hstate_k : path'.stateSeq k = path.stateSeq k := by
      simpa [path'] using
        halfExpPP_strictCompletionThrough_stateSeq_eq path k k
    have htimecomp :
        M.frozenTimeCompensatedJumpMartingale path' i k =
          M.frozenTimeCompensatedJumpMartingale path i k :=
      halfExpPP_strictCompletionThrough_frozenTimeCompensated_eq M path i k
    calc
      M.frozenMartingalePart M.canonicalPathMap s records i
          = M.frozenMartingalePart (fun _ : Unit => path') s Unit.unit i := by
              rw [htransfer]
      _ = M.frozenTimeCompensatedJumpMartingale path' i k -
            M.generatorDrift (path'.stateSeq k) i *
              (s - path'.sojournStart k) := by
              simpa [M, path', hcount', CTMC.CTMCPath.currentSojournElapsed] using h
      _ = M.frozenTimeCompensatedJumpMartingale path i k -
            M.generatorDrift (path.stateSeq k) i *
              (s - path.sojournStart k) := by
              rw [htimecomp, hstate_k, hstart_eq]
  have hskel_i := congr_fun hskel i
  calc
    M.frozenMartingalePart M.canonicalPathMap s records i
        = M.frozenTimeCompensatedJumpMartingale path i k -
            M.generatorDrift (path.stateSeq k) i *
              (s - path.sojournStart k) := happly
    _ = halfExpPP_clockSkeletonVec M T k records i -
            M.generatorDrift (path.stateSeq k) i *
              (s - path.sojournStart k) := by
          rw [← hskel_i]
    _ = ((1 - θ) • halfExpPP_clockSkeletonVec M T k records +
            θ • halfExpPP_clockCellLeftLimit M T k records) i := by
          rw [hcell]
          simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply]
          rw [hs_sub]
          ring

private theorem halfExpPP_truncatedJumpSqIncrementFromHistory_nonneg
    (M : CTMC.DensityDepCTMC 3) (T : ℝ) (records : M.canonicalRecordΩ)
    (k : ℕ) :
    0 ≤ M.truncatedJumpSqIncrementFromHistory T k
      (Preorder.frestrictLe k records) (records (k + 1)) := by
  unfold CTMC.DensityDepCTMC.truncatedJumpSqIncrementFromHistory
  by_cases hmem :
      (records (k + 1)).1 ∈
        Set.Iic (CTMC.QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records))
  · rw [Set.indicator_of_mem hmem]
    exact mul_nonneg zero_le_one (sq_nonneg _)
  · rw [Set.indicator_of_notMem hmem]
    simp

private theorem halfExpPP_truncatedJumpSqIncrement_le_sumTruncatedJumpSq
    (M : CTMC.DensityDepCTMC 3) (T : ℝ) (records : M.canonicalRecordΩ)
    {k : ℕ} (hk : k ∈ Finset.range (M.N + 1)) :
    M.truncatedJumpSqIncrementFromHistory T k
        (Preorder.frestrictLe k records) (records (k + 1)) ≤
      halfExpPP_sumTruncatedJumpSq M T records := by
  classical
  unfold halfExpPP_sumTruncatedJumpSq
  exact Finset.single_le_sum
    (fun j _hj =>
      halfExpPP_truncatedJumpSqIncrementFromHistory_nonneg M T records j)
    hk

private theorem halfExpPP_frozenMartingalePart_live_sq_le_affineBridgeBound
    (N : ℕ) (hN : 0 < N) (T s : ℝ)
    (records :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordΩ)
    (k : ℕ)
    (hk : k ∈ Finset.range (N + 1))
    (hstrict_prefix : ∀ n < k,
      (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).times n <
      ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).times (n + 1)))
    (hpos :
      0 < ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).times 0)
    (hseq :
      ∀ m ≤ k,
        (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex
          (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
            records).stateSeq m))
    (hstart_le_s :
      ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).sojournStart k ≤ s)
    (hs_lt_next :
      s < ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
        records).sojournStart (k + 1))
    (hs_le_min :
      s ≤ min T
        (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
          records).sojournStart (k + 1))) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2 ≤
      (4 / 3 : ℝ) * halfExpPP_clockSkeletonSupSq M T records +
        4 * halfExpPP_sumTruncatedJumpSq M T records := by
  classical
  let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  let path := M.canonicalPathMap records
  have hstart_lt_end : path.sojournStart k < path.sojournStart (k + 1) :=
    lt_of_le_of_lt hstart_le_s hs_lt_next
  have hstart_le_T : path.sojournStart k ≤ T :=
    le_trans hstart_le_s (le_trans hs_le_min (min_le_left _ _))
  obtain ⟨θ, hθ0, hθ1, haff⟩ :=
    halfExpPP_frozenMartingalePart_live_affine
      N hN T s records k hstrict_prefix hpos hseq
      hstart_le_s hs_lt_next hs_le_min
  have hmax :
      ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2 ≤
        max
          (‖halfExpPP_clockSkeletonVec M T k records‖ ^ 2)
          (‖halfExpPP_clockCellLeftLimit M T k records‖ ^ 2) :=
    halfExpPP_frozenMartingalePart_sq_le_cell_endpoint_max_of_affine
      M T records k s θ (halfExpPP_clockCellLeftLimit M T k records)
      hθ0 hθ1 haff
  have hk_skel : k ∈ Finset.range (M.N + 2) := by
    have hklt := Finset.mem_range.mp hk
    change k ∈ Finset.range (N + 2)
    exact Finset.mem_range.mpr (by omega)
  have hk_next_skel : k + 1 ∈ Finset.range (M.N + 2) := by
    have hklt := Finset.mem_range.mp hk
    change k + 1 ∈ Finset.range (N + 2)
    exact Finset.mem_range.mpr (by omega)
  have hk_sum : k ∈ Finset.range (M.N + 1) := by
    change k ∈ Finset.range (N + 1)
    exact hk
  have hskel_bridge :
      ‖halfExpPP_clockSkeletonVec M T k records‖ ^ 2 ≤
        (4 / 3 : ℝ) * halfExpPP_clockSkeletonSupSq M T records +
          4 * halfExpPP_sumTruncatedJumpSq M T records :=
    (halfExpPP_clockSkeletonVec_sq_le_sup M T records hk_skel).trans
      (halfExpPP_clockSkeletonSupSq_le_affineBridgeBound M T records)
  have hdefect :
      ‖halfExpPP_clockSkeletonVec M T (k + 1) records -
          halfExpPP_clockCellLeftLimit M T k records‖ ^ 2
        ≤ M.truncatedJumpSqIncrementFromHistory T k
          (Preorder.frestrictLe k records) (records (k + 1)) := by
    exact
      halfExpPP_clockCellLeftLimit_defect_le_truncatedJumpSq
        N hN T records k hstrict_prefix hpos hseq hstart_lt_end hstart_le_T
  have hcell_raw :=
    halfExpPP_clockCellLeftLimit_sq_le_nextSkeleton_add_jumpSq
      M T records k hdefect
  have hnext_le :
      ‖halfExpPP_clockSkeletonVec M T (k + 1) records‖ ^ 2 ≤
        halfExpPP_clockSkeletonSupSq M T records :=
    halfExpPP_clockSkeletonVec_sq_le_sup M T records hk_next_skel
  have hterm_le :
      M.truncatedJumpSqIncrementFromHistory T k
          (Preorder.frestrictLe k records) (records (k + 1)) ≤
        halfExpPP_sumTruncatedJumpSq M T records :=
    halfExpPP_truncatedJumpSqIncrement_le_sumTruncatedJumpSq M T records hk_sum
  have hcell_bridge :
      ‖halfExpPP_clockCellLeftLimit M T k records‖ ^ 2 ≤
        (4 / 3 : ℝ) * halfExpPP_clockSkeletonSupSq M T records +
          4 * halfExpPP_sumTruncatedJumpSq M T records := by
    calc
      ‖halfExpPP_clockCellLeftLimit M T k records‖ ^ 2
          ≤ (4 / 3 : ℝ) *
              ‖halfExpPP_clockSkeletonVec M T (k + 1) records‖ ^ 2 +
            4 * M.truncatedJumpSqIncrementFromHistory T k
              (Preorder.frestrictLe k records) (records (k + 1)) := hcell_raw
      _ ≤ (4 / 3 : ℝ) * halfExpPP_clockSkeletonSupSq M T records +
            4 * halfExpPP_sumTruncatedJumpSq M T records := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hnext_le (by norm_num))
              (mul_le_mul_of_nonneg_left hterm_le (by norm_num))
  exact hmax.trans (max_le hskel_bridge hcell_bridge)

private theorem canonicalRecordMeasure_all_next_state_eq_current_ae_of_absorbing_pre
    {S : Type*} [Fintype S] [DecidableEq S] [Countable S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (Q : CTMC.QMatrix S) (s₀ : S) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀, ∀ n,
      Q.IsAbsorbing
          (CTMC.QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records)) →
        (records (n + 1)).2 =
          CTMC.QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records) := by
  refine MeasureTheory.ae_all_iff.mpr ?_
  intro n
  let μ := Q.canonicalRecordMeasure s₀
  let X : ((m : ℕ) → CTMC.QMatrix.JumpHoldTrajectorySpace S m) →
      ((i : Finset.Iic n) → CTMC.QMatrix.JumpHoldTrajectorySpace S i) :=
    Preorder.frestrictLe n
  let Y : ((m : ℕ) → CTMC.QMatrix.JumpHoldTrajectorySpace S m) →
      CTMC.QMatrix.JumpHoldTrajectorySpace S (n + 1) :=
    fun records => records (n + 1)
  let p :
      (((i : Finset.Iic n) → CTMC.QMatrix.JumpHoldTrajectorySpace S i) ×
        CTMC.QMatrix.JumpHoldTrajectorySpace S (n + 1)) → Prop :=
    fun z =>
      Q.IsAbsorbing (CTMC.QMatrix.currentStateFromHistory (S := S) n z.1) →
        z.2.2 = CTMC.QMatrix.currentStateFromHistory (S := S) n z.1
  have hp : MeasurableSet {z | p z} := by
    have h_abs : MeasurableSet
        {z : (((i : Finset.Iic n) → CTMC.QMatrix.JumpHoldTrajectorySpace S i) ×
            CTMC.QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          Q.IsAbsorbing (CTMC.QMatrix.currentStateFromHistory (S := S) n z.1)} := by
      exact ((CTMC.QMatrix.measurable_currentStateFromHistory (S := S) n).comp measurable_fst)
        ((Set.to_countable {s : S | Q.IsAbsorbing s}).measurableSet)
    have h_eq : MeasurableSet
        {z : (((i : Finset.Iic n) → CTMC.QMatrix.JumpHoldTrajectorySpace S i) ×
            CTMC.QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          z.2.2 = CTMC.QMatrix.currentStateFromHistory (S := S) n z.1} :=
      measurableSet_eq_fun (measurable_snd.comp measurable_snd)
        ((CTMC.QMatrix.measurable_currentStateFromHistory (S := S) n).comp measurable_fst)
    rw [show {z | p z} =
        {z : (((i : Finset.Iic n) → CTMC.QMatrix.JumpHoldTrajectorySpace S i) ×
            CTMC.QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          ¬ Q.IsAbsorbing (CTMC.QMatrix.currentStateFromHistory (S := S) n z.1)} ∪
        {z : (((i : Finset.Iic n) → CTMC.QMatrix.JumpHoldTrajectorySpace S i) ×
            CTMC.QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          z.2.2 = CTMC.QMatrix.currentStateFromHistory (S := S) n z.1} by
      ext z
      by_cases h : Q.IsAbsorbing (CTMC.QMatrix.currentStateFromHistory (S := S) n z.1)
      · simp [p, h]
      · simp [p, h]]
    exact h_abs.compl.union h_eq
  have hkernel :
      ∀ᵐ hist ∂μ.map X,
        ∀ᵐ r ∂Q.jumpHoldTrajectoryStepKernel n hist, p (hist, r) := by
    refine Filter.Eventually.of_forall ?_
    intro hist
    by_cases h : Q.IsAbsorbing (CTMC.QMatrix.currentStateFromHistory (S := S) n hist)
    · have hdirac :
          Q.jumpHoldTrajectoryStepKernel n hist =
            MeasureTheory.Measure.dirac
              (0, CTMC.QMatrix.currentStateFromHistory (S := S) n hist) := by
        rw [Q.jumpHoldTrajectoryStepKernel_apply, Q.jumpHoldStepKernel_apply,
          Q.jumpHoldStepMeasureTotal_of_absorbing h]
      rw [hdirac]
      simp [p, h]
    · filter_upwards with r
      intro hAbs
      exact (h hAbs).elim
  have hpair : ∀ᵐ z ∂(μ.map fun records => (X records, Y records)), p z := by
    rw [show μ.map (fun records => (X records, Y records)) =
        μ.map (fun records => (Preorder.frestrictLe n records, records (n + 1))) by
          rfl]
    rw [show μ.map X = μ.map (Preorder.frestrictLe n) by rfl] at hkernel
    rw [show Q.jumpHoldTrajectoryStepKernel n = Q.jumpHoldTrajectoryStepKernel n by rfl] at hkernel
    rw [show μ = Q.canonicalRecordMeasure s₀ by rfl]
    rw [Q.canonicalRecordMeasure_history_next s₀ n]
    exact MeasureTheory.Measure.ae_compProd_of_ae_ae hp hkernel
  have hrecords : ∀ᵐ records ∂μ, p (X records, Y records) :=
    MeasureTheory.ae_of_ae_map (by fun_prop) hpair
  simpa [μ, X, Y, p] using hrecords

private theorem halfExpPP_canonical_frozenMartingalePart_eq_zero_ae_of_absorbing_pre
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1))
    (hinit : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x₀)
    (habs :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing x₀) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ t : ℝ,
      M.frozenMartingalePart M.canonicalPathMap t records = 0 := by
  let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  have hDrift : M.rateSpec.drift (M.scaledState x₀) = 0 := by
    exact (halfExpPP_driftZeroAtAbsorbingOnSimplex N hN) x₀ hinit
      (by simpa [M, CTMC.QMatrix.IsAbsorbing] using habs)
  filter_upwards
    [M.toQMatrix.canonicalRecordMeasure_record_zero_eq_init_ae x₀,
      canonicalRecordMeasure_all_next_state_eq_current_ae_of_absorbing_pre M.toQMatrix x₀]
    with records hrecord0 hstay t
  have hrecord0_state : (records 0).2 = x₀ := by
    simpa using congrArg Prod.snd hrecord0
  have hseq : ∀ n, (M.canonicalPathMap records).stateSeq n = x₀ := by
    intro n
    induction n with
    | zero =>
        simpa [M, CTMC.DensityDepCTMC.canonicalPathMap,
          CTMC.QMatrix.recordTrajectoryToPath_stateSeq] using hrecord0_state
    | succ n ih =>
        have hcur :
            CTMC.QMatrix.currentStateFromHistory
                (S := Fin 3 → Fin (N + 1)) n (Preorder.frestrictLe n records) = x₀ := by
          simpa [M, CTMC.DensityDepCTMC.canonicalPathMap,
            CTMC.QMatrix.currentStateFromHistory_frestrictLe] using ih
        have hnext := hstay n (by simpa [hcur, M] using habs)
        have hnext_state : (records (n + 1)).2 = x₀ := by
          simpa [hcur] using hnext
        simpa [M, CTMC.DensityDepCTMC.canonicalPathMap,
          CTMC.QMatrix.recordTrajectoryToPath_stateSeq] using hnext_state
  have hfrozen : ∀ s : ℝ, (M.canonicalPathMap records).frozenStateAt s = x₀ := by
    intro s
    let path := M.canonicalPathMap records
    have hseq_path : ∀ n, path.stateSeq n = x₀ := hseq
    by_cases hex : ∃ n, s < path.times n
    · let n := Nat.find hex
      have hmin : ∀ k ∈ Finset.range n, ¬ s < path.times k := by
        intro k hk
        exact Nat.find_min hex (Finset.mem_range.mp hk)
      rw [path.frozenStateAt_eq_stateSeq_of_first_time_gt s n
        (Nat.find_spec hex) hmin, hseq_path n]
    · have hno : ∀ n, ¬ s < path.times n := by
        intro n hn
        exact hex ⟨n, hn⟩
      have hstable : path.stateSeq 0 = path.stateSeq (0 + 1) := by
        rw [hseq_path 0, hseq_path 1]
      have hmin : ∀ k ∈ Finset.range 0,
          path.stateSeq k ≠ path.stateSeq (k + 1) := by
        intro k hk
        simp at hk
      rw [path.frozenStateAt_eq_stateSeq_of_first_stable s 0 hno hstable hmin,
        hseq_path 0]
  ext i
  simp only [CTMC.DensityDepCTMC.frozenMartingalePart,
    CTMC.DensityDepCTMC.frozenDensityProcess,
    CTMC.DensityDepCTMC.frozenInitialCondition, Pi.sub_apply, Pi.zero_apply]
  have hinit_frozen : (M.canonicalPathMap records).frozenStateAt 0 = x₀ := hfrozen 0
  have ht_frozen : (M.canonicalPathMap records).frozenStateAt t = x₀ := hfrozen t
  have hfun_zero :
      (fun s : ℝ =>
        (M.rateSpec.drift (M.frozenDensityProcess M.canonicalPathMap s records)) i)
        = fun _ => 0 := by
    funext s
    have hdens :
        M.frozenDensityProcess M.canonicalPathMap s records = M.scaledState x₀ := by
      ext j
      simp [CTMC.DensityDepCTMC.frozenDensityProcess,
        CTMC.DensityDepCTMC.scaledState, hfrozen s]
    rw [hdens]
    exact congr_fun hDrift i
  rw [ht_frozen, hinit_frozen, hfun_zero]
  simp [CTMC.DensityDepCTMC.frozenDensityProcess]

private theorem halfExpPP_integral_clockTruncated_vector_sup_sq_le_coord_qv
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1)) (T : ℝ) (n : ℕ) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    ∫ records,
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k =>
            ‖(fun i : Fin 3 =>
              M.canonicalFrozenClockTruncatedMartingale T i k records)‖ ^ 2)
        ∂M.canonicalRecordMeasure x₀ ≤
      4 * ∑ i : Fin 3, ∑ k ∈ Finset.range n,
        ∫ records,
          (let hist := Preorder.frestrictLe k records
           let x : Fin 3 → Fin (N + 1) :=
            CTMC.QMatrix.currentStateFromHistory
              (S := Fin 3 → Fin (N + 1)) k hist
           M.instantCoordQVRate x i *
            min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist))
          ∂M.canonicalRecordMeasure x₀ := by
  intro M
  let μ := M.canonicalRecordMeasure x₀
  let V : M.canonicalRecordΩ → ℝ := fun records =>
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k =>
        ‖(fun i : Fin 3 =>
          M.canonicalFrozenClockTruncatedMartingale T i k records)‖ ^ 2)
  let C : Fin 3 → M.canonicalRecordΩ → ℝ := fun i records =>
    ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)) ^ 2
  have hC_int : ∀ i : Fin 3, MeasureTheory.Integrable (C i) μ := by
    intro i
    simpa [C, μ] using
      M.integrable_canonicalFrozenClockTruncatedMartingale_sup_sq x₀ T i n
  have hsumC_int : MeasureTheory.Integrable (fun records => ∑ i : Fin 3, C i records) μ :=
    MeasureTheory.integrable_finsetSum Finset.univ fun i _ => hC_int i
  have hV_meas : MeasureTheory.AEStronglyMeasurable V μ := by
    dsimp [V]
    refine (Finset.measurable_range_sup'' ?_).aestronglyMeasurable
    intro k _hk
    exact (measurable_norm.comp
      (by
        exact measurable_pi_lambda _ fun i =>
          (M.measurable_canonicalFrozenClockTruncatedMartingale_canonicalRecordFiltration
            T i k).mono (M.canonicalRecordFiltration.le k) le_rfl)).pow measurable_const
  have hpoint : ∀ records : M.canonicalRecordΩ, V records ≤ ∑ i : Fin 3, C i records := by
    intro records
    dsimp [V, C]
    refine Finset.sup'_le _ _ ?_
    intro k hk
    have hcoord :
        ‖(fun i : Fin 3 =>
          M.canonicalFrozenClockTruncatedMartingale T i k records)‖ ^ 2 ≤
        ∑ i : Fin 3,
          (M.canonicalFrozenClockTruncatedMartingale T i k records) ^ 2 :=
      Ripple.Kurtz.vector_norm_sq_le_sum_sq _
    refine hcoord.trans ?_
    refine Finset.sum_le_sum fun i _hi => ?_
    let S : ℝ :=
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)
    have hS_nonneg : 0 ≤ S := by
      exact (norm_nonneg _).trans
        (Finset.le_sup'
          (s := Finset.range (n + 1))
          (f := fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)
          (Finset.mem_range.mpr (Nat.succ_pos n)))
    have habs_le :
        |M.canonicalFrozenClockTruncatedMartingale T i k records| ≤ S := by
      simpa [S, Real.norm_eq_abs] using
        Finset.le_sup'
          (s := Finset.range (n + 1))
          (f := fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)
          hk
    have hsquare :
        (M.canonicalFrozenClockTruncatedMartingale T i k records) ^ 2 ≤ S ^ 2 := by
      rw [← sq_abs]
      exact sq_le_sq' (by
        nlinarith [hS_nonneg,
          abs_nonneg (M.canonicalFrozenClockTruncatedMartingale T i k records)]) habs_le
    simpa [S] using hsquare
  have hV_int : MeasureTheory.Integrable V μ := by
    refine hsumC_int.mono' hV_meas ?_
    refine Filter.Eventually.of_forall fun records => ?_
    have hV_nonneg : 0 ≤ V records := by
      dsimp [V]
      exact sq_nonneg _ |>.trans
        (Finset.le_sup'
          (s := Finset.range (n + 1))
          (f := fun k =>
            ‖(fun i : Fin 3 =>
              M.canonicalFrozenClockTruncatedMartingale T i k records)‖ ^ 2)
          (Finset.mem_range.mpr (Nat.succ_pos n)))
    have hsum_nonneg : 0 ≤ ∑ i : Fin 3, C i records := by
      exact Finset.sum_nonneg fun i _ => by
        dsimp [C]
        exact sq_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hV_nonneg, abs_of_nonneg hsum_nonneg]
      using hpoint records
  have hmono :
      ∫ records, V records ∂μ ≤ ∫ records, (∑ i : Fin 3, C i records) ∂μ :=
    MeasureTheory.integral_mono hV_int hsumC_int hpoint
  have hcalc :
      ∫ records, V records ∂μ ≤
        4 * ∑ i : Fin 3, ∑ k ∈ Finset.range n,
          ∫ records,
            (let hist := Preorder.frestrictLe k records
             let x : Fin 3 → Fin (N + 1) :=
              CTMC.QMatrix.currentStateFromHistory
                (S := Fin 3 → Fin (N + 1)) k hist
             M.instantCoordQVRate x i *
              min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist))
            ∂M.canonicalRecordMeasure x₀ := by
    calc
      ∫ records, V records ∂μ
          ≤ ∫ records, (∑ i : Fin 3, C i records) ∂μ := hmono
      _ = ∑ i : Fin 3, ∫ records, C i records ∂μ := by
            rw [MeasureTheory.integral_finsetSum]
            intro i _hi
            exact hC_int i
      _ ≤ ∑ i : Fin 3, 4 * ∑ k ∈ Finset.range n,
          ∫ records,
            (let hist := Preorder.frestrictLe k records
             let x : Fin 3 → Fin (N + 1) :=
              CTMC.QMatrix.currentStateFromHistory
                (S := Fin 3 → Fin (N + 1)) k hist
             M.instantCoordQVRate x i *
              min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist))
            ∂M.canonicalRecordMeasure x₀ := by
            exact Finset.sum_le_sum fun i _hi => by
              simpa [C, μ, M] using
                M.integral_canonicalFrozenClockTruncatedMartingale_sup_sq_le_sum_clockTruncatedCoordQV
                  x₀ T i n
      _ = 4 * ∑ i : Fin 3, ∑ k ∈ Finset.range n,
          ∫ records,
            (let hist := Preorder.frestrictLe k records
             let x : Fin 3 → Fin (N + 1) :=
              CTMC.QMatrix.currentStateFromHistory
                (S := Fin 3 → Fin (N + 1)) k hist
             M.instantCoordQVRate x i *
              min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist))
            ∂M.canonicalRecordMeasure x₀ := by
            rw [Finset.mul_sum]
  simpa [V, μ] using hcalc

private theorem halfExpPP_integral_clockTruncated_vector_sup_sq_le_vector_qv
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1)) (T : ℝ) (n : ℕ) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    ∫ records,
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k =>
            ‖(fun i : Fin 3 =>
              M.canonicalFrozenClockTruncatedMartingale T i k records)‖ ^ 2)
        ∂M.canonicalRecordMeasure x₀ ≤
      8 * ∑ k ∈ Finset.range n,
        ∫ records,
          (let hist := Preorder.frestrictLe k records
           let x : Fin 3 → Fin (N + 1) :=
            CTMC.QMatrix.currentStateFromHistory
              (S := Fin 3 → Fin (N + 1)) k hist
           M.instantQVRate x *
            min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist))
          ∂M.canonicalRecordMeasure x₀ := by
  intro M
  let A : Fin 3 → ℕ → ℝ := fun i k =>
    ∫ records,
      (let hist := Preorder.frestrictLe k records
       let x : Fin 3 → Fin (N + 1) :=
        CTMC.QMatrix.currentStateFromHistory
          (S := Fin 3 → Fin (N + 1)) k hist
       M.instantCoordQVRate x i *
        min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist))
      ∂M.canonicalRecordMeasure x₀
  let B : ℕ → ℝ := fun k =>
    ∫ records,
      (let hist := Preorder.frestrictLe k records
       let x : Fin 3 → Fin (N + 1) :=
        CTMC.QMatrix.currentStateFromHistory
          (S := Fin 3 → Fin (N + 1)) k hist
       M.instantQVRate x *
        min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist))
      ∂M.canonicalRecordMeasure x₀
  have hbase :
      ∫ records,
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k =>
              ‖(fun i : Fin 3 =>
                M.canonicalFrozenClockTruncatedMartingale T i k records)‖ ^ 2)
          ∂M.canonicalRecordMeasure x₀ ≤
        4 * ∑ i : Fin 3, ∑ k ∈ Finset.range n, A i k := by
    simpa [A, M] using
      halfExpPP_integral_clockTruncated_vector_sup_sq_le_coord_qv
        N hN x₀ T n
  have hsum :
      (∑ i : Fin 3, ∑ k ∈ Finset.range n, A i k) ≤
        2 * ∑ k ∈ Finset.range n, B k := by
    calc
      (∑ i : Fin 3, ∑ k ∈ Finset.range n, A i k)
          = ∑ k ∈ Finset.range n, ∑ i : Fin 3, A i k := by
            rw [Finset.sum_comm]
      _ ≤ ∑ k ∈ Finset.range n, 2 * B k := by
            refine Finset.sum_le_sum ?_
            intro k hk
            simpa [A, B, M] using
              halfExpPP_sum_clockTruncatedCoordQV_integral_le_two_vector
                N hN x₀ T k
      _ = 2 * ∑ k ∈ Finset.range n, B k := by
            rw [Finset.mul_sum]
  have hmain :
      ∫ records,
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k =>
              ‖(fun i : Fin 3 =>
                M.canonicalFrozenClockTruncatedMartingale T i k records)‖ ^ 2)
          ∂M.canonicalRecordMeasure x₀ ≤
        8 * ∑ k ∈ Finset.range n, B k := by
    nlinarith
  simpa [B] using hmain

private theorem halfExpPP_integral_clockSkeletonSupSq_le_eight_clockQV_sum
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1)) (T : ℝ) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    ∫ records, halfExpPP_clockSkeletonSupSq M T records
        ∂M.canonicalRecordMeasure x₀ ≤
      8 * ∑ k ∈ Finset.range (N + 1),
        ∫ records,
          (let hist := Preorder.frestrictLe k records
           let x : Fin 3 → Fin (N + 1) :=
            CTMC.QMatrix.currentStateFromHistory
              (S := Fin 3 → Fin (N + 1)) k hist
           M.instantQVRate x *
            min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist))
          ∂M.canonicalRecordMeasure x₀ := by
  intro M
  simpa [M, halfExpPP_clockSkeletonSupSq, halfExpPP_clockSkeletonVec] using
    halfExpPP_integral_clockTruncated_vector_sup_sq_le_vector_qv
      N hN x₀ T (N + 1)

private theorem halfExpPP_integral_sumTruncatedJumpSq_eq_clockQV_sum
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1)) (T : ℝ) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    ∫ records, halfExpPP_sumTruncatedJumpSq M T records
        ∂M.canonicalRecordMeasure x₀ =
      ∑ k ∈ Finset.range (N + 1),
        ∫ records,
          (let hist := Preorder.frestrictLe k records
           let x : Fin 3 → Fin (N + 1) :=
            CTMC.QMatrix.currentStateFromHistory
              (S := Fin 3 → Fin (N + 1)) k hist
           M.instantQVRate x *
            min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist))
          ∂M.canonicalRecordMeasure x₀ := by
  intro M
  calc
    ∫ records, halfExpPP_sumTruncatedJumpSq M T records
        ∂M.canonicalRecordMeasure x₀
        =
      ∫ records,
        (∑ k ∈ Finset.range (N + 1),
          (let hist := Preorder.frestrictLe k records
           let x : Fin 3 → Fin (N + 1) :=
            CTMC.QMatrix.currentStateFromHistory
              (S := Fin 3 → Fin (N + 1)) k hist
           M.instantQVRate x *
            min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist)))
        ∂M.canonicalRecordMeasure x₀ := by
          simpa [M, halfExpPP_sumTruncatedJumpSq] using
            integral_sum_truncatedJumpSq_eq_integral_sum_clockTruncatedQV
              (M := M) x₀ T (N + 1)
    _ =
      ∑ k ∈ Finset.range (N + 1),
        ∫ records,
          (let hist := Preorder.frestrictLe k records
           let x : Fin 3 → Fin (N + 1) :=
            CTMC.QMatrix.currentStateFromHistory
              (S := Fin 3 → Fin (N + 1)) k hist
           M.instantQVRate x *
            min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist))
          ∂M.canonicalRecordMeasure x₀ := by
          simpa [M] using
            integral_sum_clockTruncatedQV_eq_sum_integral
              (M := M) x₀ T (N + 1)

private theorem halfExpPP_integrable_clockSkeletonSupSq
    (M : CTMC.DensityDepCTMC 3)
    (x₀ : Fin 3 → Fin (M.N + 1)) (T : ℝ) :
    MeasureTheory.Integrable
      (fun records => halfExpPP_clockSkeletonSupSq M T records)
      (M.canonicalRecordMeasure x₀) := by
  classical
  let n : ℕ := M.N + 1
  let μ := M.canonicalRecordMeasure x₀
  let V : M.canonicalRecordΩ → ℝ := fun records =>
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k =>
        ‖(fun i : Fin 3 =>
          M.canonicalFrozenClockTruncatedMartingale T i k records)‖ ^ 2)
  let C : Fin 3 → M.canonicalRecordΩ → ℝ := fun i records =>
    ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)) ^ 2
  have hC_int : ∀ i : Fin 3, MeasureTheory.Integrable (C i) μ := by
    intro i
    simpa [C, μ, n] using
      M.integrable_canonicalFrozenClockTruncatedMartingale_sup_sq x₀ T i n
  have hsumC_int : MeasureTheory.Integrable (fun records => ∑ i : Fin 3, C i records) μ :=
    MeasureTheory.integrable_finsetSum Finset.univ fun i _ => hC_int i
  have hV_meas : MeasureTheory.AEStronglyMeasurable V μ := by
    dsimp [V]
    refine (Finset.measurable_range_sup'' ?_).aestronglyMeasurable
    intro k _hk
    exact (measurable_norm.comp
      (by
        exact measurable_pi_lambda _ fun i =>
          (M.measurable_canonicalFrozenClockTruncatedMartingale_canonicalRecordFiltration
            T i k).mono (M.canonicalRecordFiltration.le k) le_rfl)).pow measurable_const
  have hpoint : ∀ records : M.canonicalRecordΩ, V records ≤ ∑ i : Fin 3, C i records := by
    intro records
    dsimp [V, C]
    refine Finset.sup'_le _ _ ?_
    intro k hk
    have hcoord :
        ‖(fun i : Fin 3 =>
          M.canonicalFrozenClockTruncatedMartingale T i k records)‖ ^ 2 ≤
        ∑ i : Fin 3,
          (M.canonicalFrozenClockTruncatedMartingale T i k records) ^ 2 :=
      Ripple.Kurtz.vector_norm_sq_le_sum_sq _
    refine hcoord.trans ?_
    refine Finset.sum_le_sum fun i _hi => ?_
    let S : ℝ :=
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)
    have hS_nonneg : 0 ≤ S := by
      exact (norm_nonneg _).trans
        (Finset.le_sup'
          (s := Finset.range (n + 1))
          (f := fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)
          (Finset.mem_range.mpr (Nat.succ_pos n)))
    have habs_le :
        |M.canonicalFrozenClockTruncatedMartingale T i k records| ≤ S := by
      simpa [S, Real.norm_eq_abs] using
        Finset.le_sup'
          (s := Finset.range (n + 1))
          (f := fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)
          hk
    have hsquare :
        (M.canonicalFrozenClockTruncatedMartingale T i k records) ^ 2 ≤ S ^ 2 := by
      rw [← sq_abs]
      exact sq_le_sq' (by
        nlinarith [hS_nonneg,
          abs_nonneg (M.canonicalFrozenClockTruncatedMartingale T i k records)]) habs_le
    simpa [S] using hsquare
  have hV_int : MeasureTheory.Integrable V μ := by
    refine hsumC_int.mono' hV_meas ?_
    refine Filter.Eventually.of_forall fun records => ?_
    have hV_nonneg : 0 ≤ V records := by
      dsimp [V]
      exact sq_nonneg _ |>.trans
        (Finset.le_sup'
          (s := Finset.range (n + 1))
          (f := fun k =>
            ‖(fun i : Fin 3 =>
              M.canonicalFrozenClockTruncatedMartingale T i k records)‖ ^ 2)
          (Finset.mem_range.mpr (Nat.succ_pos n)))
    have hsum_nonneg : 0 ≤ ∑ i : Fin 3, C i records := by
      exact Finset.sum_nonneg fun i _ => by
        dsimp [C]
        exact sq_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hV_nonneg, abs_of_nonneg hsum_nonneg]
      using hpoint records
  simpa [halfExpPP_clockSkeletonSupSq, V, n, μ] using hV_int

private theorem halfExpPP_integrable_sumTruncatedJumpSq
    (M : CTMC.DensityDepCTMC 3)
    (x₀ : Fin 3 → Fin (M.N + 1)) (T : ℝ) :
    MeasureTheory.Integrable
      (fun records => halfExpPP_sumTruncatedJumpSq M T records)
      (M.canonicalRecordMeasure x₀) := by
  classical
  unfold halfExpPP_sumTruncatedJumpSq
  exact MeasureTheory.integrable_finsetSum (Finset.range (M.N + 1)) fun k _ =>
    M.integrable_truncatedJumpSqIncrementFromHistory_next x₀ T k

private theorem halfExpPP_firstAbsIdx_start_sq_le_affineBridgeBound
    (N : ℕ) (hN : 0 < N) (T : ℝ)
    (records :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordΩ)
    (hAbsN :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
        (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap records).stateSeq N))
    (hsimplex : ∀ m,
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex
        (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap records).stateSeq m))
    (hhold_pos : ∀ n,
      ¬(CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
          (CTMC.QMatrix.currentStateFromHistory
            (S := Fin 3 → Fin (N + 1)) n (Preorder.frestrictLe n records)) →
        0 < (records (n + 1)).1)
    (hstate_abs : ∀ n,
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
          (CTMC.QMatrix.currentStateFromHistory
            (S := Fin 3 → Fin (N + 1)) n (Preorder.frestrictLe n records)) →
        (records (n + 1)).2 =
          CTMC.QMatrix.currentStateFromHistory
            (S := Fin 3 → Fin (N + 1)) n (Preorder.frestrictLe n records))
    (hhold_zero_abs : ∀ n,
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
          (CTMC.QMatrix.currentStateFromHistory
            (S := Fin 3 → Fin (N + 1)) n (Preorder.frestrictLe n records)) →
        (records (n + 1)).1 = 0)
    (hnext_ne : ∀ n,
      ¬(CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing
          (CTMC.QMatrix.currentStateFromHistory
            (S := Fin 3 → Fin (N + 1)) n (Preorder.frestrictLe n records)) →
        (records (n + 1)).2 ≠
          CTMC.QMatrix.currentStateFromHistory
            (S := Fin 3 → Fin (N + 1)) n (Preorder.frestrictLe n records))
    (hstartT :
      ((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap records).sojournStart
        (halfExpPP_firstAbsIdx N hN records hAbsN) ≤ T) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    let path := M.canonicalPathMap records
    let a := halfExpPP_firstAbsIdx N hN records hAbsN
    ‖M.frozenMartingalePart M.canonicalPathMap (path.sojournStart a) records‖ ^ 2 ≤
      (4 / 3 : ℝ) * halfExpPP_clockSkeletonSupSq M T records +
        4 * halfExpPP_sumTruncatedJumpSq M T records := by
  classical
  dsimp only
  let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  let path := M.canonicalPathMap records
  let a := halfExpPP_firstAbsIdx N hN records hAbsN
  have hbound_nonneg :
      0 ≤ (4 / 3 : ℝ) * halfExpPP_clockSkeletonSupSq M T records +
          4 * halfExpPP_sumTruncatedJumpSq M T records := by
    exact (halfExpPP_clockSkeletonSupSq_nonneg M T records).trans
      (halfExpPP_clockSkeletonSupSq_le_affineBridgeBound M T records)
  by_cases ha0 : a = 0
  · have hstart0 : path.sojournStart a = 0 := by
      simp [a, path, ha0, CTMC.CTMCPath.sojournStart]
    have hzero :
        M.frozenMartingalePart M.canonicalPathMap (path.sojournStart a) records = 0 := by
      rw [hstart0]
      ext i
      simp [CTMC.DensityDepCTMC.frozenMartingalePart,
        CTMC.DensityDepCTMC.frozenInitialCondition]
    rw [hzero]
    simpa using hbound_nonneg
  · have ha_pos : 0 < a := Nat.pos_of_ne_zero ha0
    let liveLast : ℕ := a - 1
    have ha_eq : a = liveLast + 1 := by
      simpa [liveLast] using (Nat.succ_pred_eq_of_pos ha_pos).symm
    have hnot_before : ∀ k, k < a → ¬M.toQMatrix.IsAbsorbing (path.stateSeq k) := by
      intro k hk
      simpa [M, path, a] using
        halfExpPP_not_absorbing_before_firstAbsIdx N hN records hAbsN hk
    have hlive_lt_a : liveLast < a := by
      omega
    have hcur_live :
        CTMC.QMatrix.currentStateFromHistory
            (S := Fin 3 → Fin (N + 1)) liveLast (Preorder.frestrictLe liveLast records) =
          path.stateSeq liveLast := by
      simpa [M, path] using halfExpPP_clockTail_currentState_eq_stateSeq M records liveLast
    have hlive_soj_pos : 0 < path.sojournTime liveLast := by
      rw [halfExpPP_clockTail_sojournTime_eq_record M records liveLast]
      exact hhold_pos liveLast (by
        rw [hcur_live]
        exact hnot_before liveLast hlive_lt_a)
    obtain ⟨hpos0, hstrict_prefix⟩ :=
      canonical_positive_sojourn_prefix_strict M records
        (by simpa [M] using hhold_pos)
        (by simpa [M] using hstate_abs)
        (by simpa [M] using hhold_zero_abs)
        hlive_soj_pos
    let path' := halfExpPP_strictCompletionThrough path liveLast
    have hcomp := halfExpPP_strictCompletionThrough_strict
      path liveLast hpos0 hstrict_prefix
    have hstart_eq :
        path'.sojournStart a = path.sojournStart a := by
      rw [ha_eq]
      simpa [path'] using
        halfExpPP_strictCompletionThrough_sojournStart_succ_eq path liveLast
    have hstate_tail_path : ∀ n,
        M.toQMatrix.IsAbsorbing (path.stateSeq n) →
          path.stateSeq (n + 1) = path.stateSeq n := by
      intro n hn
      have hcur := halfExpPP_clockTail_currentState_eq_stateSeq M records n
      have hnext := hstate_abs n (by simpa [M, path, hcur] using hn)
      simpa [M, path, CTMC.DensityDepCTMC.canonicalPathMap,
        CTMC.QMatrix.recordTrajectoryToPath_stateSeq, hcur] using hnext
    have hhold_zero_path : ∀ n,
        M.toQMatrix.IsAbsorbing (path.stateSeq n) →
          path.sojournTime n = 0 := by
      intro n hn
      have hcur := halfExpPP_clockTail_currentState_eq_stateSeq M records n
      have hzero := hhold_zero_abs n (by simpa [M, path, hcur] using hn)
      simpa [M, path, CTMC.DensityDepCTMC.canonicalPathMap,
        CTMC.QMatrix.recordTrajectoryToPath_sojournTime] using hzero
    have hhold_zero_record : ∀ n,
        M.toQMatrix.IsAbsorbing (path.stateSeq n) →
          (records (n + 1)).1 = 0 := by
      intro n hn
      have hcur := halfExpPP_clockTail_currentState_eq_stateSeq M records n
      exact hhold_zero_abs n (by simpa [M, path, hcur] using hn)
    obtain ⟨hstate_tail, hhold_zero_tail_record⟩ :=
      halfExpPP_absorbed_from_firstAbsIdx N hN records hAbsN
        (by simpa [M, path] using hstate_tail_path)
        (by simpa [M, path] using hhold_zero_record)
    have hhold_zero_tail : ∀ k, a ≤ k → path.sojournTime k = 0 := by
      intro k hk
      rw [halfExpPP_clockTail_sojournTime_eq_record M records k]
      exact hhold_zero_tail_record k hk
    have hstart_pos : 0 < path.sojournStart a := by
      have htime0_le : path.times 0 ≤ path.times liveLast :=
        halfExpPP_times_le_of_prefix path
          (Nat.zero_le liveLast) le_rfl hstrict_prefix
      rw [ha_eq]
      simpa [CTMC.CTMCPath.sojournStart] using lt_of_lt_of_le hpos0 htime0_le
    have hstate_path_start :
        path.frozenStateAt (path.sojournStart a) = path.stateSeq a := by
      exact halfExpPP_frozenStateAt_eq_stateSeq_of_firstAbsIdx_tail
        M records a hnot_before
        (by simpa [M] using hhold_pos)
        hstate_tail hhold_zero_tail
        (by simpa [M] using hnext_ne)
        le_rfl
    have hstate_path'_start :
        path'.frozenStateAt (path.sojournStart a) = path.stateSeq a := by
      have hmem' : path'.sojournStart a ∈ path'.sojournInterval a := by
        rw [ha_eq]
        constructor
        · simp [CTMC.CTMCPath.sojournInterval]
        · simpa [path', CTMC.CTMCPath.sojournInterval, CTMC.CTMCPath.sojournEnd,
            CTMC.CTMCPath.sojournStart] using hcomp.2 liveLast
      have hstate' :
          path'.frozenStateAt (path'.sojournStart a) = path'.stateSeq a :=
        halfExpPP_frozenStateAt_eq_stateSeq_of_mem_sojournInterval
          path' hcomp.2 a hmem'
      rw [← hstart_eq]
      rw [hstate']
      simpa [path'] using
        halfExpPP_strictCompletionThrough_stateSeq_eq path liveLast a
    have hstate_eq : ∀ t ∈ Set.Icc (0 : ℝ) (path.sojournStart a),
        path'.frozenStateAt t = path.frozenStateAt t := by
      intro t ht
      by_cases hlt : t < path.sojournStart a
      · rw [halfExpPP_strictCompletionThrough_frozenStateAt_eq_of_lt_succ
          path liveLast (by simpa [ha_eq] using hlt)]
      · have ht_eq : t = path.sojournStart a :=
          le_antisymm ht.2 (le_of_not_gt hlt)
        subst t
        rw [hstate_path'_start, hstate_path_start]
    have hEndpointTransfer :
        M.frozenMartingalePart M.canonicalPathMap (path.sojournStart a) records =
          M.frozenMartingalePart (fun _ : Unit => path') (path.sojournStart a) Unit.unit := by
      ext i
      simp only [CTMC.DensityDepCTMC.frozenMartingalePart,
        CTMC.DensityDepCTMC.frozenDensityProcess,
        CTMC.DensityDepCTMC.frozenInitialCondition, Pi.sub_apply]
      have hintegral :
          (∫ t in Set.Icc (0 : ℝ) (path.sojournStart a),
              (M.rateSpec.drift
                (fun j : Fin 3 => (↑(path.frozenStateAt t j) : ℝ) / ↑M.N)) i) =
            ∫ t in Set.Icc (0 : ℝ) (path.sojournStart a),
              (M.rateSpec.drift
                (fun j : Fin 3 => (↑(path'.frozenStateAt t j) : ℝ) / ↑M.N)) i := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        intro t ht
        simpa [hstate_eq t ht]
      have h0_state : path'.frozenStateAt 0 = path.frozenStateAt 0 := by
        exact hstate_eq 0 ⟨le_rfl, le_of_lt hstart_pos⟩
      change
          (↑((path.frozenStateAt (path.sojournStart a) i) : ℕ) : ℝ) / ↑M.N -
                (↑((path.frozenStateAt 0 i) : ℕ) : ℝ) / ↑M.N -
              ∫ t in Set.Icc (0 : ℝ) (path.sojournStart a),
                (M.rateSpec.drift
                  (fun j : Fin 3 => (↑(path.frozenStateAt t j) : ℝ) / ↑M.N)) i =
            (↑((path'.frozenStateAt (path.sojournStart a) i) : ℕ) : ℝ) / ↑M.N -
                (↑((path'.frozenStateAt 0 i) : ℕ) : ℝ) / ↑M.N -
              ∫ t in Set.Icc (0 : ℝ) (path.sojournStart a),
                (M.rateSpec.drift
                  (fun j : Fin 3 => (↑(path'.frozenStateAt t j) : ℝ) / ↑M.N)) i
      rw [hstate_path'_start, hstate_path_start, h0_state, hintegral]
    have hseq_path' : ∀ k < a, M.InSimplex (path'.stateSeq k) := by
      intro k hk
      have hstate : path'.stateSeq k = path.stateSeq k := by
        simpa [path'] using
          halfExpPP_strictCompletionThrough_stateSeq_eq path liveLast k
      simpa [M, path, hstate] using hsimplex k
    have hEndpoint' :
        M.frozenMartingalePart (fun _ : Unit => path') (path.sojournStart a) Unit.unit =
          fun i : Fin 3 => M.frozenTimeCompensatedJumpMartingale path' i a := by
      have h :=
        halfExpPP_frozenMartingalePart_at_sojournStart_eq_frozenTimeCompensated
          N hN path' hcomp.2 hcomp.1 a (by simpa [M] using hseq_path')
      simpa [M, path', hstart_eq] using h
    have hmp_eq :
        M.frozenMartingalePart M.canonicalPathMap (path.sojournStart a) records =
          fun i : Fin 3 => M.frozenTimeCompensatedJumpMartingale path i a := by
      calc
        M.frozenMartingalePart M.canonicalPathMap (path.sojournStart a) records
            = M.frozenMartingalePart (fun _ : Unit => path')
                (path.sojournStart a) Unit.unit := hEndpointTransfer
        _ = (fun i : Fin 3 => M.frozenTimeCompensatedJumpMartingale path' i a) := hEndpoint'
        _ = (fun i : Fin 3 => M.frozenTimeCompensatedJumpMartingale path i a) := by
              ext i
              rw [ha_eq]
              exact halfExpPP_strictCompletionThrough_frozenTimeCompensated_eq_succ
                M path i liveLast
    have hstrict_weak : ∀ n, n + 1 < a → path.times n < path.times (n + 1) := by
      intro n hn
      exact hstrict_prefix n (by omega)
    have hskel_eq :
        halfExpPP_clockSkeletonVec M T a records =
          fun i : Fin 3 => M.frozenTimeCompensatedJumpMartingale path i a := by
      simpa [M, path, a] using
        halfExpPP_clockSkeletonVec_eq_frozenTimeCompensated_weak
          M T records a hstrict_weak hpos0 hstartT
    have ha_mem : a ∈ Finset.range (M.N + 2) := by
      have ha_le_N : a ≤ N := by
        simpa [M, a] using halfExpPP_firstAbsIdx_le_N N hN records hAbsN
      change a ∈ Finset.range (N + 2)
      exact Finset.mem_range.mpr (by omega)
    rw [hmp_eq, ← hskel_eq]
    exact (halfExpPP_clockSkeletonVec_sq_le_sup M T records ha_mem).trans
      (halfExpPP_clockSkeletonSupSq_le_affineBridgeBound M T records)

private theorem halfExpPP_frozenMartingalePart_timeSup_sq_le_affineBridgeBound_ae
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1))
    (hinit : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x₀)
    {T : ℝ} :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2)
      ≤ (4 / 3 : ℝ) * halfExpPP_clockSkeletonSupSq M T records +
        4 * halfExpPP_sumTruncatedJumpSq M T records := by
  intro M
  filter_upwards
    [halfExpPP_canonical_stateSeq_absorbing_at_N_ae N hN x₀ hinit,
     M.canonicalPathMap_stateSeq_inSimplex_ae_of_conservative x₀
       (by simpa [M] using halfExpPP_conservativeJumps N hN)
       (by simpa [M] using hinit),
     M.toQMatrix.canonicalRecordMeasure_all_next_holdingTime_pos_ae_of_nonabsorbing x₀,
     canonicalRecordMeasure_all_next_state_eq_current_ae_of_absorbing_pre
       M.toQMatrix x₀,
     M.toQMatrix.canonicalRecordMeasure_all_next_holdingTime_eq_zero_ae_of_absorbing x₀,
     M.toQMatrix.canonicalRecordMeasure_all_next_state_ne_current_ae_of_nonabsorbing x₀]
    with records hAbsN hsimplex hhold_pos hstate_abs hhold_zero_abs hnext_ne
  have hbridge_nonneg :
      0 ≤ (4 / 3 : ℝ) * halfExpPP_clockSkeletonSupSq M T records +
        4 * halfExpPP_sumTruncatedJumpSq M T records := by
    exact (halfExpPP_clockSkeletonSupSq_nonneg M T records).trans
      (halfExpPP_clockSkeletonSupSq_le_affineBridgeBound M T records)
  refine Real.iSup_le ?_ hbridge_nonneg
  intro s
  refine Real.iSup_le ?_ hbridge_nonneg
  intro ⟨hs0, hsT⟩
  have hloc :=
    halfExpPP_locate_time_liveCell_or_absorbedTail N hN T s records hAbsN ⟨hs0, hsT⟩
  cases hloc with
  | inl hcell =>
    rcases hcell with ⟨k, hk_lt_a, hstart_le, hs_lt_next, hs_le_min⟩
    have ha_le_N : halfExpPP_firstAbsIdx N hN records hAbsN ≤ N := by
      simpa [M] using halfExpPP_firstAbsIdx_le_N N hN records hAbsN
    have hk_range : k ∈ Finset.range (N + 1) := by
      exact Finset.mem_range.mpr (by omega)
    have hstrict_prefix : ∀ n < k,
        (M.canonicalPathMap records).times n <
          (M.canonicalPathMap records).times (n + 1) := by
      exact halfExpPP_times_strict_prefix_before_firstAbsIdx
        N hN records hAbsN hhold_pos hk_lt_a
    have hpos0 : 0 < (M.canonicalPathMap records).times 0 := by
      by_cases hk0 : k = 0
      · subst hk0
        have : 0 < halfExpPP_firstAbsIdx N hN records hAbsN := by omega
        exact halfExpPP_time_zero_pos_before_firstAbsIdx N hN records hAbsN hhold_pos this
      · have : 0 < k := Nat.pos_of_ne_zero hk0
        exact halfExpPP_time_zero_pos_before_firstAbsIdx N hN records hAbsN hhold_pos
          (lt_trans this hk_lt_a)
    exact halfExpPP_frozenMartingalePart_live_sq_le_affineBridgeBound
      N hN T s records k hk_range
      (fun n hn => hstrict_prefix n hn)
      hpos0
      (fun m hm => hsimplex m)
      hstart_le hs_lt_next hs_le_min
  | inr htail =>
    have hstartT : (M.canonicalPathMap records).sojournStart
        (halfExpPP_firstAbsIdx N hN records hAbsN) ≤ T :=
      le_trans htail hsT
    obtain ⟨hstate_tail, hhold_zero_tail_record⟩ :=
      halfExpPP_absorbed_from_firstAbsIdx N hN records hAbsN
        (fun n hn => by
          have hcur := halfExpPP_clockTail_currentState_eq_stateSeq M records n
          have hnext := hstate_abs n (by simpa [M, hcur] using hn)
          simpa [M, CTMC.DensityDepCTMC.canonicalPathMap,
            CTMC.QMatrix.recordTrajectoryToPath_stateSeq, hcur] using hnext)
        (fun n hn => by
          have hcur := halfExpPP_clockTail_currentState_eq_stateSeq M records n
          exact hhold_zero_abs n (by simpa [M, hcur] using hn))
    have hhold_zero_tail : ∀ k,
        halfExpPP_firstAbsIdx N hN records hAbsN ≤ k →
          (M.canonicalPathMap records).sojournTime k = 0 := by
      intro k hk
      rw [halfExpPP_clockTail_sojournTime_eq_record M records k]
      exact hhold_zero_tail_record k hk
    have htail_eq :=
      halfExpPP_frozenMartingalePart_tail_eq_start
        M records (halfExpPP_firstAbsIdx N hN records hAbsN)
        (fun k hk => halfExpPP_not_absorbing_before_firstAbsIdx N hN records hAbsN hk)
        hhold_pos
        hstate_tail
        hhold_zero_tail
        hnext_ne
        (halfExpPP_driftZeroAtAbsorbingOnSimplex N hN
          ((M.canonicalPathMap records).stateSeq (halfExpPP_firstAbsIdx N hN records hAbsN))
          (hsimplex _)
          (by
            have := halfExpPP_firstAbsIdx_spec N hN records hAbsN
            simpa [M, CTMC.QMatrix.IsAbsorbing] using this))
        htail
    rw [htail_eq]
    exact halfExpPP_firstAbsIdx_start_sq_le_affineBridgeBound
      N hN T records hAbsN (fun m => hsimplex m)
      hhold_pos hstate_abs hhold_zero_abs hnext_ne hstartT

private theorem halfExpPP_clockQV_sum_ae_le_frozenQV_setIntegral
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1))
    (hinit : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x₀)
    {T : ℝ} (hT : 0 ≤ T) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      (∑ k ∈ Finset.range N,
        (let hist := Preorder.frestrictLe k records
         let x : Fin 3 → Fin (N + 1) :=
          CTMC.QMatrix.currentStateFromHistory
            (S := Fin 3 → Fin (N + 1)) k hist
         M.instantQVRate x *
          min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist))) ≤
      ∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s) := by
  intro M
  filter_upwards
    [halfExpPP_canonical_stateSeq_absorbing_at_N_ae N hN x₀ hinit,
     M.toQMatrix.canonicalRecordMeasure_all_next_holdingTime_pos_ae_of_nonabsorbing x₀,
     canonicalRecordMeasure_all_next_state_eq_current_ae_of_absorbing_pre
       M.toQMatrix x₀,
     M.toQMatrix.canonicalRecordMeasure_all_next_holdingTime_eq_zero_ae_of_absorbing x₀,
     M.toQMatrix.canonicalRecordMeasure_all_next_state_ne_current_ae_of_nonabsorbing x₀]
    with records hAbsN hhold_pos hstate_abs hhold_zero_abs hnext_ne
  let path := M.canonicalPathMap records
  let a := halfExpPP_firstAbsIdx N hN records hAbsN
  have ha_le_N : a ≤ N := by
    simpa [M, a] using halfExpPP_firstAbsIdx_le_N N hN records hAbsN
  have hconv : ∀ k,
      (let hist := Preorder.frestrictLe k records
       let x := CTMC.QMatrix.currentStateFromHistory
         (S := Fin 3 → Fin (N + 1)) k hist
       M.instantQVRate x *
        min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist)) =
      M.instantQVRate (path.stateSeq k) *
        min (path.sojournTime k) (max 0 (T - path.sojournStart k)) := by
    intro k
    have hcur :
        CTMC.QMatrix.currentStateFromHistory
            (S := Fin 3 → Fin (N + 1)) k (Preorder.frestrictLe k records) =
          path.stateSeq k := by
      simpa [M, path] using
        halfExpPP_clockTail_currentState_eq_stateSeq M records k
    have hsoj : (records (k + 1)).1 = path.sojournTime k := by
      simpa [path] using
        (halfExpPP_clockTail_sojournTime_eq_record M records k).symm
    have hremaining :
        CTMC.QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records) =
          max 0 (T - path.sojournStart k) := by
      have hraw :
          CTMC.QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records) =
            max 0 (T - (M.canonicalPathMap records).sojournStart k) := by
        simp [CTMC.QMatrix.historyClockRemaining,
          CTMC.QMatrix.historySojournStart_frestrictLe,
          CTMC.DensityDepCTMC.canonicalPathMap]
      simpa [path] using hraw
    change
      M.instantQVRate
          (CTMC.QMatrix.currentStateFromHistory
            (S := Fin 3 → Fin (N + 1)) k (Preorder.frestrictLe k records)) *
        min (records (k + 1)).1
          (CTMC.QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records)) =
      M.instantQVRate (path.stateSeq k) *
        min (path.sojournTime k) (max 0 (T - path.sojournStart k))
    rw [hcur, hsoj, hremaining]
  rw [Finset.sum_congr rfl (fun k _ => hconv k)]
  have hnot_before : ∀ k, k < a →
      ¬M.toQMatrix.IsAbsorbing (path.stateSeq k) := by
    intro k hk
    simpa [M, path, a] using
      halfExpPP_not_absorbing_before_firstAbsIdx N hN records hAbsN hk
  have haAbs : M.toQMatrix.IsAbsorbing (path.stateSeq a) := by
    simpa [M, path, a] using halfExpPP_firstAbsIdx_spec N hN records hAbsN
  obtain ⟨hstate_tail, hhold_zero_tail_record⟩ :=
    halfExpPP_absorbed_from_firstAbsIdx N hN records hAbsN
      (fun n hn => by
        have hcur := halfExpPP_clockTail_currentState_eq_stateSeq M records n
        have hnext := hstate_abs n (by rwa [hcur])
        simpa [M, CTMC.DensityDepCTMC.canonicalPathMap,
          CTMC.QMatrix.recordTrajectoryToPath_stateSeq, hcur] using hnext)
      (fun n hn => by
        have hcur := halfExpPP_clockTail_currentState_eq_stateSeq M records n
        exact hhold_zero_abs n (by rwa [hcur]))
  have hhold_zero_tail : ∀ k, a ≤ k → path.sojournTime k = 0 := by
    intro k hk
    rw [halfExpPP_clockTail_sojournTime_eq_record M records k]
    exact hhold_zero_tail_record k hk
  have hqv_zero : ∀ k, a ≤ k → M.instantQVRate (path.stateSeq k) = 0 := by
    intro k hk
    have hstate_k : path.stateSeq k = path.stateSeq a := hstate_tail k hk
    rw [hstate_k]
    exact M.instantQVRate_eq_zero_of_exitRateAt_zero
      (by simpa [CTMC.DensityDepCTMC.exitRateAt] using haAbs)
  have hsum_split :
      (∑ k ∈ Finset.range N,
        M.instantQVRate (path.stateSeq k) *
          min (path.sojournTime k) (max 0 (T - path.sojournStart k))) =
      ∑ k ∈ Finset.range a,
        M.instantQVRate (path.stateSeq k) *
          min (path.sojournTime k) (max 0 (T - path.sojournStart k)) := by
    symm
    apply Finset.sum_subset (Finset.range_mono ha_le_N)
    intro k hkN hka
    have hka' : a ≤ k := Nat.le_of_not_gt (by
      intro h; exact hka (Finset.mem_range.mpr h))
    simp [hqv_zero k hka']
  rw [hsum_split]
  by_cases ha0 : a = 0
  · simp [ha0]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun s _hs =>
      M.instantQVRate_nonneg _
  · have ha_pos : 0 < a := Nat.pos_of_ne_zero ha0
    let liveLast : ℕ := a - 1
    have hlive_succ : liveLast + 1 = a := Nat.succ_pred_eq_of_pos ha_pos
    have hlive_lt_a : liveLast < a := by omega
    have hlive_soj_pos : 0 < path.sojournTime liveLast := by
      rw [halfExpPP_clockTail_sojournTime_eq_record M records liveLast]
      exact hhold_pos liveLast (by
        rw [halfExpPP_clockTail_currentState_eq_stateSeq M records liveLast]
        exact hnot_before liveLast hlive_lt_a)
    obtain ⟨hpos0, hstrict_prefix⟩ :=
      canonical_positive_sojourn_prefix_strict M records
        (by simpa [M] using hhold_pos)
        (by simpa [M] using hstate_abs)
        (by simpa [M] using hhold_zero_abs)
        hlive_soj_pos
    let path' := halfExpPP_strictCompletionThrough path liveLast
    have hcomp := halfExpPP_strictCompletionThrough_strict
      path liveLast hpos0 hstrict_prefix
    have hstate_eq : ∀ k, k < a → path'.stateSeq k = path.stateSeq k := by
      intro k hk
      simpa [path'] using
        halfExpPP_strictCompletionThrough_stateSeq_eq path liveLast k
    have hfuture : ∃ n, T < path'.times n := by
      obtain ⟨m, hm⟩ := exists_nat_gt (T - path.times liveLast)
      refine ⟨liveLast + (m + 1), ?_⟩
      have hnot : ¬ liveLast + (m + 1) ≤ liveLast := by omega
      have hsub : liveLast + (m + 1) - liveLast = m + 1 := by omega
      have htime :
          path'.times (liveLast + (m + 1)) =
            path.times liveLast + (m + 1 : ℝ) := by
        simp [path', halfExpPP_strictCompletionThrough, hnot, hsub]
      have hm' : (m : ℝ) < (m + 1 : ℝ) := by
        exact_mod_cast Nat.lt_succ_self m
      rw [htime]
      nlinarith
    have hbridge :=
      frozenClockTruncatedQV_sum_range_le_setIntegral
        M path' hcomp.2 hcomp.1 hT hfuture a
    calc
      (∑ k ∈ Finset.range a,
        M.instantQVRate (path.stateSeq k) *
          min (path.sojournTime k) (max 0 (T - path.sojournStart k)))
      = ∑ k ∈ Finset.range a,
          M.instantQVRate (path'.stateSeq k) *
            min (path'.sojournTime k) (max 0 (T - path'.sojournStart k)) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hk_lt_a := Finset.mem_range.mp hk
            have hk_le : k ≤ liveLast := by omega
            rw [halfExpPP_strictCompletionThrough_stateSeq_eq path liveLast k,
              halfExpPP_strictCompletionThrough_sojournTime_eq_of_le path (n := liveLast) hk_le,
              halfExpPP_strictCompletionThrough_sojournStart_eq_of_le path liveLast k hk_le]
      _ ≤ ∫ t in Set.Icc (0 : ℝ) T,
            M.instantQVRate (path'.frozenStateAt t) := hbridge
      _ = ∫ t in Set.Icc (0 : ℝ) T,
            M.instantQVRate (path.frozenStateAt t) := by
            have hstart_eq : path'.sojournStart a = path.sojournStart a := by
              rw [← hlive_succ]
              simpa [path'] using
                halfExpPP_strictCompletionThrough_sojournStart_succ_eq path liveLast
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
            intro t ht
            by_cases hlt : t < path.sojournStart a
            · have hlt_succ : t < path.sojournStart (liveLast + 1) := by
                simpa [hlive_succ] using hlt
              have hstate :
                  path'.frozenStateAt t = path.frozenStateAt t := by
                rw [halfExpPP_strictCompletionThrough_frozenStateAt_eq_of_lt_succ
                  path liveLast hlt_succ]
              simpa [hstate]
            · have htail_t : path.sojournStart a ≤ t := le_of_not_gt hlt
              have hstate_path :
                  path.frozenStateAt t = path.stateSeq a :=
                halfExpPP_frozenStateAt_eq_stateSeq_of_firstAbsIdx_tail
                  M records a hnot_before hhold_pos hstate_tail hhold_zero_tail
                  hnext_ne htail_t
              have hqv_path : M.instantQVRate (path.frozenStateAt t) = 0 := by
                rw [hstate_path]
                exact hqv_zero a le_rfl
              have hfuture_t : ∃ n, t < path'.times n := by
                rcases hfuture with ⟨n, hn⟩
                exact ⟨n, lt_of_le_of_lt ht.2 hn⟩
              have hstate_path' :
                  path'.frozenStateAt t = path'.stateSeq (path'.jumpCount t) := by
                exact CTMC.DensityDepCTMC.frozenStateAt_eq_stateSeq_jumpCount_of_mem_currentSojourn
                  path' hcomp.2 hfuture_t
                  ⟨path'.sojournStart_jumpCount_le_of_exists ht.1 hfuture_t, le_rfl⟩
              have hj_ge_a : a ≤ path'.jumpCount t := by
                by_contra hnot_ge
                have hjlt : path'.jumpCount t < a := Nat.lt_of_not_ge hnot_ge
                have hmem := path'.mem_sojournInterval_jumpCount ht.1 hfuture_t
                have hend_le :
                    path'.sojournEnd (path'.jumpCount t) ≤ path'.sojournStart a :=
                  path'.sojournEnd_le_sojournStart_of_lt hcomp.2 hjlt
                have htail_t' : path'.sojournStart a ≤ t := by
                  simpa [hstart_eq] using htail_t
                exact (not_lt_of_ge (le_trans hend_le htail_t')) hmem.2
              have hqv_path' : M.instantQVRate (path'.frozenStateAt t) = 0 := by
                rw [hstate_path']
                have hsseq :
                    path'.stateSeq (path'.jumpCount t) =
                      path.stateSeq (path'.jumpCount t) := by
                  simpa [path'] using
                    halfExpPP_strictCompletionThrough_stateSeq_eq
                      path liveLast (path'.jumpCount t)
                rw [hsseq]
                exact hqv_zero (path'.jumpCount t) hj_ge_a
              change M.instantQVRate (path'.frozenStateAt t) =
                M.instantQVRate (path.frozenStateAt t)
              exact hqv_path'.trans hqv_path.symm

private theorem halfExpPP_sum_clockTruncatedQV_integral_range_N_le_frozenInstantQVRate_integral
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1))
    (hinit : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x₀)
    {T : ℝ} (hT : 0 ≤ T) :
    let M : CTMC.DensityDepCTMC 3 :=
      CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    (∑ k ∈ Finset.range N,
      ∫ records,
        (let hist := Preorder.frestrictLe k records
         let x : Fin 3 → Fin (N + 1) :=
          CTMC.QMatrix.currentStateFromHistory (S := Fin 3 → Fin (N + 1)) k hist
         M.instantQVRate x *
          min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist))
        ∂M.canonicalRecordMeasure x₀) ≤
      ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
        ∂M.canonicalRecordMeasure x₀ := by
  classical
  dsimp only
  let M : CTMC.DensityDepCTMC 3 :=
    CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  let μ := M.canonicalRecordMeasure x₀
  have hsum_int :
      (∑ k ∈ Finset.range N,
        ∫ records,
          (let hist := Preorder.frestrictLe k records
           let x : Fin 3 → Fin (N + 1) :=
            CTMC.QMatrix.currentStateFromHistory (S := Fin 3 → Fin (N + 1)) k hist
           M.instantQVRate x *
            min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist))
          ∂μ) =
        ∫ records,
          (∑ k ∈ Finset.range N,
            (let hist := Preorder.frestrictLe k records
             let x : Fin 3 → Fin (N + 1) :=
              CTMC.QMatrix.currentStateFromHistory (S := Fin 3 → Fin (N + 1)) k hist
             M.instantQVRate x *
              min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist)))
          ∂μ := by
    simpa [M, μ] using
      (integral_sum_clockTruncatedQV_eq_sum_integral (M := M) x₀ T N).symm
  rw [hsum_int]
  have hleft_int : MeasureTheory.Integrable
      (fun records : M.canonicalRecordΩ =>
        ∑ k ∈ Finset.range N,
          (let hist := Preorder.frestrictLe k records
           let x : Fin 3 → Fin (N + 1) :=
            CTMC.QMatrix.currentStateFromHistory (S := Fin 3 → Fin (N + 1)) k hist
           M.instantQVRate x *
            min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist))) μ := by
    exact MeasureTheory.integrable_finsetSum (Finset.range N) fun k _hk => by
      simpa [M, μ] using M.integrable_clockTruncatedQVIncrement x₀ T k
  have hright_int : MeasureTheory.Integrable
      (fun records : M.canonicalRecordΩ =>
        ∫ s in Set.Icc (0 : ℝ) T,
          M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s)) μ := by
    simpa [M, μ] using
      integrable_canonicalFrozenInstantQVRate_setIntegral M x₀ T hT
  have hpoint :
      (fun records : M.canonicalRecordΩ =>
        ∑ k ∈ Finset.range N,
          (let hist := Preorder.frestrictLe k records
           let x : Fin 3 → Fin (N + 1) :=
            CTMC.QMatrix.currentStateFromHistory (S := Fin 3 → Fin (N + 1)) k hist
           M.instantQVRate x *
            min (records (k + 1)).1 (CTMC.QMatrix.historyClockRemaining T k hist)))
      ≤ᵐ[μ]
      fun records : M.canonicalRecordΩ =>
        ∫ s in Set.Icc (0 : ℝ) T,
          M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s) := by
    simpa [M, μ] using
      halfExpPP_clockQV_sum_ae_le_frozenQV_setIntegral N hN x₀ hinit hT
  exact MeasureTheory.integral_mono_ae hleft_int hright_int hpoint

/-- Residual stochastic bridge after the completed-sojourn endpoint algebra
has been discharged.  What remains is the stopped random-index Doob/QV
comparison for the continuous-time interpolation. -/
private theorem halfExpPP_frozenMartingalePart_DoobL2_clock_bridge_residual
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1))
    (_hinit : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x₀)
    (hJumpBridge :
      ∀ (path : CTMC.CTMCPath (Fin 3 → Fin (N + 1)))
        (hstrict : ∀ n, path.times n < path.times (n + 1))
        (hpos : 0 < path.times 0) (n : ℕ),
        (∀ k < n,
          (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex
            (path.stateSeq k)) →
        (let M : CTMC.DensityDepCTMC 3 :=
          CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
        M.frozenMartingalePart (fun _ : Unit => path) (path.sojournStart n) Unit.unit =
          fun i => M.frozenTimeCompensatedJumpMartingale path i n)) :
    ∀ T > 0,
      let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      16 * ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
        ∂M.canonicalRecordMeasure x₀ := by
  intro T hT
  let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  let μ := M.canonicalRecordMeasure x₀
  let lhs : ℝ :=
    ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
      ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2
      ∂μ
  let rhs : ℝ :=
    ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
      M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
      ∂μ
  change lhs ≤ 16 * rhs
  have hEndpoint := hJumpBridge
  have hRHS_nonneg : 0 ≤ rhs := by
    dsimp [rhs]
    exact MeasureTheory.integral_nonneg fun records =>
      MeasureTheory.setIntegral_nonneg measurableSet_Icc fun s _hs =>
        M.instantQVRate_nonneg ((M.canonicalPathMap records).frozenStateAt s)
  have hLHS_finite : ∃ K > 0, lhs ≤ K := by
    obtain ⟨K, hK_pos, hK_bound⟩ :=
      M.exists_frozen_martingale_sup_sq_bound M.canonicalPathMap T (le_of_lt hT)
    refine ⟨K, hK_pos, ?_⟩
    dsimp [lhs, μ]
    calc
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2
          ∂M.canonicalRecordMeasure x₀
          ≤ ∫ _records, K ∂M.canonicalRecordMeasure x₀ := by
            exact MeasureTheory.integral_mono_ae
              (M.canonical_frozen_martingale_sup_sq_integrable x₀ T hT)
              (MeasureTheory.integrable_const K)
              (Filter.Eventually.of_forall fun records => hK_bound records)
      _ = K := by simp
  have hStoppedDoobBridge :
      lhs ≤ 16 * rhs := by
    by_cases hzero : rhs = 0
    · have hZeroEnergyAbsorbing : lhs = 0 := by
        by_cases habs : M.toQMatrix.IsAbsorbing x₀
        · have hMzero :
              ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ t : ℝ,
                M.frozenMartingalePart M.canonicalPathMap t records = 0 := by
            simpa [M] using
              halfExpPP_canonical_frozenMartingalePart_eq_zero_ae_of_absorbing_pre
                N hN x₀ _hinit (by simpa [M] using habs)
          dsimp [lhs, μ]
          have hsup_zero :
              (fun records : M.canonicalRecordΩ =>
                ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
                  ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2)
                =ᵐ[M.canonicalRecordMeasure x₀] fun _ => 0 := by
            filter_upwards [hMzero] with records hz
            simp [hz]
          simpa using MeasureTheory.integral_eq_zero_of_ae hsup_zero
        · exfalso
          have hrhs_pos : 0 < rhs := by
            dsimp [rhs, μ]
            simpa [M] using
              halfExpPP_frozenQV_energy_expectation_pos_of_nonabsorbing
                N hN x₀ _hinit hT (by simpa [M] using habs)
          exact (ne_of_gt hrhs_pos) hzero
      rw [hZeroEnergyAbsorbing, hzero]
      norm_num
    · have hRHS_pos : 0 < rhs := lt_of_le_of_ne hRHS_nonneg (Ne.symm hzero)
      have hStoppedDoobL2 :
          lhs ≤ 16 * rhs := by
        /-
        Blocker: this is the missing stopped random-index Doob/QV-to-clock
        bridge for the absorbing-aware frozen martingale:
        1. lift `hEndpoint` from deterministic sojourn boundaries to
           `jumpCountTop T`;
        2. apply optional stopping to
           `shiftedFrozenMartingale_sq_minus_qvComp_supermartingale`;
        3. use the fixed-index maximal inequality for
           `frozenScaledJumpMartingale`;
        4. identify the stopped guarded QV compensator with the clock integral
           of `instantQVRate` along `frozenStateAt`.

        The existing `FrozenRandomIndexDoob` file has the guarded fixed-index
        martingale, layer-cake, and supermartingale pieces.  It does not yet
        contain the random stopping-time maximal inequality or the stopped
        guarded-QV-compensator/clock-integral identification needed for the
        fixed constant `16`.
        -/
        have hae_bound :=
          halfExpPP_frozenMartingalePart_timeSup_sq_le_affineBridgeBound_ae
            N hN x₀ _hinit (T := T)
        have hSkel :=
          halfExpPP_integral_clockSkeletonSupSq_le_eight_clockQV_sum N hN x₀ T
        have hJump :=
          halfExpPP_integral_sumTruncatedJumpSq_eq_clockQV_sum N hN x₀ T
        have hDrop :=
          halfExpPP_sum_clockTruncatedQV_integral_range_succ_absorb_eq_range
            N hN x₀ _hinit T
        dsimp [M] at hSkel hJump hDrop hae_bound
        let S : ℝ :=
          ∑ k ∈ Finset.range (N + 1),
            ∫ records,
              (let hist := Preorder.frestrictLe k records
               let x : Fin 3 → Fin (N + 1) :=
                CTMC.QMatrix.currentStateFromHistory
                  (S := Fin 3 → Fin (N + 1)) k hist
               (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).instantQVRate x *
                min (records (k + 1)).1
                  (CTMC.QMatrix.historyClockRemaining T k hist))
              ∂(CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordMeasure x₀
        dsimp [lhs, rhs, μ]
        have hint_bound : (∫ records,
              ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
                ‖(CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).frozenMartingalePart
                  (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
                  s records‖ ^ 2
              ∂(CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordMeasure x₀)
            ≤ (44 / 3 : ℝ) * S := by
            let M0 : CTMC.DensityDepCTMC 3 :=
              CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
            let μ0 := M0.canonicalRecordMeasure x₀
            let F : M0.canonicalRecordΩ → ℝ := fun records =>
              ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
                ‖M0.frozenMartingalePart M0.canonicalPathMap s records‖ ^ 2
            let A : M0.canonicalRecordΩ → ℝ := fun records =>
              (4 / 3 : ℝ) * halfExpPP_clockSkeletonSupSq M0 T records +
                4 * halfExpPP_sumTruncatedJumpSq M0 T records
            have hF_int : MeasureTheory.Integrable F μ0 := by
              simpa [F, μ0, M0] using
                M0.canonical_frozen_martingale_sup_sq_integrable x₀ T hT
            have hSkel_int :
                MeasureTheory.Integrable
                  (fun records => halfExpPP_clockSkeletonSupSq M0 T records) μ0 := by
              simpa [M0, μ0] using
                halfExpPP_integrable_clockSkeletonSupSq M0 x₀ T
            have hJump_int :
                MeasureTheory.Integrable
                  (fun records => halfExpPP_sumTruncatedJumpSq M0 T records) μ0 := by
              simpa [M0, μ0] using
                halfExpPP_integrable_sumTruncatedJumpSq M0 x₀ T
            have hA_int : MeasureTheory.Integrable A μ0 := by
              simpa [A] using
                (hSkel_int.const_mul (4 / 3 : ℝ)).add (hJump_int.const_mul 4)
            have hmono : ∫ records, F records ∂μ0 ≤ ∫ records, A records ∂μ0 := by
              exact MeasureTheory.integral_mono_ae hF_int hA_int (by
                simpa [F, A, M0, μ0] using hae_bound)
            have hSkel_le :
                ∫ records, halfExpPP_clockSkeletonSupSq M0 T records ∂μ0 ≤
                  8 * S := by
              simpa [S, M0, μ0] using hSkel
            have hJump_eq :
                ∫ records, halfExpPP_sumTruncatedJumpSq M0 T records ∂μ0 =
                  S := by
              simpa [S, M0, μ0] using hJump
            calc
              ∫ records, F records ∂μ0
                  ≤ ∫ records, A records ∂μ0 := hmono
              _ =
                  (4 / 3 : ℝ) *
                    ∫ records, halfExpPP_clockSkeletonSupSq M0 T records ∂μ0 +
                  4 * ∫ records, halfExpPP_sumTruncatedJumpSq M0 T records ∂μ0 := by
                    rw [MeasureTheory.integral_add]
                    · rw [MeasureTheory.integral_const_mul,
                        MeasureTheory.integral_const_mul]
                    · exact hSkel_int.const_mul (4 / 3 : ℝ)
                    · exact hJump_int.const_mul 4
              _ ≤ (4 / 3 : ℝ) * (8 * S) + 4 * S := by
                    have hmul := mul_le_mul_of_nonneg_left hSkel_le (by norm_num : (0 : ℝ) ≤ 4 / 3)
                    rw [hJump_eq]
                    nlinarith
              _ = (44 / 3 : ℝ) * S := by ring
        have hS_le_rhs : S ≤
            ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
              (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).instantQVRate
                (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
                  records).frozenStateAt s))
            ∂(CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordMeasure x₀ := by
          calc
            S =
                ∑ k ∈ Finset.range N,
                  ∫ records,
                    (let hist := Preorder.frestrictLe k records
                     let x : Fin 3 → Fin (N + 1) :=
                      CTMC.QMatrix.currentStateFromHistory
                        (S := Fin 3 → Fin (N + 1)) k hist
                     (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).instantQVRate x *
                      min (records (k + 1)).1
                        (CTMC.QMatrix.historyClockRemaining T k hist))
                    ∂(CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordMeasure x₀ := by
                  simpa [S] using hDrop
            _ ≤
                ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
                  (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).instantQVRate
                    (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
                      records).frozenStateAt s))
                ∂(CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordMeasure x₀ := by
                  simpa using
                    halfExpPP_sum_clockTruncatedQV_integral_range_N_le_frozenInstantQVRate_integral
                      N hN x₀ _hinit (le_of_lt hT)
        calc
          ∫ records,
            ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
              ‖(CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).frozenMartingalePart
                (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
                s records‖ ^ 2
            ∂(CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordMeasure x₀
          ≤ (44 / 3 : ℝ) * S := hint_bound
          _ ≤ 16 * S := by
            have hS_nonneg : (0 : ℝ) ≤ S := by
              rw [show S = ∫ records,
                    halfExpPP_sumTruncatedJumpSq
                      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec) T records
                    ∂(CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordMeasure x₀
                  from hJump.symm]
              exact MeasureTheory.integral_nonneg fun records =>
                halfExpPP_sumTruncatedJumpSq_nonneg
                  (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec) T records
            nlinarith
          _ ≤ 16 * ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
              (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).instantQVRate
                (((CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalPathMap
                  records).frozenStateAt s))
            ∂(CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordMeasure x₀ := by
            exact mul_le_mul_of_nonneg_left hS_le_rhs (by norm_num)
      exact hStoppedDoobL2
  exact hStoppedDoobBridge

/-- Doob L2 maximal inequality for the piecewise-linear frozen martingale of
`halfExpPP`.  The sharp discrete-time constant is 4; the non-sharp constant 16
leaves room for the continuous interpolation and stopping-time presentation.

The fixed jump-index guarded martingale and maximal-inequality components live
in `Ripple.CTMC.FrozenRandomIndexDoob`; the remaining bridge is the stopped
random-index/continuous-time interpolation below. -/
private theorem halfExpPP_frozenMartingalePart_DoobL2_clock_bridge
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1))
    (_hinit : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x₀) :
    ∀ T > 0,
      let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      16 * ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
        ∂M.canonicalRecordMeasure x₀ := by
  intro T hT
  exact halfExpPP_frozenMartingalePart_DoobL2_clock_bridge_residual
    N hN x₀ _hinit
    (fun path hstrict hpos n hseq =>
      halfExpPP_frozenMartingalePart_at_sojournStart_eq_frozenTimeCompensated
        N hN path hstrict hpos n hseq)
    T hT

theorem halfExpPPFrozenDoobL2_holds : halfExpPPFrozenDoobL2 16 := by
  intro N hN x₀ hinit T hT
  exact halfExpPP_frozenMartingalePart_DoobL2_clock_bridge N hN x₀ hinit T hT

private theorem canonicalRecordMeasure_all_next_state_eq_current_ae_of_absorbing
    {S : Type*} [Fintype S] [DecidableEq S] [Countable S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (Q : CTMC.QMatrix S) (s₀ : S) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀, ∀ n,
      Q.IsAbsorbing
          (CTMC.QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records)) →
        (records (n + 1)).2 =
          CTMC.QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records) := by
  refine MeasureTheory.ae_all_iff.mpr ?_
  intro n
  let μ := Q.canonicalRecordMeasure s₀
  let X : ((m : ℕ) → CTMC.QMatrix.JumpHoldTrajectorySpace S m) →
      ((i : Finset.Iic n) → CTMC.QMatrix.JumpHoldTrajectorySpace S i) :=
    Preorder.frestrictLe n
  let Y : ((m : ℕ) → CTMC.QMatrix.JumpHoldTrajectorySpace S m) →
      CTMC.QMatrix.JumpHoldTrajectorySpace S (n + 1) :=
    fun records => records (n + 1)
  let p :
      (((i : Finset.Iic n) → CTMC.QMatrix.JumpHoldTrajectorySpace S i) ×
        CTMC.QMatrix.JumpHoldTrajectorySpace S (n + 1)) → Prop :=
    fun z =>
      Q.IsAbsorbing (CTMC.QMatrix.currentStateFromHistory (S := S) n z.1) →
        z.2.2 = CTMC.QMatrix.currentStateFromHistory (S := S) n z.1
  have hp : MeasurableSet {z | p z} := by
    have h_abs : MeasurableSet
        {z : (((i : Finset.Iic n) → CTMC.QMatrix.JumpHoldTrajectorySpace S i) ×
            CTMC.QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          Q.IsAbsorbing (CTMC.QMatrix.currentStateFromHistory (S := S) n z.1)} := by
      exact ((CTMC.QMatrix.measurable_currentStateFromHistory (S := S) n).comp measurable_fst)
        ((Set.to_countable {s : S | Q.IsAbsorbing s}).measurableSet)
    have h_eq : MeasurableSet
        {z : (((i : Finset.Iic n) → CTMC.QMatrix.JumpHoldTrajectorySpace S i) ×
            CTMC.QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          z.2.2 = CTMC.QMatrix.currentStateFromHistory (S := S) n z.1} :=
      measurableSet_eq_fun (measurable_snd.comp measurable_snd)
        ((CTMC.QMatrix.measurable_currentStateFromHistory (S := S) n).comp measurable_fst)
    rw [show {z | p z} =
        {z : (((i : Finset.Iic n) → CTMC.QMatrix.JumpHoldTrajectorySpace S i) ×
            CTMC.QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          ¬ Q.IsAbsorbing (CTMC.QMatrix.currentStateFromHistory (S := S) n z.1)} ∪
        {z : (((i : Finset.Iic n) → CTMC.QMatrix.JumpHoldTrajectorySpace S i) ×
            CTMC.QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          z.2.2 = CTMC.QMatrix.currentStateFromHistory (S := S) n z.1} by
      ext z
      by_cases h : Q.IsAbsorbing (CTMC.QMatrix.currentStateFromHistory (S := S) n z.1)
      · simp [p, h]
      · simp [p, h]]
    exact h_abs.compl.union h_eq
  have hkernel :
      ∀ᵐ hist ∂μ.map X,
        ∀ᵐ r ∂Q.jumpHoldTrajectoryStepKernel n hist, p (hist, r) := by
    refine Filter.Eventually.of_forall ?_
    intro hist
    by_cases h : Q.IsAbsorbing (CTMC.QMatrix.currentStateFromHistory (S := S) n hist)
    · have hdirac :
          Q.jumpHoldTrajectoryStepKernel n hist =
            MeasureTheory.Measure.dirac
              (0, CTMC.QMatrix.currentStateFromHistory (S := S) n hist) := by
        rw [Q.jumpHoldTrajectoryStepKernel_apply, Q.jumpHoldStepKernel_apply,
          Q.jumpHoldStepMeasureTotal_of_absorbing h]
      rw [hdirac]
      simp [p, h]
    · filter_upwards with r
      intro hAbs
      exact (h hAbs).elim
  have hpair : ∀ᵐ z ∂(μ.map fun records => (X records, Y records)), p z := by
    rw [show μ.map (fun records => (X records, Y records)) =
        μ.map (fun records => (Preorder.frestrictLe n records, records (n + 1))) by
          rfl]
    rw [show μ.map X = μ.map (Preorder.frestrictLe n) by rfl] at hkernel
    rw [show Q.jumpHoldTrajectoryStepKernel n = Q.jumpHoldTrajectoryStepKernel n by rfl] at hkernel
    rw [show μ = Q.canonicalRecordMeasure s₀ by rfl]
    rw [Q.canonicalRecordMeasure_history_next s₀ n]
    exact MeasureTheory.Measure.ae_compProd_of_ae_ae hp hkernel
  have hrecords : ∀ᵐ records ∂μ, p (X records, Y records) :=
    MeasureTheory.ae_of_ae_map (by fun_prop) hpair
  simpa [μ, X, Y, p] using hrecords

private theorem halfExpPP_canonical_frozenMartingalePart_eq_zero_ae_of_absorbing
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1))
    (hinit : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x₀)
    (habs :
      (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).toQMatrix.IsAbsorbing x₀) :
    let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ t : ℝ,
      M.frozenMartingalePart M.canonicalPathMap t records = 0 := by
  let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  have hDrift : M.rateSpec.drift (M.scaledState x₀) = 0 := by
    exact (halfExpPP_driftZeroAtAbsorbingOnSimplex N hN) x₀ hinit
      (by simpa [M, CTMC.QMatrix.IsAbsorbing] using habs)
  filter_upwards
    [M.toQMatrix.canonicalRecordMeasure_record_zero_eq_init_ae x₀,
      canonicalRecordMeasure_all_next_state_eq_current_ae_of_absorbing M.toQMatrix x₀]
    with records hrecord0 hstay t
  have hrecord0_state : (records 0).2 = x₀ := by
    simpa using congrArg Prod.snd hrecord0
  have hseq : ∀ n, (M.canonicalPathMap records).stateSeq n = x₀ := by
    intro n
    induction n with
    | zero =>
        simpa [M, CTMC.DensityDepCTMC.canonicalPathMap,
          CTMC.QMatrix.recordTrajectoryToPath_stateSeq] using hrecord0_state
    | succ n ih =>
        have hcur :
            CTMC.QMatrix.currentStateFromHistory
                (S := Fin 3 → Fin (N + 1)) n (Preorder.frestrictLe n records) = x₀ := by
          simpa [M, CTMC.DensityDepCTMC.canonicalPathMap,
            CTMC.QMatrix.currentStateFromHistory_frestrictLe] using ih
        have hnext := hstay n (by simpa [hcur, M] using habs)
        have hnext_state : (records (n + 1)).2 = x₀ := by
          simpa [hcur] using hnext
        simpa [M, CTMC.DensityDepCTMC.canonicalPathMap,
          CTMC.QMatrix.recordTrajectoryToPath_stateSeq] using hnext_state
  have hfrozen : ∀ s : ℝ, (M.canonicalPathMap records).frozenStateAt s = x₀ := by
    intro s
    let path := M.canonicalPathMap records
    have hseq_path : ∀ n, path.stateSeq n = x₀ := hseq
    by_cases hex : ∃ n, s < path.times n
    · let n := Nat.find hex
      have hmin : ∀ k ∈ Finset.range n, ¬ s < path.times k := by
        intro k hk
        exact Nat.find_min hex (Finset.mem_range.mp hk)
      rw [path.frozenStateAt_eq_stateSeq_of_first_time_gt s n
        (Nat.find_spec hex) hmin, hseq_path n]
    · have hno : ∀ n, ¬ s < path.times n := by
        intro n hn
        exact hex ⟨n, hn⟩
      have hstable : path.stateSeq 0 = path.stateSeq (0 + 1) := by
        rw [hseq_path 0, hseq_path 1]
      have hmin : ∀ k ∈ Finset.range 0,
          path.stateSeq k ≠ path.stateSeq (k + 1) := by
        intro k hk
        simp at hk
      rw [path.frozenStateAt_eq_stateSeq_of_first_stable s 0 hno hstable hmin,
        hseq_path 0]
  ext i
  simp only [CTMC.DensityDepCTMC.frozenMartingalePart,
    CTMC.DensityDepCTMC.frozenDensityProcess,
    CTMC.DensityDepCTMC.frozenInitialCondition, Pi.sub_apply, Pi.zero_apply]
  have hinit_frozen : (M.canonicalPathMap records).frozenStateAt 0 = x₀ := hfrozen 0
  have ht_frozen : (M.canonicalPathMap records).frozenStateAt t = x₀ := hfrozen t
  have hfun_zero :
      (fun s : ℝ =>
        (M.rateSpec.drift (M.frozenDensityProcess M.canonicalPathMap s records)) i)
        = fun _ => 0 := by
    funext s
    have hdens :
        M.frozenDensityProcess M.canonicalPathMap s records = M.scaledState x₀ := by
      ext j
      simp [CTMC.DensityDepCTMC.frozenDensityProcess,
        CTMC.DensityDepCTMC.scaledState, hfrozen s]
    rw [hdens]
    exact congr_fun hDrift i
  rw [ht_frozen, hinit_frozen, hfun_zero]
  simp [CTMC.DensityDepCTMC.frozenDensityProcess]

/-! ## Solution norm bound -/

theorem halfExpSol_norm_le_one (t : ℝ) (ht : 0 ≤ t) :
    ‖halfExpSol t‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (halfExpSol_nonneg t ht i)]
  calc halfExpSol t i
      ≤ ∑ j : Fin 3, halfExpSol t j :=
        Finset.single_le_sum (fun j _ => halfExpSol_nonneg t ht j)
          (Finset.mem_univ i)
    _ = 1 := halfExpSol_simplex_sum t

/-! ## Kurtz finite-horizon convergence (per-N)

The finite-horizon convergence for the frozen DensityProcess. This is
the per-N statement: for each T and large enough N, the sup-norm error
is small with high probability. Each N uses its own canonical measure.

The proof requires:
1. The O(T/N) QV bound for the frozen (stopped) martingale
2. The pathwise Gronwall event inclusion
3. Markov's inequality

The O(T/N) QV bound is the main formalization gap: it needs Doob's
maximal inequality for the stopped martingale, which is not yet in
the Ripple infrastructure. Mathematically, the frozen martingale equals
the standard martingale stopped at absorption time, so its QV is bounded
by the standard one, which is O(T/N) from the instantaneous QV rate. -/

private lemma setIntegral_Icc_eq_intervalIntegral_of_le
    {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    (∫ s in Set.Icc a b, f s) = ∫ s in a..b, f s := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]

private lemma halfExpSol_component_hasDerivAt
    (i : Fin 3) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => halfExpSol s i)
      ((halfExpPP.toRateSpec.drift (halfExpSol t)) i) t :=
  hasDerivAt_pi.mp (halfExpMeanFieldSolution.sol_ode t ht) i

private lemma continuous_halfExp_drift_component (i : Fin 3) :
    Continuous (fun s : ℝ =>
      (halfExpPP.toRateSpec.drift (halfExpSol s)) i) := by
  rw [halfExpPP_drift_eq]
  fin_cases i <;>
    simp [halfExpFieldPP, halfExpSol, halfExpSol_F, halfExpSol_E, halfExpSol_G] <;>
    fun_prop

private lemma intervalIntegrable_halfExp_drift_component
    (i : Fin 3) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable
      (fun s : ℝ => (halfExpPP.toRateSpec.drift (halfExpSol s)) i)
      MeasureTheory.volume (0 : ℝ) t :=
  ContinuousOn.intervalIntegrable_of_Icc ht
    (continuous_halfExp_drift_component i).continuousOn

private lemma halfExpSol_component_sub_eq_integral
    (i : Fin 3) {t : ℝ} (ht : 0 ≤ t) :
    halfExpSol t i - halfExpSol 0 i =
      ∫ s in (0 : ℝ)..t,
        (halfExpPP.toRateSpec.drift (halfExpSol s)) i := by
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => halfExpSol_component_hasDerivAt i
      ((by simpa [Set.uIcc_of_le ht] using hs : s ∈ Set.Icc 0 t).1))
    (intervalIntegrable_halfExp_drift_component i ht)).symm

set_option maxHeartbeats 800000 in
private theorem integrableOn_frozen_error_mul_lipschitz
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1))
    (hinit : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x₀)
    (L : ℝ) (hL_nn : 0 ≤ L)
    {T : ℝ} (hT : 0 < T)
    (ω : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordΩ) :
    MeasureTheory.IntegrableOn
      (fun s => L * ‖(halfExpPP_frozenDensityProcess N hN x₀ hinit).process s ω -
        halfExpSol s‖)
      (Set.uIcc (0 : ℝ) T) MeasureTheory.volume := by
  rw [Set.uIcc_of_le (le_of_lt hT)]
  have hsol_meas : Measurable halfExpSol := by
    rw [measurable_pi_iff]; intro i
    fin_cases i <;>
      simp [halfExpSol, halfExpSol_F, halfExpSol_E, halfExpSol_G] <;> fun_prop
  have hpair : Measurable (fun s : ℝ =>
      ((s, ω) : ℝ ×
        (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordΩ)) :=
    Measurable.prodMk measurable_id measurable_const
  let M : CTMC.DensityDepCTMC 3 := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  have hsol_meas : Measurable halfExpSol := by
    rw [measurable_pi_iff]; intro i
    fin_cases i <;>
      simp [halfExpSol, halfExpSol_F, halfExpSol_E, halfExpSol_G] <;> fun_prop
  have hpair : Measurable (fun s : ℝ =>
      ((s, (show M.canonicalRecordΩ from ω)) : ℝ × M.canonicalRecordΩ)) :=
    Measurable.prodMk measurable_id measurable_const
  have hX_raw : Measurable (fun s : ℝ =>
      M.frozenDensityProcess M.canonicalPathMap s
        (show M.canonicalRecordΩ from ω)) :=
    M.measurable_prod_canonicalFrozenDensityProcess.comp hpair
  have hdiff_meas : Measurable (fun s : ℝ =>
      M.frozenDensityProcess M.canonicalPathMap s
        (show M.canonicalRecordΩ from ω) - halfExpSol s) := by
    rw [measurable_pi_iff]; intro i
    exact ((measurable_pi_apply i).comp hX_raw).sub
      ((measurable_pi_apply i).comp hsol_meas)
  have hg_meas : Measurable (fun s : ℝ =>
      L * ‖M.frozenDensityProcess M.canonicalPathMap s
        (show M.canonicalRecordΩ from ω) - halfExpSol s‖) :=
    (measurable_norm.comp hdiff_meas).const_mul L
  refine MeasureTheory.IntegrableOn.of_bound measure_Icc_lt_top
    hg_meas.aestronglyMeasurable (L * 2) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hL_nn (norm_nonneg _))]
  show L * ‖M.frozenDensityProcess M.canonicalPathMap s
    (show M.canonicalRecordΩ from ω) - halfExpSol s‖ ≤ L * 2
  have h1 := M.frozenDensityProcess_norm_le M.canonicalPathMap s ω
  have h2 := halfExpSol_norm_le_one s hs.1
  have h3 := norm_sub_le
    (M.frozenDensityProcess M.canonicalPathMap s ω) (halfExpSol s)
  nlinarith

set_option maxHeartbeats 800000 in
/-- Pathwise Gronwall event inclusion for the frozen DensityProcess.
For ae ω: if sup ‖X(t) - sol(t)‖ ≥ ε, then either init error ≥ δ
or sup ‖M(t)‖² ≥ δ². Uses integral_gronwall_core with right-continuity. -/
theorem halfExpPP_frozen_event_inclusion
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1))
    (hinit : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x₀)
    {T : ℝ} (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) :
    let dp := halfExpPP_frozenDensityProcess N hN x₀ hinit
    let μ := (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordMeasure x₀
    ∃ δ > 0, ∀ᵐ ω ∂μ,
      (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
          ‖dp.process t ω - halfExpSol t‖ ≥ ε) →
        (‖dp.init ω - halfExpMeanFieldSolution.x₀‖ ≥ δ) ∨
        (δ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖dp.martingale_part s ω‖ ^ 2) := by
  dsimp only
  -- Lipschitz constant
  obtain ⟨L, hL_pos, hLip⟩ :=
    halfExpPP.toRateSpec.drift_lipschitz_on_ball 1 one_pos
  have hL_nn : 0 ≤ L := le_of_lt hL_pos
  -- Set δ
  set C_exp := Real.exp (L * T)
  have hCexp_pos : 0 < C_exp := Real.exp_pos _
  set δ := ε / (2 * C_exp)
  have hδ_pos : 0 < δ := div_pos hε (mul_pos two_pos hCexp_pos)
  refine ⟨δ, hδ_pos, ?_⟩
  set M_ctmc := CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec
  set dp := halfExpPP_frozenDensityProcess N hN x₀ hinit
  -- Right-continuity of the frozen DP (ae)
  have hrcont_ae :=
    M_ctmc.canonical_frozenDensityProcess_forall_continuousWithinAt_Ici_ae x₀
  obtain ⟨K_mart, _hK_pos, hK_bound⟩ :=
    M_ctmc.exists_frozenMartingalePart_norm_bound M_ctmc.canonicalPathMap T (le_of_lt hT)
  filter_upwards [hrcont_ae] with ω hrcont hsup
  -- Shared: IntegrableOn for the error integrand on uIcc 0 T
  -- (from boundedness + AEStronglyMeasurable)
  -- IntegrableOn: bounded (by L*2) + AEStronglyMeasurable (from joint measurability)
  -- Proof: uIcc→Icc, then IntegrableOn.of_bound with measure_Icc_lt_top.
  -- AEStronglyMeasurable from: measurable_prod_canonicalFrozenDensityProcess.comp
  --   (Measurable.prodMk measurable_id measurable_const) for fixed-ω section,
  --   then .sub hsol_meas, measurable_norm.comp, .const_mul, .aestronglyMeasurable.
  -- Needs set_option maxHeartbeats ≥ 400000 for the measurability chain.
  have hint_uIcc : MeasureTheory.IntegrableOn
      (fun s => L * ‖dp.process s ω - halfExpSol s‖)
      (Set.uIcc (0 : ℝ) T) MeasureTheory.volume :=
    integrableOn_frozen_error_mul_lipschitz N hN x₀ hinit L hL_nn hT ω
  have hint_Icc : MeasureTheory.IntegrableOn
      (fun s => L * ‖dp.process s ω - halfExpSol s‖)
      (Set.Icc (0 : ℝ) T) MeasureTheory.volume := by
    rwa [Set.uIcc_of_le (le_of_lt hT)] at hint_uIcc
  exact gronwall_event_inclusion_pathwise_rightContinuous
    halfExpMeanFieldSolution hT hL_nn
    (fun t => dp.process t ω)
    (dp.init ω)
    (fun t => dp.martingale_part t ω)
    (by -- hg_int
      intro x hx
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1).mpr
        (hint_Icc.mono_set (Set.Ioc_subset_Icc_self.trans
          (Set.Icc_subset_Icc_right (le_of_lt hx.2)))))
    (by -- hg_cont_right
      intro x hx
      exact (((hrcont x).mono Set.Ioi_subset_Ici_self).sub
        (halfExpSol_is_solution x hx.1).continuousAt.continuousWithinAt).norm.const_mul L)
    (by -- hg_sm
      intro x hx
      exact ⟨Set.Icc 0 T, Icc_mem_nhdsGT_of_mem hx,
        hint_Icc.aestronglyMeasurable⟩)
    (by -- hg_prim_cont
      have hprim := intervalIntegral.continuousOn_primitive_interval hint_uIcc
      rwa [Set.uIcc_of_le (le_of_lt hT)] at hprim)
    (by -- hM_sq_le_sup: ‖M t‖² ≤ sup M² via le_ciSup
      intro t ht
      have hinner_bdd : BddAbove (Set.range fun _ : 0 ≤ t ∧ t ≤ T =>
          ‖dp.martingale_part t ω‖ ^ 2) :=
        ⟨K_mart ^ 2, by rintro y ⟨ht, rfl⟩
                        have hb := hK_bound t ω ht.1 ht.2
                        have : ‖dp.martingale_part t ω‖ ≤ K_mart := hb
                        nlinarith [norm_nonneg (dp.martingale_part t ω)]⟩
      have houter_bdd : BddAbove (Set.range fun s : ℝ =>
          ⨆ (_ : 0 ≤ s ∧ s ≤ T), ‖dp.martingale_part s ω‖ ^ 2) :=
        ⟨K_mart ^ 2, by rintro y ⟨s, rfl⟩
                        exact Real.iSup_le (fun hs => by
                          have hb := hK_bound s ω hs.1 hs.2
                          have : ‖dp.martingale_part s ω‖ ≤ K_mart := hb
                          nlinarith [norm_nonneg (dp.martingale_part s ω)])
                          (by positivity)⟩
      exact le_trans (le_ciSup hinner_bdd ⟨ht.1, ht.2⟩)
        (le_ciSup houter_bdd t))
    hε
    (by -- h_integral_ineq: extracted as standalone proof to avoid let-binding conflicts
      -- The Gronwall type has `let C := exp(L*T); let δ := ε/(2*C)`.
      -- We use `show` to match the outer `set δ` with the inner `let δ`.
      show (∀ t₁ ∈ Set.Icc (0 : ℝ) T, ‖dp.martingale_part t₁ ω‖ ≤ δ) →
        ∀ t₁ ∈ Set.Icc (0 : ℝ) T,
          ‖dp.process t₁ ω - halfExpSol t₁‖ ≤
            (‖dp.init ω - halfExpMeanFieldSolution.x₀‖ + δ) +
              ∫ s in (0 : ℝ)..t₁, L * ‖dp.process s ω - halfExpSol s‖
      intro hM_bound t₁ ht₁
      apply (pi_norm_le_iff_of_nonneg (add_nonneg (add_nonneg (norm_nonneg _)
        (le_of_lt hδ_pos)) (intervalIntegral.integral_nonneg ht₁.1
          fun s _hs => mul_nonneg hL_nn (norm_nonneg _)))).mpr
      intro i
      have hmpart_def : dp.martingale_part t₁ ω i =
          dp.process t₁ ω i - dp.init ω i -
          (∫ s in Set.Icc (0 : ℝ) t₁,
            (halfExpPP.toRateSpec.drift (dp.process s ω)) i) := rfl
      have hode_sub := halfExpSol_component_sub_eq_integral i ht₁.1
      have hinit_eq := congr_fun halfExpMeanFieldSolution.sol_init i
      have hconv := setIntegral_Icc_eq_intervalIntegral_of_le ht₁.1
        (fun s => (halfExpPP.toRateSpec.drift (dp.process s ω)) i)
      have herr : (dp.process t₁ ω - halfExpSol t₁) i =
          (dp.init ω i - halfExpMeanFieldSolution.x₀ i) +
          ((∫ s in (0 : ℝ)..t₁, (halfExpPP.toRateSpec.drift (dp.process s ω)) i) -
           (∫ s in (0 : ℝ)..t₁, (halfExpPP.toRateSpec.drift (halfExpSol s)) i)) +
          dp.martingale_part t₁ ω i := by
        simp only [Pi.sub_apply]
        have hmpart_interval : dp.martingale_part t₁ ω i =
            dp.process t₁ ω i - dp.init ω i -
            (∫ s in (0 : ℝ)..t₁,
              (halfExpPP.toRateSpec.drift (dp.process s ω)) i) := by
          rw [hmpart_def, hconv]
        have hinit_eq' : halfExpSol 0 i = halfExpMeanFieldSolution.x₀ i := by
          simpa [halfExpMeanFieldSolution] using hinit_eq
        have hode_sub' : halfExpSol t₁ i - halfExpMeanFieldSolution.x₀ i =
            ∫ s in (0 : ℝ)..t₁,
              (halfExpPP.toRateSpec.drift (halfExpSol s)) i := by
          linarith
        linarith
      rw [Real.norm_eq_abs, herr]
      have htri1 := abs_add_le
        ((dp.init ω i - halfExpMeanFieldSolution.x₀ i) +
          ((∫ s in (0 : ℝ)..t₁, (halfExpPP.toRateSpec.drift (dp.process s ω)) i) -
           (∫ s in (0 : ℝ)..t₁, (halfExpPP.toRateSpec.drift (halfExpSol s)) i)))
        (dp.martingale_part t₁ ω i)
      have htri2 := abs_add_le
        (dp.init ω i - halfExpMeanFieldSolution.x₀ i)
        ((∫ s in (0 : ℝ)..t₁, (halfExpPP.toRateSpec.drift (dp.process s ω)) i) -
         (∫ s in (0 : ℝ)..t₁, (halfExpPP.toRateSpec.drift (halfExpSol s)) i))
      have h_init_bound : |dp.init ω i - halfExpMeanFieldSolution.x₀ i| ≤
          ‖dp.init ω - halfExpMeanFieldSolution.x₀‖ := by
        rw [← Pi.sub_apply, ← Real.norm_eq_abs]; exact norm_le_pi_norm _ i
      have h_mart_bound : |dp.martingale_part t₁ ω i| ≤ δ := by
        calc |dp.martingale_part t₁ ω i|
            = ‖dp.martingale_part t₁ ω i‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖dp.martingale_part t₁ ω‖ := norm_le_pi_norm _ i
          _ ≤ δ := hM_bound t₁ ht₁
      have hint_X_i : IntervalIntegrable
          (fun s => (halfExpPP.toRateSpec.drift (dp.process s ω)) i)
          MeasureTheory.volume (0 : ℝ) t₁ := by
        have hmeas : Measurable (fun s : ℝ =>
            (halfExpPP.toRateSpec.drift (dp.process s ω)) i) := by
          simpa [M_ctmc, dp, halfExpPP_frozenDensityProcess] using
            M_ctmc.measurable_canonicalFrozenDrift_component_section ω i
        obtain ⟨C, _hC, hbound⟩ :=
          halfExpPP.toRateSpec.exists_drift_bound_on_ball 1 zero_lt_one
        have hIcc : MeasureTheory.IntegrableOn
            (fun s => (halfExpPP.toRateSpec.drift (dp.process s ω)) i)
            (Set.Icc (0 : ℝ) t₁) MeasureTheory.volume := by
          refine MeasureTheory.IntegrableOn.of_bound measure_Icc_lt_top
            hmeas.aestronglyMeasurable C ?_
          filter_upwards with s
          exact (norm_le_pi_norm
            (halfExpPP.toRateSpec.drift (dp.process s ω)) i).trans
              (hbound (dp.process s ω) (dp.process_norm_le_one s ω))
        exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht₁.1).mpr
          (hIcc.mono_set Set.Ioc_subset_Icc_self)
      have hint_sol_i := intervalIntegrable_halfExp_drift_component i ht₁.1
      have h_drift_bound :
          |(∫ s in (0 : ℝ)..t₁, (halfExpPP.toRateSpec.drift (dp.process s ω)) i) -
           (∫ s in (0 : ℝ)..t₁, (halfExpPP.toRateSpec.drift (halfExpSol s)) i)| ≤
          ∫ s in (0 : ℝ)..t₁, L * ‖dp.process s ω - halfExpSol s‖ := by
        have hdiff_int : IntervalIntegrable
            (fun s =>
              (halfExpPP.toRateSpec.drift (dp.process s ω)) i -
                (halfExpPP.toRateSpec.drift (halfExpSol s)) i)
            MeasureTheory.volume (0 : ℝ) t₁ :=
          hint_X_i.sub hint_sol_i
        have h_abs_int : IntervalIntegrable
            (fun s =>
              |(halfExpPP.toRateSpec.drift (dp.process s ω)) i -
                (halfExpPP.toRateSpec.drift (halfExpSol s)) i|)
            MeasureTheory.volume (0 : ℝ) t₁ :=
          hdiff_int.abs
        have hint_rhs : IntervalIntegrable
            (fun s => L * ‖dp.process s ω - halfExpSol s‖)
            MeasureTheory.volume (0 : ℝ) t₁ := by
          exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht₁.1).mpr
            (hint_Icc.mono_set (Set.Ioc_subset_Icc_self.trans
              (Set.Icc_subset_Icc_right ht₁.2)))
        calc
          |(∫ s in (0 : ℝ)..t₁,
              (halfExpPP.toRateSpec.drift (dp.process s ω)) i) -
            (∫ s in (0 : ℝ)..t₁,
              (halfExpPP.toRateSpec.drift (halfExpSol s)) i)|
              = |∫ s in (0 : ℝ)..t₁,
                  ((halfExpPP.toRateSpec.drift (dp.process s ω)) i -
                    (halfExpPP.toRateSpec.drift (halfExpSol s)) i)| := by
                rw [intervalIntegral.integral_sub hint_X_i hint_sol_i]
          _ ≤ ∫ s in (0 : ℝ)..t₁,
                |(halfExpPP.toRateSpec.drift (dp.process s ω)) i -
                  (halfExpPP.toRateSpec.drift (halfExpSol s)) i| :=
              intervalIntegral.abs_integral_le_integral_abs ht₁.1
          _ ≤ ∫ s in (0 : ℝ)..t₁, L * ‖dp.process s ω - halfExpSol s‖ := by
              apply intervalIntegral.integral_mono_on ht₁.1 h_abs_int hint_rhs
              intro s hs
              have hcoord :
                  |(halfExpPP.toRateSpec.drift (dp.process s ω)) i -
                    (halfExpPP.toRateSpec.drift (halfExpSol s)) i| ≤
                    ‖halfExpPP.toRateSpec.drift (dp.process s ω) -
                      halfExpPP.toRateSpec.drift (halfExpSol s)‖ := by
                rw [← Real.norm_eq_abs]
                convert norm_le_pi_norm
                  (halfExpPP.toRateSpec.drift (dp.process s ω) -
                    halfExpPP.toRateSpec.drift (halfExpSol s)) i using 1
              exact hcoord.trans
                (hLip (dp.process s ω) (halfExpSol s)
                  (dp.process_norm_le_one s ω)
                  (halfExpSol_norm_le_one s hs.1))
      linarith [htri1, htri2, h_init_bound, h_mart_bound, h_drift_bound])
    hsup

theorem halfExpPP_kurtz_finite_horizon
    {T : ℝ} (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (hN : 0 < N)
    (x₀ : Fin 3 → Fin (N + 1))
    (hinit : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x₀)
    (_hinit_close :
      ‖(fun i => (↑(x₀ i) : ℝ) / ↑N) -
        halfExpMeanFieldSolution.x₀‖ ≤ 1 / ↑N),
    (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordMeasure x₀
      {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        ‖(halfExpPP_frozenDensityProcess N hN x₀ hinit).process t ω -
          halfExpSol t‖ > ε} ≤ ENNReal.ofReal η := by
  have hSolMeas : Measurable halfExpMeanFieldSolution.sol := by
    change Measurable halfExpSol
    rw [measurable_pi_iff]
    intro i
    fin_cases i <;>
      simp [halfExpSol, halfExpSol_F, halfExpSol_E, halfExpSol_G] <;> fun_prop
  have hDoob : Kurtz.FrozenDoobL2 halfExpPP.toRateSpec 16 := by
    intro N hN x₀ hinit T hT
    exact halfExpPPFrozenDoobL2_holds N hN x₀ hinit T hT
  simpa [halfExpPP_frozenDensityProcess, halfExpMeanFieldSolution] using
    (Kurtz.kurtz_finite_horizon_generic
      (Γ := halfExpPP.toRateSpec)
      (mf := halfExpMeanFieldSolution)
      (hDriftZero := halfExpPP_driftZeroAtAbsorbingOnSimplex)
      (hConservative := halfExpPP_conservativeJumps)
      (hSolBound := halfExpSol_norm_le_one)
      (hSolMeas := hSolMeas)
      (hSolDriftInt := by
        intro i t ht
        exact intervalIntegrable_halfExp_drift_component i ht)
      (A_doob := 16)
      (hA_doob_pos := by norm_num)
      (hDoob := hDoob)
      (hQVRate := halfExpPP_exists_instantQVRate_bound_uniform)
      hT ε hε η hη)


/-! ## Stochastic convergence to ½e⁻¹

The final theorem: for balanced initial conditions, the F-density of the
½e⁻¹ population protocol converges to ½e⁻¹ in the exchanged order
(first N → ∞, then T → ∞). Each N uses its own canonical probability space.

The proof chains ODE convergence (halfExpSol_F_tendsto) with finite-horizon
Kurtz convergence (halfExpPP_kurtz_finite_horizon) via the triangle inequality.
The stochastic maximal inequality is supplied by `halfExpPPFrozenDoobL2_holds`. -/

/-- **Stochastic convergence to ½e⁻¹.**

For any accuracy ε > 0 and confidence η > 0, there exists a time horizon T₀
such that for all T ≥ T₀, there exists a population size threshold N₀
such that for all N ≥ N₀ with initial conditions close to (½, ½, 0):

  P(|X̄^N_F(T) - ½e⁻¹| > ε) ≤ η

This is the main result: the stochastic population protocol converges
to ½e⁻¹ in probability, in the exchanged order lim_T lim_N. -/
theorem halfExpPP_stochastic_convergence
    (ε : ℝ) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∃ T₀ > 0, ∀ T ≥ T₀, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (hN : 0 < N) (x₀ : Fin 3 → Fin (N + 1))
      (hinit : (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).InSimplex x₀)
      (_hinit_close :
        ‖(fun i => (↑(x₀ i) : ℝ) / ↑N) -
          halfExpMeanFieldSolution.x₀‖ ≤ 1 / ↑N),
    (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordMeasure x₀
      {ω | |(halfExpPP_frozenDensityProcess N hN x₀ hinit).process T ω 0 -
        Real.exp (-1) / 2| > ε} ≤ ENNReal.ofReal η := by
  -- Step 1: ODE convergence — choose T₀ so |F(T) - ½e⁻¹| < ε/2
  set ρ := ε / 2 with hρ_def
  have hρ : 0 < ρ := by positivity
  have htend := halfExpSol_F_tendsto
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨Traw, hTraw⟩ := htend ρ hρ
  set T₀ := max Traw 1 with hT₀_def
  have hT₀_pos : 0 < T₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨T₀, hT₀_pos, ?_⟩
  intro T hT
  have hT_pos : 0 < T := lt_of_lt_of_le hT₀_pos hT
  have hTraw_le : Traw ≤ T := le_trans (le_max_left _ _) hT
  have hode : |halfExpSol_F T - Real.exp (-1) / 2| < ρ := by
    simpa [Real.dist_eq] using hTraw T hTraw_le
  -- Step 2: Kurtz finite-horizon convergence for ρ = ε/2
  obtain ⟨N₀, hN₀⟩ :=
    halfExpPP_kurtz_finite_horizon hT_pos ρ hρ η hη
  refine ⟨N₀, fun N hN_ge hN x₀ hinit hinit_close => ?_⟩
  -- Step 3: Triangle inequality + point ≤ sup
  -- {|process_F(T) - ½e⁻¹| > ε} ⊆ {sup ‖process - sol‖ > ε/2}
  -- because |sol_F(T) - ½e⁻¹| < ε/2 (from ODE convergence)
  set dp := halfExpPP_frozenDensityProcess N hN x₀ hinit
  set μ := (CTMC.DensityDepCTMC.mk N hN halfExpPP.toRateSpec).canonicalRecordMeasure x₀
  -- Triangle inequality + point ≤ sup:
  -- {|F(T) - ½e⁻¹| > ε} ⊆ {sup ‖X - sol‖ > ρ}
  -- because |sol_F(T) - ½e⁻¹| < ρ (ODE convergence) and
  -- ‖X(T) - sol(T)‖ ≤ sup_{t∈[0,T]} ‖X(t) - sol(t)‖
  have h_incl : {ω | |dp.process T ω 0 - Real.exp (-1) / 2| > ε} ⊆
      {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
            ‖dp.process t ω - halfExpSol t‖ > ρ} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hcoord : |dp.process T ω 0 - halfExpSol T 0| ≤
        ‖dp.process T ω - halfExpSol T‖ := by
      have : dp.process T ω 0 - halfExpSol T 0 =
        (dp.process T ω - halfExpSol T) 0 := by simp [Pi.sub_apply]
      rw [this, ← Real.norm_eq_abs]
      exact norm_le_pi_norm _ 0
    have hpoint : ‖dp.process T ω - halfExpSol T‖ > ρ := by
      by_contra h_le
      push_neg at h_le
      have hsol_eq : halfExpSol T 0 = halfExpSol_F T := rfl
      have hab : |dp.process T ω 0 - Real.exp (-1) / 2| ≤ ρ + ρ := by
        calc |dp.process T ω 0 - Real.exp (-1) / 2|
            = |(dp.process T ω 0 - halfExpSol T 0) +
                (halfExpSol T 0 - Real.exp (-1) / 2)| := by ring_nf
          _ ≤ |dp.process T ω 0 - halfExpSol T 0| +
                |halfExpSol T 0 - Real.exp (-1) / 2| := abs_add_le _ _
          _ ≤ ρ + ρ := by
            gcongr
            · exact hcoord.trans h_le
            · rw [hsol_eq]; exact le_of_lt hode
      linarith [show ρ + ρ = ε from by dsimp [ρ]; ring]
    set f := fun s => ‖dp.process s ω - halfExpSol s‖ with hf_def
    have hf_le_2 : ∀ s : ℝ, 0 ≤ s → f s ≤ 2 := by
      intro s hs
      calc f s ≤ ‖dp.process s ω‖ + ‖halfExpSol s‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by
          gcongr
          · exact dp.process_norm_le_one s ω
          · exact halfExpSol_norm_le_one s hs
        _ = 2 := by norm_num
    have hinner_bdd : ∀ s : ℝ,
        BddAbove (Set.range fun _ : 0 ≤ s ∧ s ≤ T => f s) := by
      intro s
      exact ⟨2, by rintro y ⟨hs, rfl⟩; exact hf_le_2 s hs.1⟩
    have houter_bdd : BddAbove (Set.range fun s : ℝ =>
        ⨆ (_ : 0 ≤ s ∧ s ≤ T), f s) := by
      refine ⟨2, ?_⟩
      rintro y ⟨s, rfl⟩
      exact Real.iSup_le
        (fun hs => hf_le_2 s hs.1)
        (by norm_num)
    calc ρ < f T := hpoint
      _ ≤ ⨆ (_ : 0 ≤ T ∧ T ≤ T), f T :=
        le_ciSup (hinner_bdd T) ⟨le_of_lt hT_pos, le_rfl⟩
      _ ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T), f s :=
        le_ciSup houter_bdd T
  calc μ {ω | |dp.process T ω 0 - Real.exp (-1) / 2| > ε}
      ≤ μ {ω | ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
            ‖dp.process t ω - halfExpSol t‖ > ρ} :=
        MeasureTheory.measure_mono h_incl
    _ ≤ ENNReal.ofReal η := hN₀ N hN_ge hN x₀ hinit hinit_close

end Ripple
