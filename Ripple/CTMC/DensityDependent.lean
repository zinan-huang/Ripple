import Ripple.CTMC.CTMC
import Ripple.CTMC.CTMCProcess
import Ripple.CTMC.CanonicalLaw
import Ripple.Kurtz.Defs
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Probability.CondVar
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

namespace Ripple.CTMC

open MeasureTheory MeasureTheory.Measure Topology

/-- Layer-cake/Doob integration step: a tail inequality
`ε μ {ε ≤ X} ≤ ∫_{ε≤X} Y` upgrades to the L2 estimate
`∫ X^2 ≤ 2 ∫ X Y`.  This is the measure-theoretic core used below to turn
Doob's maximal inequality into a finite-time L2 maximal bound. -/
theorem integral_sq_le_two_integral_mul_of_maximal_ineq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {X Y : α → ℝ}
    (hX_meas : Measurable X) (hY_meas : Measurable Y)
    (hX_nonneg : 0 ≤ᵐ[μ] X) (hY_nonneg : 0 ≤ᵐ[μ] Y)
    (hXsq_int : Integrable (fun a => X a ^ 2) μ)
    (hY_int : Integrable Y μ)
    (hXY_int : Integrable (fun a => X a * Y a) μ)
    (hMax : ∀ ε : NNReal,
      ((ε : ENNReal) * μ {a | (ε : ℝ) ≤ X a}) ≤
        ENNReal.ofReal (∫ a in {a | (ε : ℝ) ≤ X a}, Y a ∂μ)) :
    ∫ a, X a ^ 2 ∂μ ≤ 2 * ∫ a, X a * Y a ∂μ := by
  let ν : Measure α := μ.withDensity fun a => ENNReal.ofReal (Y a)
  have hν_ac : ν ≪ μ := by
    dsimp [ν]
    exact withDensity_absolutelyContinuous μ _
  have hX_nonneg_ν : 0 ≤ᵐ[ν] X := hν_ac.ae_le hX_nonneg
  have htail_ae :
      (fun t : ℝ => μ {a | t ≤ X a} * ENNReal.ofReal t)
        ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun t : ℝ => ν {a | t ≤ X a}) := by
    filter_upwards
      [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))]
      with t ht
    have ht_nonneg : 0 ≤ t := le_of_lt ht
    let ε : NNReal := ⟨t, ht_nonneg⟩
    have hset : MeasurableSet {a : α | t ≤ X a} :=
      measurableSet_le measurable_const hX_meas
    have hright :
        ENNReal.ofReal (∫ a in {a : α | t ≤ X a}, Y a ∂μ) =
          ν {a : α | t ≤ X a} := by
      dsimp [ν]
      rw [withDensity_apply _ hset]
      rw [← ofReal_integral_eq_lintegral_ofReal
        (μ := μ.restrict {a : α | t ≤ X a}) hY_int.restrict
        (ae_restrict_of_ae hY_nonneg)]
    have hmax := hMax ε
    dsimp [ε] at hmax
    have heps : ((ε : NNReal) : ENNReal) = ENNReal.ofReal t := by
      simp [ε, ENNReal.ofReal_eq_coe_nnreal, ht_nonneg]
    calc
      μ {a : α | t ≤ X a} * ENNReal.ofReal t
          = ENNReal.ofReal t * μ {a : α | t ≤ X a} := by rw [mul_comm]
      _ = ((ε : NNReal) : ENNReal) * μ {a : α | t ≤ X a} := by rw [heps]
      _ ≤ ENNReal.ofReal (∫ a in {a : α | t ≤ X a}, Y a ∂μ) := hmax
      _ = ν {a : α | t ≤ X a} := hright
  have htail_int :
      ∫⁻ t in Set.Ioi (0 : ℝ), μ {a | t ≤ X a} * ENNReal.ofReal t ≤
        ∫⁻ t in Set.Ioi (0 : ℝ), ν {a | t ≤ X a} := by
    exact lintegral_mono_ae htail_ae
  have hX_layer :=
    lintegral_rpow_eq_lintegral_meas_le_mul (μ := μ) (p := (2 : ℝ))
      hX_nonneg hX_meas.aemeasurable (by norm_num)
  have hν_layer :=
    lintegral_eq_lintegral_meas_le (μ := ν) hX_nonneg_ν hX_meas.aemeasurable
  have hlhs :
      ENNReal.ofReal (∫ a, X a ^ 2 ∂μ) =
        ∫⁻ a, ENNReal.ofReal (X a ^ 2) ∂μ := by
    exact ofReal_integral_eq_lintegral_ofReal hXsq_int
      (ae_of_all μ fun a => sq_nonneg (X a))
  have hrhs :
      ENNReal.ofReal (∫ a, X a * Y a ∂μ) =
        ∫⁻ a, ENNReal.ofReal (X a * Y a) ∂μ := by
    exact ofReal_integral_eq_lintegral_ofReal hXY_int
      (hX_nonneg.and hY_nonneg |>.mono fun _ h => mul_nonneg h.1 h.2)
  have hweighted :
      ∫⁻ a, ENNReal.ofReal (X a) ∂ν =
        ∫⁻ a, ENNReal.ofReal (X a * Y a) ∂μ := by
    rw [lintegral_withDensity_eq_lintegral_mul μ hY_meas.ennreal_ofReal
      hX_meas.ennreal_ofReal]
    apply lintegral_congr_ae
    filter_upwards [hX_nonneg, hY_nonneg] with a hXa hYa
    change ENNReal.ofReal (Y a) * ENNReal.ofReal (X a) =
      ENNReal.ofReal (X a * Y a)
    rw [show X a * Y a = Y a * X a by ring, ENNReal.ofReal_mul hYa]
  have h_ENN :
      ENNReal.ofReal (∫ a, X a ^ 2 ∂μ) ≤
        ENNReal.ofReal (2 * ∫ a, X a * Y a ∂μ) := by
    calc
      ENNReal.ofReal (∫ a, X a ^ 2 ∂μ)
          = ∫⁻ a, ENNReal.ofReal (X a ^ 2) ∂μ := hlhs
      _ = ∫⁻ a, ENNReal.ofReal (X a ^ (2 : ℝ)) ∂μ := by
            apply lintegral_congr_ae
            filter_upwards with a
            rw [Real.rpow_two]
      _ = ENNReal.ofReal (2 : ℝ) *
            ∫⁻ t in Set.Ioi (0 : ℝ),
              μ {a : α | t ≤ X a} * ENNReal.ofReal (t ^ ((2 : ℝ) - 1)) := hX_layer
      _ = ENNReal.ofReal (2 : ℝ) *
            ∫⁻ t in Set.Ioi (0 : ℝ),
              μ {a : α | t ≤ X a} * ENNReal.ofReal t := by
            congr 1
            apply lintegral_congr_ae
            filter_upwards with t
            rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
      _ ≤ ENNReal.ofReal (2 : ℝ) *
            ∫⁻ t in Set.Ioi (0 : ℝ), ν {a : α | t ≤ X a} := by
            exact mul_le_mul_right htail_int _
      _ = ENNReal.ofReal (2 : ℝ) * ∫⁻ a, ENNReal.ofReal (X a) ∂ν := by
            rw [hν_layer]
      _ = ENNReal.ofReal (2 : ℝ) * ∫⁻ a, ENNReal.ofReal (X a * Y a) ∂μ := by
            rw [hweighted]
      _ = ENNReal.ofReal (2 * ∫ a, X a * Y a ∂μ) := by
            rw [← hrhs]
            rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hB_nonneg : 0 ≤ ∫ a, X a * Y a ∂μ :=
    integral_nonneg_of_ae
      (hX_nonneg.and hY_nonneg |>.mono fun _ h => mul_nonneg h.1 h.2)
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hB_nonneg)).1 h_ENN

/-- A density-dependent CTMC is a CTMC on the lattice (1/N)·ℤ^d where
the transition rates depend on the current density x = state/N. -/
structure DensityDepCTMC (d : ℕ) where
  /-- Population size -/
  N : ℕ
  hN : 0 < N
  /-- The rate specification (from Ripple.Kurtz.Defs) -/
  rateSpec : Ripple.Kurtz.RateSpec d

namespace DensityDepCTMC

variable {d : ℕ} (M : DensityDepCTMC d)

/-- Off-diagonal rates for the Q-matrix. -/
noncomputable def offDiagRate (x y : Fin d → Fin (M.N + 1)) : ℝ :=
  if x = y then 0
  else ∑ ℓ ∈ M.rateSpec.jumps.filter (fun ℓ => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i),
         (M.N : ℝ) * M.rateSpec.rate ℓ (fun i => (x i : ℝ) / (M.N : ℝ))

/-- Density-dependent off-diagonal rates are non-negative, including the
diagonal convention where they are defined to be zero. -/
theorem offDiagRate_nonneg (x y : Fin d → Fin (M.N + 1)) :
    0 ≤ M.offDiagRate x y := by
  by_cases hxy : x = y
  · simp [offDiagRate, hxy]
  · simp only [offDiagRate, if_neg hxy]
    apply Finset.sum_nonneg
    intro ℓ hℓ
    apply mul_nonneg (Nat.cast_nonneg _)
    apply M.rateSpec.rate_nonneg ℓ (Finset.mem_filter.mp hℓ).1
    intro i
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The rate matrix for the Q-matrix. -/
noncomputable def qMatrixRate (x y : Fin d → Fin (M.N + 1)) : ℝ :=
  if x = y then
    - ∑ z ∈ Finset.univ.filter (· ≠ x), M.offDiagRate x z
  else
    M.offDiagRate x y

/-- The Q-matrix on Fin(N+1)^d. -/
noncomputable def toQMatrix : QMatrix (Fin d → Fin (M.N + 1)) where
  rate := M.qMatrixRate
  rate_nonneg := by
    intro x y hne
    simp only [qMatrixRate, if_neg hne, offDiagRate]
    apply Finset.sum_nonneg
    intro ℓ hℓ
    apply mul_nonneg (Nat.cast_nonneg _)
    apply M.rateSpec.rate_nonneg ℓ (Finset.mem_filter.mp hℓ).1
    intro i
    apply div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rate_diag := by
    intro x
    have lhs : M.qMatrixRate x x =
        -∑ z ∈ Finset.univ.filter (· ≠ x), M.offDiagRate x z := by
      simp [qMatrixRate]
    have rhs : ∀ z ∈ Finset.univ.filter (· ≠ x),
        M.qMatrixRate x z = M.offDiagRate x z := by
      intro z hz
      have : ¬(x = z) := Ne.symm (Finset.mem_filter.mp hz).2
      simp [qMatrixRate, this]
    rw [lhs, Finset.sum_congr rfl rhs]

/-- Exit rate of the density-dependent Q-matrix at state x.
Equal to ∑_{y≠x} offDiagRate(x,y). -/
noncomputable def exitRateAt (x : Fin d → Fin (M.N + 1)) : ℝ :=
  M.toQMatrix.exitRate x

/-- Exit rate is non-negative. -/
theorem exitRateAt_nonneg (x : Fin d → Fin (M.N + 1)) :
    0 ≤ M.exitRateAt x :=
  M.toQMatrix.exitRate_nonneg x

/-! ## Embedded jump-chain support -/

/-- The density-dependent Q-matrix has no absorbing states.  This is not
automatic for arbitrary rate specifications; boundary or terminal population
states may be absorbing. -/
def NoAbsorbing : Prop :=
  ∀ x : Fin d → Fin (M.N + 1), ¬M.toQMatrix.IsAbsorbing x

/-- Under `NoAbsorbing`, every density-dependent state has strictly positive
exit rate. -/
theorem exitRateAt_pos_of_noAbsorbing
    (hNA : M.NoAbsorbing) (x : Fin d → Fin (M.N + 1)) :
    0 < M.exitRateAt x :=
  M.toQMatrix.exitRate_pos_of_nonabsorbing (hNA x)

/-- A positive density-dependent off-diagonal rate rules out absorption at the
source state. -/
theorem not_absorbing_of_offDiagRate_pos
    {x y : Fin d → Fin (M.N + 1)} (hxy : x ≠ y)
    (hrate : 0 < M.offDiagRate x y) :
    ¬M.toQMatrix.IsAbsorbing x := by
  have hq : 0 < M.toQMatrix.rate x y := by
    simpa only [toQMatrix, qMatrixRate, if_neg hxy] using hrate
  exact M.toQMatrix.not_absorbing_of_rate_pos hxy hq

/-- If every population state has at least one positive outgoing
density-dependent off-diagonal rate, then the induced Q-matrix has no absorbing
states. -/
theorem noAbsorbing_of_forall_exists_offDiagRate_pos
    (h : ∀ x : Fin d → Fin (M.N + 1),
      ∃ y : Fin d → Fin (M.N + 1), x ≠ y ∧ 0 < M.offDiagRate x y) :
    M.NoAbsorbing := by
  intro x
  obtain ⟨y, hxy, hrate⟩ := h x
  exact M.not_absorbing_of_offDiagRate_pos hxy hrate

/-- A positive entry of the induced Q-matrix is necessarily a positive
off-diagonal density-dependent transition rate. -/
theorem offDiagRate_pos_of_toQMatrix_rate_pos
    {x y : Fin d → Fin (M.N + 1)} (h : 0 < M.toQMatrix.rate x y) :
    0 < M.offDiagRate x y := by
  by_cases hxy : x = y
  · subst y
    have hnonpos : M.toQMatrix.rate x x ≤ 0 := by
      rw [M.toQMatrix.diag_eq_neg_exitRate]
      exact neg_nonpos.mpr (M.toQMatrix.exitRate_nonneg x)
    exact (not_lt_of_ge hnonpos h).elim
  · simpa only [toQMatrix, qMatrixRate, if_neg hxy] using h

/-- Under the explicit no-absorbing-state condition, the canonical record law
for the density-dependent Q-matrix reads out to compatible CTMC paths almost
surely. -/
theorem canonicalRecordMeasure_recordTrajectoryToPath_isCompatible_ae_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (h : M.NoAbsorbing) :
    ∀ᵐ records ∂M.toQMatrix.canonicalRecordMeasure x₀,
      (QMatrix.recordTrajectoryToPath records).IsCompatible M.toQMatrix :=
  M.toQMatrix.canonicalRecordMeasure_recordTrajectoryToPath_isCompatible_ae_of_no_absorbing x₀ h

/-! ## Canonical record probability space -/

/-- Canonical record sample space for the density-dependent CTMC. -/
abbrev canonicalRecordΩ : Type :=
  (n : ℕ) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) n

/-- Natural filtration on density-dependent canonical record trajectories. -/
def canonicalRecordFiltration :
    MeasureTheory.Filtration ℕ
      (inferInstance : MeasurableSpace M.canonicalRecordΩ) :=
  QMatrix.canonicalRecordFiltration
    (S := Fin d → Fin (M.N + 1))

/-- Shifted canonical record filtration for clock-horizon stopping times. -/
def shiftedCanonicalRecordFiltration :
    MeasureTheory.Filtration ℕ
      (inferInstance : MeasurableSpace M.canonicalRecordΩ) :=
  QMatrix.shiftedCanonicalRecordFiltration
    (S := Fin d → Fin (M.N + 1))

/-- Canonical record law for the density-dependent CTMC started from `x₀`. -/
noncomputable def canonicalRecordMeasure
    (x₀ : Fin d → Fin (M.N + 1)) : Measure M.canonicalRecordΩ :=
  M.toQMatrix.canonicalRecordMeasure x₀

/-- The canonical record law is a probability measure. -/
instance instIsProbabilityMeasureCanonicalRecordMeasure
    (x₀ : Fin d → Fin (M.N + 1)) :
    IsProbabilityMeasure (M.canonicalRecordMeasure x₀) := by
  unfold canonicalRecordMeasure
  infer_instance

/-- Canonical path readout from the density-dependent record trajectory. -/
noncomputable def canonicalPathMap :
    M.canonicalRecordΩ → CTMCPath (Fin d → Fin (M.N + 1)) :=
  QMatrix.recordTrajectoryToPath

/-- The canonical read-out state sequence is adapted to the density-dependent
canonical record filtration. -/
theorem measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration
    (n : ℕ) :
    Measurable[M.canonicalRecordFiltration n]
      (fun records : M.canonicalRecordΩ =>
        (M.canonicalPathMap records).stateSeq n) := by
  simpa [canonicalRecordFiltration, canonicalPathMap] using
    (QMatrix.measurable_recordTrajectoryToPath_stateSeq_canonicalRecordFiltration
      (S := Fin d → Fin (M.N + 1)) n)

/-- Earlier canonical read-out states remain measurable with respect to later
density-dependent canonical histories. -/
theorem measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration_le
    {k n : ℕ} (hkn : k ≤ n) :
    Measurable[M.canonicalRecordFiltration n]
      (fun records : M.canonicalRecordΩ =>
        (M.canonicalPathMap records).stateSeq k) := by
  simpa [canonicalRecordFiltration, canonicalPathMap] using
    (QMatrix.measurable_recordTrajectoryToPath_stateSeq_canonicalRecordFiltration_le
      (S := Fin d → Fin (M.N + 1)) hkn)

/-- The canonical read-out state sequence is adapted to the canonical record
filtration. -/
theorem adapted_canonicalPathMap_stateSeq_canonicalRecordFiltration :
    MeasureTheory.Adapted M.canonicalRecordFiltration
      (fun n records => (M.canonicalPathMap records).stateSeq n) :=
  fun n => M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration n

/-- Under the explicit no-absorbing-state condition, the density-dependent
canonical path readout is compatible with its Q-matrix almost surely. -/
theorem canonicalPathMap_isCompatible_ae_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (h : M.NoAbsorbing) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      (M.canonicalPathMap records).IsCompatible M.toQMatrix := by
  simpa [canonicalRecordMeasure, canonicalPathMap] using
    M.canonicalRecordMeasure_recordTrajectoryToPath_isCompatible_ae_of_noAbsorbing x₀ h

/-- Under `NoAbsorbing`, the next holding-time conditional law has the
uniform exponential tail lower bound at every finite history level. -/
theorem condDistrib_canonicalRecordMeasure_next_holdingTime_Ioi_ge_uniformRate_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
      Real.exp (-(M.toQMatrix.uniformRate * δ)) ≤
        (ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist).real
          (Set.Ioi δ) := by
  unfold canonicalRecordMeasure
  filter_upwards
    [M.toQMatrix.condDistrib_next_holdingTime_Ioi_ge_uniformRate_of_nonabsorbing
      x₀ n hδ]
    with hist hhist
  exact hhist (hNA (QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n hist))

/-- Under `NoAbsorbing`, the conditional expectation of the next raw
holding-time tail indicator is bounded below by the uniform exponential tail. -/
theorem condExp_next_holdingTime_Ioi_ge_uniformRate_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      Real.exp (-(M.toQMatrix.uniformRate * δ)) ≤
        MeasureTheory.condExp
          (MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance)
          (M.canonicalRecordMeasure x₀)
          (((fun records : M.canonicalRecordΩ => (records (n + 1)).1) ⁻¹'
            Set.Ioi δ).indicator fun _ => (1 : ℝ))
          records := by
  unfold canonicalRecordMeasure
  exact M.toQMatrix.condExp_next_holdingTime_Ioi_ge_uniformRate_of_no_absorbing
    x₀ hNA n hδ

/-- Under `NoAbsorbing`, the conditional expectation of the next raw holding
time is the reciprocal of the current density-dependent exit rate. -/
theorem condExp_next_holdingTime_eq_inv_exitRate_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) (n : ℕ) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      MeasureTheory.condExp
          (MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance)
          (M.canonicalRecordMeasure x₀)
          (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
          records =
        (M.exitRateAt ((M.canonicalPathMap records).stateSeq n))⁻¹ := by
  unfold canonicalRecordMeasure
  have h :=
    M.toQMatrix.condExp_next_holdingTime_eq_inv_exitRate_of_no_absorbing
      x₀ hNA n
  simpa [canonicalPathMap, exitRateAt, QMatrix.currentStateFromHistory_frestrictLe]
    using h

/-- Under `NoAbsorbing`, the conditional expectation of the squared next raw
holding time is the second moment of the exponential holding-time law at the
current density-dependent exit rate. -/
theorem condExp_next_holdingTime_sq_eq_two_div_exitRate_sq_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) (n : ℕ) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      MeasureTheory.condExp
          (MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance)
          (M.canonicalRecordMeasure x₀)
          (fun records : M.canonicalRecordΩ => (records (n + 1)).1 ^ 2)
          records =
        2 * (1 / M.exitRateAt ((M.canonicalPathMap records).stateSeq n)) ^ 2 := by
  unfold canonicalRecordMeasure
  have h :=
    M.toQMatrix.condExp_next_holdingTime_sq_eq_two_div_exitRate_sq_of_no_absorbing
      x₀ hNA n
  simpa [canonicalPathMap, exitRateAt, QMatrix.currentStateFromHistory_frestrictLe]
    using h

theorem integrable_next_holdingTime_canonicalRecordMeasure_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
      (M.canonicalRecordMeasure x₀) := by
  unfold canonicalRecordMeasure
  exact M.toQMatrix.integrable_next_holdingTime_canonicalRecordMeasure x₀ hNA n

theorem integrable_next_holdingTime_sq_canonicalRecordMeasure_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ => (records (n + 1)).1 ^ 2)
      (M.canonicalRecordMeasure x₀) := by
  unfold canonicalRecordMeasure
  exact M.toQMatrix.integrable_next_holdingTime_sq_canonicalRecordMeasure x₀ hNA n

/-- Under `NoAbsorbing`, the conditional law of the next raw record state is
the embedded jump-chain row from the current finite history state. -/
theorem condDistrib_canonicalRecordMeasure_next_state_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) (n : ℕ) :
    ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
      ProbabilityTheory.condDistrib
          (fun records : M.canonicalRecordΩ => (records (n + 1)).2)
          (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
        M.toQMatrix.embeddedStepMeasure
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n hist) := by
  unfold canonicalRecordMeasure
  filter_upwards
    [M.toQMatrix.condDistrib_canonicalRecordMeasure_next_state_of_nonabsorbing
      x₀ n]
    with hist hhist
  exact hhist (hNA
    (QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n hist))

/-- Canonical density-dependent non-explosion bridge: after the
large-holding-time count has been proved to diverge almost surely, the
canonical path readout is non-explosive almost surely. -/
theorem canonicalPathMap_nonExplosive_ae_of_large_count_tendsto
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    {ε : ℝ} (hε : 0 < ε)
    (hcount : ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      Filter.Tendsto
        (fun K : ℕ =>
          (((Finset.range K).filter fun k =>
            ε ≤ (M.canonicalPathMap records).holdingTime k).card : ℝ))
        Filter.atTop Filter.atTop) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      (M.canonicalPathMap records).NonExplosive := by
  simpa [canonicalRecordMeasure, canonicalPathMap] using
    M.toQMatrix.canonicalRecordMeasure_nonExplosive_ae_of_large_count_tendsto
      x₀ hNA hε hcount

/-- Strict-threshold version of
`canonicalPathMap_nonExplosive_ae_of_large_count_tendsto`, aligned with
conditional tail events `Set.Ioi ε`. -/
theorem canonicalPathMap_nonExplosive_ae_of_large_strict_count_tendsto
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    {ε : ℝ} (hε : 0 < ε)
    (hcount : ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      Filter.Tendsto
        (fun K : ℕ =>
          (((Finset.range K).filter fun k =>
            ε < (M.canonicalPathMap records).holdingTime k).card : ℝ))
        Filter.atTop Filter.atTop) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      (M.canonicalPathMap records).NonExplosive := by
  simpa [canonicalRecordMeasure, canonicalPathMap] using
    M.toQMatrix.canonicalRecordMeasure_nonExplosive_ae_of_large_strict_count_tendsto
      x₀ hNA hε hcount

/-- Under `NoAbsorbing`, the canonical density-dependent path readout is
non-explosive almost surely. -/
theorem canonicalPathMap_nonExplosive_ae_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      (M.canonicalPathMap records).NonExplosive := by
  simpa [canonicalRecordMeasure, canonicalPathMap] using
    M.toQMatrix.canonicalRecordMeasure_recordTrajectoryToPath_nonExplosive_ae_of_no_absorbing
      x₀ hNA

/-- The embedded jump chain of the density-dependent Q-matrix has no self-jump
from a non-absorbing state. -/
theorem embeddedDTMC_step_self_of_nonabsorbing
    (x : Fin d → Fin (M.N + 1)) (h : ¬M.toQMatrix.IsAbsorbing x) :
    M.toQMatrix.embeddedDTMC.step x x = 0 :=
  M.toQMatrix.embeddedDTMC_step_self_of_nonabsorbing h

/-- Positive density-dependent off-diagonal rate gives positive one-step
probability in the embedded jump chain. -/
theorem embeddedDTMC_step_pos_of_offDiagRate_pos
    {x y : Fin d → Fin (M.N + 1)} (hxy : x ≠ y)
    (hrate : 0 < M.offDiagRate x y) :
    0 < M.toQMatrix.embeddedDTMC.step x y := by
  have hq : 0 < M.toQMatrix.rate x y := by
    simpa only [toQMatrix, qMatrixRate, if_neg hxy] using hrate
  exact M.toQMatrix.embeddedDTMC_step_pos_of_rate_pos hxy hq

/-- Zero density-dependent off-diagonal rate gives zero one-step probability
in the embedded jump chain, for non-absorbing source states. -/
theorem embeddedDTMC_step_eq_zero_of_offDiagRate_eq_zero
    {x y : Fin d → Fin (M.N + 1)} (hsrc : ¬M.toQMatrix.IsAbsorbing x)
    (hxy : x ≠ y) (hrate : M.offDiagRate x y = 0) :
    M.toQMatrix.embeddedDTMC.step x y = 0 := by
  have hq : M.toQMatrix.rate x y = 0 := by
    simpa only [toQMatrix, qMatrixRate, if_neg hxy] using hrate
  exact M.toQMatrix.embeddedDTMC_step_eq_zero_of_rate_eq_zero hsrc hxy hq

/-! ## Scaled lattice states -/

/-- Scale a finite population state by the population size. -/
noncomputable def scaledState (x : Fin d → Fin (M.N + 1)) : Fin d → ℝ :=
  fun i => (x i : ℝ) / (M.N : ℝ)

/-- Total population count of a lattice state in the ambient cube. -/
def totalCount (x : Fin d → Fin (M.N + 1)) : ℕ :=
  ∑ i, (x i : ℕ)

/-- The population simplex inside the ambient cube: states with total count
equal to `N`.  Population protocols should live on this invariant subset. -/
def InSimplex (x : Fin d → Fin (M.N + 1)) : Prop :=
  M.totalCount x = M.N

/-- All listed jumps preserve total population. -/
def ConservativeJumps : Prop :=
  ∀ ℓ ∈ M.rateSpec.jumps, ∑ i, ℓ i = 0

/-- Scaled lattice states lie in the unit cube, hence have sup-norm at most 1. -/
theorem scaledState_norm_le (x : Fin d → Fin (M.N + 1)) :
    ‖M.scaledState x‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · rw [scaledState, div_le_one (Nat.cast_pos.mpr M.hN)]
    exact Nat.cast_le.mpr (Fin.is_le _)
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Each coordinate of a scaled lattice state has norm at most `1`. -/
theorem scaledState_apply_norm_le_one
    (x : Fin d → Fin (M.N + 1)) (i : Fin d) :
    ‖M.scaledState x i‖ ≤ 1 := by
  exact (norm_le_pi_norm (M.scaledState x) i).trans (M.scaledState_norm_le x)

/-- Each coordinate of a scaled jump is bounded by `2` in absolute value. -/
theorem scaledState_sub_apply_norm_le_two
    (x y : Fin d → Fin (M.N + 1)) (i : Fin d) :
    ‖(M.scaledState y - M.scaledState x) i‖ ≤ 2 := by
  calc
    ‖(M.scaledState y - M.scaledState x) i‖
        = ‖M.scaledState y i - M.scaledState x i‖ := by
          simp [Pi.sub_apply]
    _ ≤ ‖M.scaledState y i‖ + ‖M.scaledState x i‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add
      (M.scaledState_apply_norm_le_one y i)
      (M.scaledState_apply_norm_le_one x i)
    _ = 2 := by norm_num

/-- The next raw record's coordinate scaled jump, measured from the current
read-out state sequence, is measurable. -/
theorem measurable_next_scaledState_sub_apply
    (n : ℕ) (i : Fin d) :
    Measurable (fun records : M.canonicalRecordΩ =>
      (M.scaledState ((records (n + 1)).2) -
        M.scaledState ((M.canonicalPathMap records).stateSeq n)) i) := by
  have hnext_state : Measurable (fun records : M.canonicalRecordΩ =>
      (records (n + 1)).2) := by
    fun_prop
  have hcurr_state : Measurable (fun records : M.canonicalRecordΩ =>
      (M.canonicalPathMap records).stateSeq n) := by
    simpa [canonicalPathMap] using
      (QMatrix.measurable_recordTrajectoryToPath_stateSeq
        (S := Fin d → Fin (M.N + 1)) n)
  have hnext_coord : Measurable (fun records : M.canonicalRecordΩ =>
      M.scaledState ((records (n + 1)).2) i) :=
    (Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp hnext_state
  have hcurr_coord : Measurable (fun records : M.canonicalRecordΩ =>
      M.scaledState ((M.canonicalPathMap records).stateSeq n) i) :=
    (Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp hcurr_state
  simpa [Pi.sub_apply] using hnext_coord.sub hcurr_coord

/-- The next raw coordinate scaled jump is integrable under the canonical
record law. -/
theorem integrable_next_scaledState_sub_apply
    (x₀ : Fin d → Fin (M.N + 1)) (n : ℕ) (i : Fin d) :
    Integrable (fun records : M.canonicalRecordΩ =>
      (M.scaledState ((records (n + 1)).2) -
        M.scaledState ((M.canonicalPathMap records).stateSeq n)) i)
      (M.canonicalRecordMeasure x₀) := by
  refine Integrable.of_bound
    (M.measurable_next_scaledState_sub_apply n i).aestronglyMeasurable 2 ?_
  exact ae_of_all _ fun records =>
    M.scaledState_sub_apply_norm_le_two
      ((M.canonicalPathMap records).stateSeq n) ((records (n + 1)).2) i

/-- The square of the next raw coordinate scaled jump is measurable. -/
theorem measurable_next_scaledState_sub_apply_sq
    (n : ℕ) (i : Fin d) :
    Measurable (fun records : M.canonicalRecordΩ =>
      ((M.scaledState ((records (n + 1)).2) -
        M.scaledState ((M.canonicalPathMap records).stateSeq n)) i) ^ 2) :=
  (M.measurable_next_scaledState_sub_apply n i).pow_const 2

/-- The square of the next raw coordinate scaled jump is integrable under the
canonical record law. -/
theorem integrable_next_scaledState_sub_apply_sq
    (x₀ : Fin d → Fin (M.N + 1)) (n : ℕ) (i : Fin d) :
    Integrable (fun records : M.canonicalRecordΩ =>
      ((M.scaledState ((records (n + 1)).2) -
        M.scaledState ((M.canonicalPathMap records).stateSeq n)) i) ^ 2)
      (M.canonicalRecordMeasure x₀) := by
  refine Integrable.of_bound
    (M.measurable_next_scaledState_sub_apply_sq n i).aestronglyMeasurable 4 ?_
  refine ae_of_all _ fun records => ?_
  let a : ℝ :=
    (M.scaledState ((records (n + 1)).2) -
      M.scaledState ((M.canonicalPathMap records).stateSeq n)) i
  have ha : ‖a‖ ≤ 2 := by
    exact M.scaledState_sub_apply_norm_le_two
      ((M.canonicalPathMap records).stateSeq n) ((records (n + 1)).2) i
  rw [Real.norm_eq_abs] at ha
  change ‖a ^ 2‖ ≤ 4
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a), ← sq_abs]
  nlinarith [abs_nonneg a]

/-- Conditional expectation of the next coordinate scaled jump, expressed via
the canonical conditional next-state distribution. -/
theorem condExp_next_scaledState_sub_apply_eq_integral_condDistrib
    (x₀ : Fin d → Fin (M.N + 1)) (n : ℕ) (i : Fin d) :
    (M.canonicalRecordMeasure x₀)[
        fun records : M.canonicalRecordΩ =>
          (M.scaledState ((records (n + 1)).2) -
            M.scaledState ((M.canonicalPathMap records).stateSeq n)) i
        | MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance]
        =ᵐ[M.canonicalRecordMeasure x₀]
      fun records : M.canonicalRecordΩ =>
        ∫ y, (M.scaledState y -
            M.scaledState ((M.canonicalPathMap records).stateSeq n)) i
          ∂ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => (records (n + 1)).2)
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀)
            (Preorder.frestrictLe n records) := by
  let μ := M.canonicalRecordMeasure x₀
  let X : M.canonicalRecordΩ →
      ((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) :=
    Preorder.frestrictLe n
  let Y : M.canonicalRecordΩ → (Fin d → Fin (M.N + 1)) :=
    fun records => (records (n + 1)).2
  let f :
      (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
        (Fin d → Fin (M.N + 1))) → ℝ :=
    fun p => (M.scaledState p.2 -
      M.scaledState
        (QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1)) i
  have hX : Measurable X := by
    dsimp [X]
    exact Preorder.measurable_frestrictLe n
  have hY : AEMeasurable Y μ := by
    dsimp [Y]
    exact (by fun_prop : Measurable
      (fun records : M.canonicalRecordΩ => (records (n + 1)).2)).aemeasurable
  have hf_meas : Measurable f := by
    dsimp [f]
    have hnext : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            (Fin d → Fin (M.N + 1))) => p.2) := measurable_snd
    have hcurr : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            (Fin d → Fin (M.N + 1))) =>
          QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1) :=
      (QMatrix.measurable_currentStateFromHistory
        (S := Fin d → Fin (M.N + 1)) n).comp measurable_fst
    have hnext_coord : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            (Fin d → Fin (M.N + 1))) =>
          M.scaledState p.2 i) :=
      (Measurable.of_discrete
        (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp hnext
    have hcurr_coord : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            (Fin d → Fin (M.N + 1))) =>
          M.scaledState
            (QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1) i) :=
      (Measurable.of_discrete
        (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp hcurr
    simpa [Pi.sub_apply] using hnext_coord.sub hcurr_coord
  have hf_int :
      Integrable (fun a : M.canonicalRecordΩ => f (X a, Y a)) μ := by
    dsimp [f, X, Y, μ]
    simpa [canonicalPathMap, QMatrix.currentStateFromHistory_frestrictLe] using
      M.integrable_next_scaledState_sub_apply x₀ n i
  have h :=
    ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib
      (μ := μ) (X := X) (Y := Y) (f := f)
      hX hY hf_meas.stronglyMeasurable hf_int
  simpa [μ, X, Y, f, canonicalRecordFiltration, canonicalPathMap,
    QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe,
    QMatrix.currentStateFromHistory_frestrictLe] using h

/-- Conditional expectation of the squared next coordinate scaled jump,
expressed via the canonical conditional next-state distribution. -/
theorem condExp_next_scaledState_sub_apply_sq_eq_integral_condDistrib
    (x₀ : Fin d → Fin (M.N + 1)) (n : ℕ) (i : Fin d) :
    (M.canonicalRecordMeasure x₀)[
        fun records : M.canonicalRecordΩ =>
          ((M.scaledState ((records (n + 1)).2) -
            M.scaledState ((M.canonicalPathMap records).stateSeq n)) i) ^ 2
        | MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance]
        =ᵐ[M.canonicalRecordMeasure x₀]
      fun records : M.canonicalRecordΩ =>
        ∫ y, ((M.scaledState y -
            M.scaledState ((M.canonicalPathMap records).stateSeq n)) i) ^ 2
          ∂ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => (records (n + 1)).2)
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀)
            (Preorder.frestrictLe n records) := by
  let μ := M.canonicalRecordMeasure x₀
  let X : M.canonicalRecordΩ →
      ((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) :=
    Preorder.frestrictLe n
  let Y : M.canonicalRecordΩ → (Fin d → Fin (M.N + 1)) :=
    fun records => (records (n + 1)).2
  let f :
      (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
        (Fin d → Fin (M.N + 1))) → ℝ :=
    fun p => ((M.scaledState p.2 -
      M.scaledState
        (QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1)) i) ^ 2
  have hX : Measurable X := by
    dsimp [X]
    exact Preorder.measurable_frestrictLe n
  have hY : AEMeasurable Y μ := by
    dsimp [Y]
    exact (by fun_prop : Measurable
      (fun records : M.canonicalRecordΩ => (records (n + 1)).2)).aemeasurable
  have hf_meas : Measurable f := by
    dsimp [f]
    have hnext : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            (Fin d → Fin (M.N + 1))) => p.2) := measurable_snd
    have hcurr : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            (Fin d → Fin (M.N + 1))) =>
          QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1) :=
      (QMatrix.measurable_currentStateFromHistory
        (S := Fin d → Fin (M.N + 1)) n).comp measurable_fst
    have hnext_coord : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            (Fin d → Fin (M.N + 1))) =>
          M.scaledState p.2 i) :=
      (Measurable.of_discrete
        (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp hnext
    have hcurr_coord : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            (Fin d → Fin (M.N + 1))) =>
          M.scaledState
            (QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1) i) :=
      (Measurable.of_discrete
        (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp hcurr
    simpa [Pi.sub_apply] using (hnext_coord.sub hcurr_coord).pow_const 2
  have hf_int :
      Integrable (fun a : M.canonicalRecordΩ => f (X a, Y a)) μ := by
    dsimp [f, X, Y, μ]
    simpa [canonicalPathMap, QMatrix.currentStateFromHistory_frestrictLe] using
      M.integrable_next_scaledState_sub_apply_sq x₀ n i
  have h :=
    ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib
      (μ := μ) (X := X) (Y := Y) (f := f)
      hX hY hf_meas.stronglyMeasurable hf_int
  simpa [μ, X, Y, f, canonicalRecordFiltration, canonicalPathMap,
    QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe,
    QMatrix.currentStateFromHistory_frestrictLe] using h

/-- If `y - x = ℓ` componentwise on the lattice, then the scaled-state
difference is `ℓ / N`. -/
theorem scaledState_sub_eq_of_jump {x y : Fin d → Fin (M.N + 1)}
    {ℓ : Fin d → ℤ}
    (hxy : ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i) :
    M.scaledState y - M.scaledState x =
      fun i => (ℓ i : ℝ) / (M.N : ℝ) := by
  ext i
  simp only [scaledState, Pi.sub_apply]
  have hreal : (y i : ℝ) - (x i : ℝ) = (ℓ i : ℝ) := by
    norm_num [← hxy i]
  rw [← hreal]
  ring

/-- Finite sum of scaled state increments along the first `n` path
transitions. -/
noncomputable def scaledJumpSum
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (n : ℕ) : Fin d → ℝ :=
  fun i => ∑ k ∈ Finset.range n,
    (M.scaledState (path.stateSeq (k + 1)) -
      M.scaledState (path.stateSeq k)) i

/-- At a fixed jump index, each coordinate of the scaled jump sum is
measurable with respect to the canonical record history through that index. -/
theorem measurable_scaledJumpSum_apply_canonicalRecordFiltration
    (i : Fin d) (n : ℕ) :
    Measurable[M.canonicalRecordFiltration n]
      (fun records : M.canonicalRecordΩ =>
        M.scaledJumpSum (M.canonicalPathMap records) n i) := by
  simp only [scaledJumpSum]
  refine Finset.measurable_sum _ ?_
  intro k hk
  have hk_lt : k < n := Finset.mem_range.mp hk
  have hnext_state :
      Measurable[M.canonicalRecordFiltration n]
        (fun records : M.canonicalRecordΩ =>
          (M.canonicalPathMap records).stateSeq (k + 1)) :=
    M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration_le
      (Nat.succ_le_iff.mpr hk_lt)
  have hcurr_state :
      Measurable[M.canonicalRecordFiltration n]
        (fun records : M.canonicalRecordΩ =>
          (M.canonicalPathMap records).stateSeq k) :=
    M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration_le
      (le_of_lt hk_lt)
  have hnext_coord :
      Measurable[M.canonicalRecordFiltration n]
        (fun records : M.canonicalRecordΩ =>
          M.scaledState ((M.canonicalPathMap records).stateSeq (k + 1)) i) :=
    (Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp
        hnext_state
  have hcurr_coord :
      Measurable[M.canonicalRecordFiltration n]
        (fun records : M.canonicalRecordΩ =>
          M.scaledState ((M.canonicalPathMap records).stateSeq k) i) :=
    (Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp
        hcurr_state
  simpa [Pi.sub_apply] using hnext_coord.sub hcurr_coord

/-- Each coordinate of the scaled jump-sum process is adapted to the canonical
record filtration. -/
theorem adapted_scaledJumpSum_apply_canonicalRecordFiltration
    (i : Fin d) :
    MeasureTheory.Adapted M.canonicalRecordFiltration
      (fun n records => M.scaledJumpSum (M.canonicalPathMap records) n i) :=
  fun n => M.measurable_scaledJumpSum_apply_canonicalRecordFiltration i n

/-- Each coordinate of the scaled jump-sum process is strongly adapted to the
canonical record filtration. -/
theorem stronglyAdapted_scaledJumpSum_apply_canonicalRecordFiltration
    (i : Fin d) :
    MeasureTheory.StronglyAdapted M.canonicalRecordFiltration
      (fun n records => M.scaledJumpSum (M.canonicalPathMap records) n i) :=
  fun n => (M.measurable_scaledJumpSum_apply_canonicalRecordFiltration i n).stronglyMeasurable

/-- Each coordinate of the scaled jump-sum process is integrable at every jump
index under the canonical record law. -/
theorem integrable_scaledJumpSum_apply_canonicalRecordMeasure
    (x₀ : Fin d → Fin (M.N + 1)) (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.scaledJumpSum (M.canonicalPathMap records) n i)
      (M.canonicalRecordMeasure x₀) := by
  refine Integrable.of_bound
    ((M.measurable_scaledJumpSum_apply_canonicalRecordFiltration i n).mono
      (M.canonicalRecordFiltration.le n) le_rfl).aestronglyMeasurable
    ((n : ℝ) * 2) ?_
  refine ae_of_all _ fun records => ?_
  simp only [scaledJumpSum]
  calc
    ‖(fun i => ∑ k ∈ Finset.range n,
      (M.scaledState ((M.canonicalPathMap records).stateSeq (k + 1)) -
        M.scaledState ((M.canonicalPathMap records).stateSeq k)) i) i‖
        = ‖∑ k ∈ Finset.range n,
            (M.scaledState ((M.canonicalPathMap records).stateSeq (k + 1)) -
              M.scaledState ((M.canonicalPathMap records).stateSeq k)) i‖ := rfl
    _ ≤ ∑ k ∈ Finset.range n,
        ‖(M.scaledState ((M.canonicalPathMap records).stateSeq (k + 1)) -
          M.scaledState ((M.canonicalPathMap records).stateSeq k)) i‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range n, (2 : ℝ) := by
        exact Finset.sum_le_sum fun k _ =>
          M.scaledState_sub_apply_norm_le_two
            ((M.canonicalPathMap records).stateSeq k)
            ((M.canonicalPathMap records).stateSeq (k + 1)) i
    _ = (n : ℝ) * 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Scaled states telescope along the path state sequence. -/
theorem scaledState_stateSeq_eq_init_add_scaledJumpSum
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (n : ℕ) :
    M.scaledState (path.stateSeq n) =
      M.scaledState path.init + M.scaledJumpSum path n := by
  ext i
  induction n with
  | zero =>
      simp [scaledJumpSum]
  | succ n ih =>
      have ih' : M.scaledState (path.stateSeq n) i =
          M.scaledState path.init i +
            ∑ k ∈ Finset.range n,
              (M.scaledState (path.stateSeq (k + 1)) -
                M.scaledState (path.stateSeq k)) i := by
        simpa [scaledJumpSum] using ih
      simp only [scaledJumpSum, Finset.sum_range_succ, Pi.add_apply, Pi.sub_apply]
      calc
        M.scaledState (path.stateSeq (n + 1)) i
            = M.scaledState (path.stateSeq n) i +
                (M.scaledState (path.stateSeq (n + 1)) i -
                  M.scaledState (path.stateSeq n) i) := by ring
        _ = (M.scaledState path.init i +
              ∑ k ∈ Finset.range n,
                (M.scaledState (path.stateSeq (k + 1)) -
                  M.scaledState (path.stateSeq k)) i) +
              (M.scaledState (path.stateSeq (n + 1)) i -
                M.scaledState (path.stateSeq n) i) := by rw [ih']
        _ = M.scaledState path.init i +
              (∑ k ∈ Finset.range n,
                (M.scaledState (path.stateSeq (k + 1)) -
                  M.scaledState (path.stateSeq k)) i +
                (M.scaledState (path.stateSeq (n + 1)) i -
                  M.scaledState (path.stateSeq n) i)) := by ring

/-- A listed jump changes the scaled state by at most `jumpNormBound / N`. -/
theorem scaledState_jump_norm_le_bound {x y : Fin d → Fin (M.N + 1)}
    {ℓ : Fin d → ℤ}
    (hℓ : ℓ ∈ M.rateSpec.jumps)
    (hxy : ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i) :
    ‖M.scaledState y - M.scaledState x‖ ≤
      M.rateSpec.jumpNormBound / (M.N : ℝ) := by
  rw [M.scaledState_sub_eq_of_jump hxy]
  have hscale :
      (fun i : Fin d => (ℓ i : ℝ) / (M.N : ℝ)) =
        (1 / (M.N : ℝ)) • (fun i : Fin d => (ℓ i : ℝ)) := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, one_div]
    ring
  rw [hscale, norm_smul]
  have hNnorm : ‖1 / (M.N : ℝ)‖ = 1 / (M.N : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    positivity
  rw [hNnorm]
  have hbound := M.rateSpec.jump_norm_le_bound hℓ
  have hscale_nonneg : 0 ≤ 1 / (M.N : ℝ) := by positivity
  calc
    (1 / (M.N : ℝ)) * ‖(fun i : Fin d => (ℓ i : ℝ))‖
        ≤ (1 / (M.N : ℝ)) * M.rateSpec.jumpNormBound :=
          mul_le_mul_of_nonneg_left hbound hscale_nonneg
    _ = M.rateSpec.jumpNormBound / (M.N : ℝ) := by ring

/-- A realized jump whose coordinate changes sum to zero preserves the total
population count. -/
theorem totalCount_eq_of_jump_match {x y : Fin d → Fin (M.N + 1)}
    {ℓ : Fin d → ℤ}
    (hmatch : ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i)
    (hsum : ∑ i, ℓ i = 0) :
    M.totalCount y = M.totalCount x := by
  have hdiff : (M.totalCount y : ℤ) - (M.totalCount x : ℤ) = 0 := by
    calc
      (M.totalCount y : ℤ) - (M.totalCount x : ℤ)
          = (∑ i, (y i : ℤ)) - (∑ i, (x i : ℤ)) := by
            simp [totalCount]
      _ = ∑ i, ((y i : ℤ) - (x i : ℤ)) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ i, ℓ i := by
            apply Finset.sum_congr rfl
            intro i _
            exact hmatch i
      _ = 0 := hsum
  have hcast : (M.totalCount y : ℤ) = (M.totalCount x : ℤ) := by
    linarith
  exact Int.ofNat.inj hcast

/-- A positive density-dependent off-diagonal rate is witnessed by a listed
jump vector matching the source and target states. -/
theorem exists_jump_of_offDiagRate_pos {x y : Fin d → Fin (M.N + 1)}
    (hpos : 0 < M.offDiagRate x y) :
    ∃ ℓ ∈ M.rateSpec.jumps, ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i := by
  by_cases hxy : x = y
  · simp [offDiagRate, hxy] at hpos
  · have hsumpos : 0 < ∑ ℓ ∈ M.rateSpec.jumps.filter
        (fun ℓ : Fin d → ℤ => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i),
        (M.N : ℝ) * M.rateSpec.rate ℓ (M.scaledState x) := by
      simpa [offDiagRate, hxy] using hpos
    have hnonneg : ∀ ℓ ∈ M.rateSpec.jumps.filter
        (fun ℓ : Fin d → ℤ => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i),
        0 ≤ (M.N : ℝ) * M.rateSpec.rate ℓ (M.scaledState x) := by
      intro ℓ hℓ
      have hmem : ℓ ∈ M.rateSpec.jumps := (Finset.mem_filter.mp hℓ).1
      exact mul_nonneg (Nat.cast_nonneg _)
        (M.rateSpec.rate_nonneg ℓ hmem (M.scaledState x) fun i =>
          div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    obtain ⟨ℓ, hℓfilter, _hterm⟩ :=
      (Finset.sum_pos_iff_of_nonneg hnonneg).mp hsumpos
    exact ⟨ℓ, (Finset.mem_filter.mp hℓfilter).1,
      (Finset.mem_filter.mp hℓfilter).2⟩

/-- If all listed jumps are conservative, every positive transition preserves
the total population count. -/
theorem totalCount_eq_of_offDiagRate_pos (hcons : M.ConservativeJumps)
    {x y : Fin d → Fin (M.N + 1)} (hpos : 0 < M.offDiagRate x y) :
    M.totalCount y = M.totalCount x := by
  obtain ⟨ℓ, hℓ, hmatch⟩ := M.exists_jump_of_offDiagRate_pos hpos
  exact M.totalCount_eq_of_jump_match hmatch (hcons ℓ hℓ)

/-- The population simplex is invariant under positive off-diagonal
transitions when all listed jumps conserve total count. -/
theorem inSimplex_of_offDiagRate_pos (hcons : M.ConservativeJumps)
    {x y : Fin d → Fin (M.N + 1)} (hx : M.InSimplex x)
    (hpos : 0 < M.offDiagRate x y) :
    M.InSimplex y := by
  unfold InSimplex at hx ⊢
  rw [M.totalCount_eq_of_offDiagRate_pos hcons hpos, hx]

/-- A realized path uses only positive density-dependent off-diagonal rates
between consecutive states.  This is stronger than the current
`CTMCPath.IsCompatible` predicate and is the deterministic invariant needed for
simplex restriction. -/
def PathUsesPositiveRates (path : CTMCPath (Fin d → Fin (M.N + 1))) : Prop :=
  ∀ n, 0 < M.offDiagRate (path.stateSeq n) (path.stateSeq (n + 1))

/-- Under `NoAbsorbing`, the canonical read-out path uses only positive
density-dependent off-diagonal transition rates almost surely. -/
theorem canonicalPathMap_pathUsesPositiveRates_ae_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      M.PathUsesPositiveRates (M.canonicalPathMap records) := by
  unfold canonicalRecordMeasure
  filter_upwards
    [M.toQMatrix.canonicalRecordMeasure_all_next_rate_pos_ae_of_nonabsorbing x₀]
    with records hrecords
  intro n
  have hn := hrecords n (hNA _)
  have hq : 0 < M.toQMatrix.rate (records n).2 (records (n + 1)).2 := by
    simpa [QMatrix.currentStateFromHistory] using hn
  simpa [canonicalPathMap] using
    M.offDiagRate_pos_of_toQMatrix_rate_pos hq

/-- Along a path using only positive transition rates, every scaled jump has
the deterministic `O(1/N)` jump-size bound. -/
theorem scaledState_sub_stateSeq_norm_le_of_pathUsesPositiveRates
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (hpath : M.PathUsesPositiveRates path) (n : ℕ) :
    ‖M.scaledState (path.stateSeq (n + 1)) -
        M.scaledState (path.stateSeq n)‖ ≤
      M.rateSpec.jumpNormBound / (M.N : ℝ) := by
  obtain ⟨ℓ, hℓ, hmatch⟩ := M.exists_jump_of_offDiagRate_pos (hpath n)
  exact M.scaledState_jump_norm_le_bound hℓ hmatch

/-- Squared version of
`scaledState_sub_stateSeq_norm_le_of_pathUsesPositiveRates`. -/
theorem scaledState_sub_stateSeq_norm_sq_le_of_pathUsesPositiveRates
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (hpath : M.PathUsesPositiveRates path) (n : ℕ) :
    ‖M.scaledState (path.stateSeq (n + 1)) -
        M.scaledState (path.stateSeq n)‖ ^ 2 ≤
      (M.rateSpec.jumpNormBound / (M.N : ℝ)) ^ 2 := by
  have hnorm := M.scaledState_sub_stateSeq_norm_le_of_pathUsesPositiveRates
    path hpath n
  have hleft_nonneg :
      0 ≤ ‖M.scaledState (path.stateSeq (n + 1)) -
        M.scaledState (path.stateSeq n)‖ := norm_nonneg _
  have hright_nonneg : 0 ≤ M.rateSpec.jumpNormBound / (M.N : ℝ) := by
    exact div_nonneg M.rateSpec.jumpNormBound_nonneg (le_of_lt (Nat.cast_pos.mpr M.hN))
  nlinarith

/-- Under `NoAbsorbing`, canonical record paths satisfy the deterministic
scaled-jump-size bound at every jump almost surely. -/
theorem canonicalPathMap_scaledState_sub_stateSeq_norm_le_ae_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ n : ℕ,
      ‖M.scaledState ((M.canonicalPathMap records).stateSeq (n + 1)) -
          M.scaledState ((M.canonicalPathMap records).stateSeq n)‖ ≤
        M.rateSpec.jumpNormBound / (M.N : ℝ) := by
  filter_upwards [M.canonicalPathMap_pathUsesPositiveRates_ae_of_noAbsorbing x₀ hNA]
    with records hpath n
  exact M.scaledState_sub_stateSeq_norm_le_of_pathUsesPositiveRates
    (M.canonicalPathMap records) hpath n

/-- Squared canonical scaled-jump-size bound. -/
theorem canonicalPathMap_scaledState_sub_stateSeq_norm_sq_le_ae_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ n : ℕ,
      ‖M.scaledState ((M.canonicalPathMap records).stateSeq (n + 1)) -
          M.scaledState ((M.canonicalPathMap records).stateSeq n)‖ ^ 2 ≤
        (M.rateSpec.jumpNormBound / (M.N : ℝ)) ^ 2 := by
  filter_upwards [M.canonicalPathMap_pathUsesPositiveRates_ae_of_noAbsorbing x₀ hNA]
    with records hpath n
  exact M.scaledState_sub_stateSeq_norm_sq_le_of_pathUsesPositiveRates
    (M.canonicalPathMap records) hpath n

/-- Sum of squared scaled jump sizes along the first `n` path transitions. -/
noncomputable def scaledJumpSqSum
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    ‖M.scaledState (path.stateSeq (k + 1)) -
      M.scaledState (path.stateSeq k)‖ ^ 2

@[simp]
theorem scaledJumpSqSum_zero
    (path : CTMCPath (Fin d → Fin (M.N + 1))) :
    M.scaledJumpSqSum path 0 = 0 := by
  simp [scaledJumpSqSum]

/-- The cumulative squared scaled-jump sum is non-negative. -/
theorem scaledJumpSqSum_nonneg
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (n : ℕ) :
    0 ≤ M.scaledJumpSqSum path n := by
  simp only [scaledJumpSqSum]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Recursion for the cumulative squared scaled-jump sum. -/
theorem scaledJumpSqSum_succ
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (n : ℕ) :
    M.scaledJumpSqSum path (n + 1) =
      M.scaledJumpSqSum path n +
        ‖M.scaledState (path.stateSeq (n + 1)) -
          M.scaledState (path.stateSeq n)‖ ^ 2 := by
  simp [scaledJumpSqSum, Finset.sum_range_succ]

/-- The cumulative squared scaled-jump sum is monotone in the number of
included jumps. -/
theorem scaledJumpSqSum_mono
    (path : CTMCPath (Fin d → Fin (M.N + 1))) {m n : ℕ} (hmn : m ≤ n) :
    M.scaledJumpSqSum path m ≤ M.scaledJumpSqSum path n := by
  simp only [scaledJumpSqSum]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by
      intro k hk
      exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hmn))
    (fun _ _ _ => sq_nonneg _)

/-- Sum of squared scaled jump sizes in a single coordinate along the first
`n` path transitions.  This is the coordinate-level bracket skeleton. -/
noncomputable def scaledCoordJumpSqSum
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    ((M.scaledState (path.stateSeq (k + 1)) -
      M.scaledState (path.stateSeq k)) i) ^ 2

@[simp]
theorem scaledCoordJumpSqSum_zero
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) :
    M.scaledCoordJumpSqSum path i 0 = 0 := by
  simp [scaledCoordJumpSqSum]

/-- Coordinate cumulative squared scaled-jump sums are non-negative. -/
theorem scaledCoordJumpSqSum_nonneg
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) :
    0 ≤ M.scaledCoordJumpSqSum path i n := by
  simp only [scaledCoordJumpSqSum]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Recursion for the coordinate cumulative squared scaled-jump sum. -/
theorem scaledCoordJumpSqSum_succ
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) :
    M.scaledCoordJumpSqSum path i (n + 1) =
      M.scaledCoordJumpSqSum path i n +
        ((M.scaledState (path.stateSeq (n + 1)) -
          M.scaledState (path.stateSeq n)) i) ^ 2 := by
  simp [scaledCoordJumpSqSum, Finset.sum_range_succ]

/-- At a fixed jump index, the coordinate cumulative squared-jump sum is
measurable with respect to the canonical record history through that index. -/
theorem measurable_scaledCoordJumpSqSum_canonicalRecordFiltration
    (i : Fin d) (n : ℕ) :
    Measurable[M.canonicalRecordFiltration n]
      (fun records : M.canonicalRecordΩ =>
        M.scaledCoordJumpSqSum (M.canonicalPathMap records) i n) := by
  induction n with
  | zero =>
      simp [scaledCoordJumpSqSum]
  | succ n ih =>
      have ih_later :
          Measurable[M.canonicalRecordFiltration (n + 1)]
            (fun records : M.canonicalRecordΩ =>
              M.scaledCoordJumpSqSum (M.canonicalPathMap records) i n) :=
        ih.mono ((M.canonicalRecordFiltration).mono (Nat.le_succ n)) le_rfl
      have hnext_state :
          Measurable[M.canonicalRecordFiltration (n + 1)]
            (fun records : M.canonicalRecordΩ =>
              (M.canonicalPathMap records).stateSeq (n + 1)) :=
        M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration (n + 1)
      have hcurr_state :
          Measurable[M.canonicalRecordFiltration (n + 1)]
            (fun records : M.canonicalRecordΩ =>
              (M.canonicalPathMap records).stateSeq n) :=
        M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration_le
          (Nat.le_succ n)
      have hnext_coord :
          Measurable[M.canonicalRecordFiltration (n + 1)]
            (fun records : M.canonicalRecordΩ =>
              M.scaledState ((M.canonicalPathMap records).stateSeq (n + 1)) i) :=
        (Measurable.of_discrete
          (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp
            hnext_state
      have hcurr_coord :
          Measurable[M.canonicalRecordFiltration (n + 1)]
            (fun records : M.canonicalRecordΩ =>
              M.scaledState ((M.canonicalPathMap records).stateSeq n) i) :=
        (Measurable.of_discrete
          (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp
            hcurr_state
      have hjump :
          Measurable[M.canonicalRecordFiltration (n + 1)]
            (fun records : M.canonicalRecordΩ =>
              ((M.scaledState ((M.canonicalPathMap records).stateSeq (n + 1)) -
                M.scaledState ((M.canonicalPathMap records).stateSeq n)) i) ^ 2) := by
        simpa [Pi.sub_apply] using (hnext_coord.sub hcurr_coord).pow_const 2
      simpa [scaledCoordJumpSqSum, Finset.sum_range_succ] using ih_later.add hjump

/-- For each coordinate, the cumulative squared-jump process is adapted to the
canonical record filtration. -/
theorem adapted_scaledCoordJumpSqSum_canonicalRecordFiltration
    (i : Fin d) :
    MeasureTheory.Adapted M.canonicalRecordFiltration
      (fun n records => M.scaledCoordJumpSqSum (M.canonicalPathMap records) i n) :=
  fun n => M.measurable_scaledCoordJumpSqSum_canonicalRecordFiltration i n

/-- For each coordinate, the cumulative squared-jump process is strongly
adapted to the canonical record filtration. -/
theorem stronglyAdapted_scaledCoordJumpSqSum_canonicalRecordFiltration
    (i : Fin d) :
    MeasureTheory.StronglyAdapted M.canonicalRecordFiltration
      (fun n records => M.scaledCoordJumpSqSum (M.canonicalPathMap records) i n) :=
  fun n => (M.measurable_scaledCoordJumpSqSum_canonicalRecordFiltration i n).stronglyMeasurable

/-- For each coordinate, the cumulative squared-jump process is integrable at
every jump index under the canonical record law. -/
theorem integrable_scaledCoordJumpSqSum_canonicalRecordMeasure
    (x₀ : Fin d → Fin (M.N + 1)) (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.scaledCoordJumpSqSum (M.canonicalPathMap records) i n)
      (M.canonicalRecordMeasure x₀) := by
  refine Integrable.of_bound
    ((M.measurable_scaledCoordJumpSqSum_canonicalRecordFiltration i n).mono
      (M.canonicalRecordFiltration.le n) le_rfl).aestronglyMeasurable
    ((n : ℝ) * 4) ?_
  refine ae_of_all _ fun records => ?_
  simp only [scaledCoordJumpSqSum]
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · calc
      ∑ k ∈ Finset.range n,
          ((M.scaledState ((M.canonicalPathMap records).stateSeq (k + 1)) -
            M.scaledState ((M.canonicalPathMap records).stateSeq k)) i) ^ 2
          ≤ ∑ _k ∈ Finset.range n, (4 : ℝ) := by
            exact Finset.sum_le_sum fun k _ => by
              let a : ℝ :=
                (M.scaledState ((M.canonicalPathMap records).stateSeq (k + 1)) -
                  M.scaledState ((M.canonicalPathMap records).stateSeq k)) i
              have ha : ‖a‖ ≤ 2 := by
                exact M.scaledState_sub_apply_norm_le_two
                  ((M.canonicalPathMap records).stateSeq k)
                  ((M.canonicalPathMap records).stateSeq (k + 1)) i
              rw [Real.norm_eq_abs] at ha
              change a ^ 2 ≤ 4
              rw [← sq_abs]
              nlinarith [abs_nonneg a]
      _ = (n : ℝ) * 4 := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Coordinate cumulative squared scaled-jump sums are monotone in the number
of included jumps. -/
theorem scaledCoordJumpSqSum_mono
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d)
    {m n : ℕ} (hmn : m ≤ n) :
    M.scaledCoordJumpSqSum path i m ≤ M.scaledCoordJumpSqSum path i n := by
  simp only [scaledCoordJumpSqSum]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by
      intro k hk
      exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hmn))
    (fun _ _ _ => sq_nonneg _)

/-- A coordinate squared jump is bounded by the vector squared jump. -/
theorem scaledState_sub_stateSeq_coord_sq_le_norm_sq
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) :
    ((M.scaledState (path.stateSeq (n + 1)) -
      M.scaledState (path.stateSeq n)) i) ^ 2 ≤
    ‖M.scaledState (path.stateSeq (n + 1)) -
      M.scaledState (path.stateSeq n)‖ ^ 2 := by
  have hcoord :
      |(M.scaledState (path.stateSeq (n + 1)) -
        M.scaledState (path.stateSeq n)) i| ≤
      ‖M.scaledState (path.stateSeq (n + 1)) -
        M.scaledState (path.stateSeq n)‖ := by
    simpa [Real.norm_eq_abs] using
      norm_le_pi_norm
        (M.scaledState (path.stateSeq (n + 1)) -
          M.scaledState (path.stateSeq n)) i
  rw [← sq_abs]
  nlinarith [norm_nonneg
    (M.scaledState (path.stateSeq (n + 1)) -
      M.scaledState (path.stateSeq n)),
    abs_nonneg ((M.scaledState (path.stateSeq (n + 1)) -
      M.scaledState (path.stateSeq n)) i)]

/-- Coordinate cumulative squared jumps are bounded by the vector cumulative
squared-jump sum. -/
theorem scaledCoordJumpSqSum_le_scaledJumpSqSum
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) :
    M.scaledCoordJumpSqSum path i n ≤ M.scaledJumpSqSum path n := by
  simp only [scaledCoordJumpSqSum, scaledJumpSqSum]
  exact Finset.sum_le_sum fun k _ =>
    M.scaledState_sub_stateSeq_coord_sq_le_norm_sq path i k

/-- The cumulative squared scaled-jump sum, sampled at `jumpCount`, is
monotone in clock time along a non-explosive path with strictly increasing jump
times. -/
theorem scaledJumpSqSum_jumpCount_mono_of_nonExplosive
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (hne : path.NonExplosive)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    {s t : ℝ} (hst : s ≤ t) :
    M.scaledJumpSqSum path (path.jumpCount s) ≤
      M.scaledJumpSqSum path (path.jumpCount t) := by
  have hs_future : ∃ n, s < path.times n := path.exists_bound_of_nonExplosive hne s
  have ht_future : ∃ n, t < path.times n := path.exists_bound_of_nonExplosive hne t
  exact M.scaledJumpSqSum_mono path
    (path.jumpCount_mono hstrict hst hs_future ht_future)

/-- Cumulative deterministic bound for squared scaled jump sizes along a
positive-rate path. -/
theorem scaledJumpSqSum_le_of_pathUsesPositiveRates
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (hpath : M.PathUsesPositiveRates path) (n : ℕ) :
    M.scaledJumpSqSum path n ≤
      (n : ℝ) * (M.rateSpec.jumpNormBound / (M.N : ℝ)) ^ 2 := by
  simp only [scaledJumpSqSum]
  calc
    ∑ k ∈ Finset.range n,
        ‖M.scaledState (path.stateSeq (k + 1)) -
          M.scaledState (path.stateSeq k)‖ ^ 2
        ≤ ∑ _k ∈ Finset.range n,
          (M.rateSpec.jumpNormBound / (M.N : ℝ)) ^ 2 := by
          exact Finset.sum_le_sum fun k _ =>
            M.scaledState_sub_stateSeq_norm_sq_le_of_pathUsesPositiveRates path hpath k
    _ = (n : ℝ) * (M.rateSpec.jumpNormBound / (M.N : ℝ)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Canonical a.s. cumulative squared-jump bound. -/
theorem canonicalPathMap_scaledJumpSqSum_le_ae_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ n : ℕ,
      M.scaledJumpSqSum (M.canonicalPathMap records) n ≤
        (n : ℝ) * (M.rateSpec.jumpNormBound / (M.N : ℝ)) ^ 2 := by
  filter_upwards [M.canonicalPathMap_pathUsesPositiveRates_ae_of_noAbsorbing x₀ hNA]
    with records hpath n
  exact M.scaledJumpSqSum_le_of_pathUsesPositiveRates
    (M.canonicalPathMap records) hpath n

/-- Canonical a.s. cumulative squared-jump bound through the random
`jumpCount T`. -/
theorem canonicalPathMap_scaledJumpSqSum_jumpCount_le_ae_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ T : ℝ,
      M.scaledJumpSqSum (M.canonicalPathMap records)
          ((M.canonicalPathMap records).jumpCount T) ≤
        ((M.canonicalPathMap records).jumpCount T : ℝ) *
          (M.rateSpec.jumpNormBound / (M.N : ℝ)) ^ 2 := by
  filter_upwards [M.canonicalPathMap_scaledJumpSqSum_le_ae_of_noAbsorbing x₀ hNA]
    with records hbound T
  exact hbound ((M.canonicalPathMap records).jumpCount T)

/-- Canonical a.s. monotonicity of the cumulative squared-jump process in
clock time. -/
theorem canonicalPathMap_scaledJumpSqSum_jumpCount_mono_ae_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ s t : ℝ, s ≤ t →
      M.scaledJumpSqSum (M.canonicalPathMap records)
          ((M.canonicalPathMap records).jumpCount s) ≤
        M.scaledJumpSqSum (M.canonicalPathMap records)
          ((M.canonicalPathMap records).jumpCount t) := by
  filter_upwards
    [M.canonicalPathMap_isCompatible_ae_of_noAbsorbing x₀ hNA,
      M.canonicalPathMap_nonExplosive_ae_of_noAbsorbing x₀ hNA]
    with records hcompat hne s t hst
  exact M.scaledJumpSqSum_jumpCount_mono_of_nonExplosive
    (M.canonicalPathMap records) hne hcompat.2.1 hst

/-- Canonical a.s. coordinate cumulative squared-jump bound through the random
`jumpCount T`. -/
theorem canonicalPathMap_scaledCoordJumpSqSum_jumpCount_le_ae_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ i : Fin d, ∀ T : ℝ,
      M.scaledCoordJumpSqSum (M.canonicalPathMap records) i
          ((M.canonicalPathMap records).jumpCount T) ≤
        ((M.canonicalPathMap records).jumpCount T : ℝ) *
          (M.rateSpec.jumpNormBound / (M.N : ℝ)) ^ 2 := by
  filter_upwards [M.canonicalPathMap_scaledJumpSqSum_jumpCount_le_ae_of_noAbsorbing x₀ hNA]
    with records hbound i T
  exact (M.scaledCoordJumpSqSum_le_scaledJumpSqSum
    (M.canonicalPathMap records) i
    ((M.canonicalPathMap records).jumpCount T)).trans (hbound T)

/-- Canonical a.s. monotonicity of the coordinate cumulative squared-jump
processes in clock time. -/
theorem canonicalPathMap_scaledCoordJumpSqSum_jumpCount_mono_ae_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ i : Fin d, ∀ s t : ℝ, s ≤ t →
      M.scaledCoordJumpSqSum (M.canonicalPathMap records) i
          ((M.canonicalPathMap records).jumpCount s) ≤
        M.scaledCoordJumpSqSum (M.canonicalPathMap records) i
          ((M.canonicalPathMap records).jumpCount t) := by
  filter_upwards
    [M.canonicalPathMap_isCompatible_ae_of_noAbsorbing x₀ hNA,
      M.canonicalPathMap_nonExplosive_ae_of_noAbsorbing x₀ hNA]
    with records hcompat hne i s t hst
  have hs_future : ∃ n, s < (M.canonicalPathMap records).times n :=
    (M.canonicalPathMap records).exists_bound_of_nonExplosive hne s
  have ht_future : ∃ n, t < (M.canonicalPathMap records).times n :=
    (M.canonicalPathMap records).exists_bound_of_nonExplosive hne t
  exact M.scaledCoordJumpSqSum_mono (M.canonicalPathMap records) i
    ((M.canonicalPathMap records).jumpCount_mono hcompat.2.1 hst hs_future ht_future)

/-- Along a path whose consecutive transitions have positive rates,
conservative jumps preserve the population simplex at every state in the state
sequence. -/
theorem inSimplex_stateSeq_of_pathUsesPositiveRates
    (hcons : M.ConservativeJumps)
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (hinit : M.InSimplex path.init)
    (hpath : M.PathUsesPositiveRates path) :
    ∀ n, M.InSimplex (path.stateSeq n) := by
  intro n
  induction n with
  | zero => simpa using hinit
  | succ n ih =>
      exact M.inSimplex_of_offDiagRate_pos hcons ih (hpath n)

/-- If a non-explosive path uses only positive conservative transitions and
starts in the simplex, then its time readout stays in the simplex for all
finite times. -/
theorem inSimplex_stateAt_of_pathUsesPositiveRates
    (hcons : M.ConservativeJumps)
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (hinit : M.InSimplex path.init)
    (hpath : M.PathUsesPositiveRates path)
    (hne : path.NonExplosive)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (t : ℝ) :
    M.InSimplex (path.stateAt t) := by
  have hseq : ∀ n, M.InSimplex (path.stateSeq n) :=
    M.inSimplex_stateSeq_of_pathUsesPositiveRates hcons path hinit hpath
  rw [path.stateAt_eq_stateSeq_jumpCount_of_nonExplosive hne hstrict t]
  exact hseq (path.jumpCount t)

/-- Under `NoAbsorbing`, conservative jumps, and a simplex initial state, the
canonical density-dependent path remains in the population simplex for all
times almost surely. -/
theorem canonicalPathMap_forall_inSimplex_stateAt_ae_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (hcons : M.ConservativeJumps) (hinit : M.InSimplex x₀) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      ∀ t : ℝ, M.InSimplex ((M.canonicalPathMap records).stateAt t) := by
  filter_upwards
    [M.canonicalPathMap_isCompatible_ae_of_noAbsorbing x₀ hNA,
      M.canonicalPathMap_nonExplosive_ae_of_noAbsorbing x₀ hNA,
      M.canonicalPathMap_pathUsesPositiveRates_ae_of_noAbsorbing x₀ hNA,
      M.toQMatrix.canonicalRecordMeasure_record_zero_eq_init_ae x₀]
    with records hcompat hne hpositive hzero
  intro t
  have hpath_init : M.InSimplex (M.canonicalPathMap records).init := by
    simpa [canonicalPathMap, hzero] using hinit
  exact M.inSimplex_stateAt_of_pathUsesPositiveRates hcons (M.canonicalPathMap records)
    hpath_init hpositive hne hcompat.2.1 t

/-- If all listed rates are bounded by `B` at `x`, then each off-diagonal
Q-matrix entry is bounded by `N * B * #jumps`. -/
theorem offDiagRate_le_of_rate_bound (x y : Fin d → Fin (M.N + 1))
    {B : ℝ} (hB_nonneg : 0 ≤ B)
    (hB : ∀ ℓ ∈ M.rateSpec.jumps, M.rateSpec.rate ℓ (M.scaledState x) ≤ B) :
    M.offDiagRate x y ≤
      (M.N : ℝ) * B * (M.rateSpec.jumps.card : ℝ) := by
  by_cases hxy : x = y
  · rw [offDiagRate, if_pos hxy]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hB_nonneg) (Nat.cast_nonneg _)
  · simp only [offDiagRate, if_neg hxy]
    calc
      ∑ ℓ ∈ M.rateSpec.jumps.filter
            (fun ℓ => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i),
          (M.N : ℝ) * M.rateSpec.rate ℓ (fun i => (x i : ℝ) / (M.N : ℝ))
          ≤ ∑ ℓ ∈ M.rateSpec.jumps.filter
            (fun ℓ => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i),
          (M.N : ℝ) * B := by
            apply Finset.sum_le_sum
            intro ℓ hℓ
            have hmem : ℓ ∈ M.rateSpec.jumps := (Finset.mem_filter.mp hℓ).1
            have hrate := hB ℓ hmem
            exact mul_le_mul_of_nonneg_left hrate (Nat.cast_nonneg _)
      _ = (M.rateSpec.jumps.filter
            (fun ℓ => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i)).card *
          ((M.N : ℝ) * B) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (M.rateSpec.jumps.card : ℝ) * ((M.N : ℝ) * B) := by
            gcongr
            exact M.rateSpec.jumps.filter_subset
              (fun ℓ => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i)
      _ = (M.N : ℝ) * B * (M.rateSpec.jumps.card : ℝ) := by ring

/-- Uniform off-diagonal rate bound on the density-dependent lattice. -/
theorem exists_offDiagRate_bound :
    ∃ C > 0, ∀ x y : Fin d → Fin (M.N + 1),
      M.offDiagRate x y ≤ (M.N : ℝ) * C := by
  obtain ⟨B, hBpos, hB⟩ := M.rateSpec.exists_rate_bound_on_ball 1 zero_lt_one
  refine ⟨B * (M.rateSpec.jumps.card : ℝ) + 1, by positivity, ?_⟩
  intro x y
  have hrate : ∀ ℓ ∈ M.rateSpec.jumps, M.rateSpec.rate ℓ (M.scaledState x) ≤ B := by
    intro ℓ hℓ
    exact (le_abs_self _).trans (hB ℓ hℓ (M.scaledState x) (M.scaledState_norm_le x))
  have hentry := M.offDiagRate_le_of_rate_bound x y (le_of_lt hBpos) hrate
  calc
    M.offDiagRate x y ≤ (M.N : ℝ) * B * (M.rateSpec.jumps.card : ℝ) := hentry
    _ = (M.N : ℝ) * (B * (M.rateSpec.jumps.card : ℝ)) := by ring
    _ ≤ (M.N : ℝ) * (B * (M.rateSpec.jumps.card : ℝ) + 1) := by
      gcongr
      linarith

/-- For a fixed source state and jump vector, there is at most one lattice
target state realizing that jump. -/
theorem matchingStates_card_le_one (x : Fin d → Fin (M.N + 1)) (ℓ : Fin d → ℤ) :
    ((Finset.univ : Finset (Fin d → Fin (M.N + 1))).filter
      (fun y => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i)).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro y z hy hz
  ext i
  have hyi := (Finset.mem_filter.mp hy).2 i
  have hzi := (Finset.mem_filter.mp hz).2 i
  have hint : (y i : ℤ) = (z i : ℤ) := by linarith
  exact Int.ofNat.inj hint

/-- Summing a non-negative constant over all target states matching one fixed
jump contributes at most one copy of that constant. -/
theorem sum_matchingStates_const_le (x : Fin d → Fin (M.N + 1))
    (ℓ : Fin d → ℤ) {a : ℝ} (ha : 0 ≤ a) :
    (∑ _y ∈ (Finset.univ : Finset (Fin d → Fin (M.N + 1))).filter
      (fun y => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i), a) ≤ a := by
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcardNat := M.matchingStates_card_le_one x ℓ
  have hcard : (((Finset.univ : Finset (Fin d → Fin (M.N + 1))).filter
      (fun y => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i)).card : ℝ) ≤ (1 : ℝ) := by
    exact_mod_cast hcardNat
  calc
    (((Finset.univ : Finset (Fin d → Fin (M.N + 1))).filter
      (fun y => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i)).card : ℝ) * a
        ≤ 1 * a := mul_le_mul_of_nonneg_right hcard ha
    _ = a := one_mul a

/-- Summing a constant over target states matching one fixed jump gives either
one copy of the constant if the jump is realizable from `x`, or zero otherwise. -/
theorem sum_matchingStates_const_eq_ite_exists
    (x : Fin d → Fin (M.N + 1)) (ℓ : Fin d → ℤ) (a : ℝ) :
    (∑ _y ∈ (Finset.univ : Finset (Fin d → Fin (M.N + 1))).filter
      (fun y => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i), a) =
      if ∃ y : Fin d → Fin (M.N + 1),
          ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i then a else 0 := by
  by_cases h : ∃ y : Fin d → Fin (M.N + 1),
      ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i
  · have hexists := h
    obtain ⟨y0, hy0⟩ := h
    rw [if_pos hexists]
    have hmem : y0 ∈ (Finset.univ : Finset (Fin d → Fin (M.N + 1))).filter
        (fun y => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ y0, hy0⟩
    refine Finset.sum_eq_single y0 ?_ ?_
    · intro z hz hzy
      have hzmatch : ∀ i, (z i : ℤ) - (x i : ℤ) = ℓ i :=
        (Finset.mem_filter.mp hz).2
      have hzy_eq : z = y0 := by
        ext i
        have hz_i := hzmatch i
        have hy_i := hy0 i
        have : (z i : ℤ) = (y0 i : ℤ) := by linarith
        exact Int.ofNat.inj this
      exact False.elim (hzy hzy_eq)
    · intro hy0not
      exact False.elim (hy0not hmem)
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro y hy
    have hy_match : ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i :=
      (Finset.mem_filter.mp hy).2
    exact False.elim (h ⟨y, hy_match⟩)

/-- Sharp total off-diagonal rate bound before removing impossible jumps:
the sum over all target states is bounded by the sum over jump vectors. -/
theorem sum_offDiagRate_le_rate_sum (x : Fin d → Fin (M.N + 1)) :
    (∑ y : Fin d → Fin (M.N + 1), M.offDiagRate x y) ≤
      (M.N : ℝ) * ∑ ℓ ∈ M.rateSpec.jumps,
        M.rateSpec.rate ℓ (M.scaledState x) := by
  let a : (Fin d → ℤ) → ℝ :=
    fun ℓ => (M.N : ℝ) * M.rateSpec.rate ℓ (M.scaledState x)
  have ha_nonneg : ∀ ℓ ∈ M.rateSpec.jumps, 0 ≤ a ℓ := by
    intro ℓ hℓ
    dsimp [a]
    apply mul_nonneg (Nat.cast_nonneg _)
    exact M.rateSpec.rate_nonneg ℓ hℓ (M.scaledState x) fun i =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hpoint : ∀ y : Fin d → Fin (M.N + 1),
      M.offDiagRate x y ≤ ∑ ℓ ∈ M.rateSpec.jumps.filter
        (fun ℓ => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i), a ℓ := by
    intro y
    by_cases hxy : x = y
    · rw [offDiagRate, if_pos hxy]
      exact Finset.sum_nonneg fun ℓ hℓ => ha_nonneg ℓ (Finset.mem_filter.mp hℓ).1
    · rw [offDiagRate, if_neg hxy]
      rfl
  calc
    ∑ y : Fin d → Fin (M.N + 1), M.offDiagRate x y
        ≤ ∑ y : Fin d → Fin (M.N + 1),
            ∑ ℓ ∈ M.rateSpec.jumps.filter
              (fun ℓ => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i), a ℓ := by
          exact Finset.sum_le_sum fun y _ => hpoint y
    _ = ∑ y : Fin d → Fin (M.N + 1),
            ∑ ℓ ∈ M.rateSpec.jumps,
              if (∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i) then a ℓ else 0 := by
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.sum_filter]
    _ = ∑ ℓ ∈ M.rateSpec.jumps,
            ∑ y : Fin d → Fin (M.N + 1),
              if (∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i) then a ℓ else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ ℓ ∈ M.rateSpec.jumps,
            ∑ y ∈ (Finset.univ : Finset (Fin d → Fin (M.N + 1))).filter
              (fun y => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i), a ℓ := by
          apply Finset.sum_congr rfl
          intro ℓ _
          rw [Finset.sum_filter]
    _ ≤ ∑ ℓ ∈ M.rateSpec.jumps, a ℓ := by
          apply Finset.sum_le_sum
          intro ℓ hℓ
          exact M.sum_matchingStates_const_le x ℓ (ha_nonneg ℓ hℓ)
    _ = (M.N : ℝ) * ∑ ℓ ∈ M.rateSpec.jumps,
        M.rateSpec.rate ℓ (M.scaledState x) := by
          simp [a, Finset.mul_sum]

/-- The total exit rate is `O(N)` with sharp constant equal to the sum of
listed density rates at the current scaled state. -/
theorem exitRateAt_le_rate_sum (x : Fin d → Fin (M.N + 1)) :
    M.exitRateAt x ≤
      (M.N : ℝ) * ∑ ℓ ∈ M.rateSpec.jumps,
        M.rateSpec.rate ℓ (M.scaledState x) := by
  have hoff_nonneg : ∀ y : Fin d → Fin (M.N + 1), 0 ≤ M.offDiagRate x y := by
    intro y
    by_cases hxy : x = y
    · rw [offDiagRate, if_pos hxy]
    · rw [offDiagRate, if_neg hxy]
      apply Finset.sum_nonneg
      intro ℓ hℓ
      apply mul_nonneg (Nat.cast_nonneg _)
      exact M.rateSpec.rate_nonneg ℓ (Finset.mem_filter.mp hℓ).1 (M.scaledState x) fun i =>
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc
    M.exitRateAt x
        = ∑ y ∈ Finset.univ.filter (· ≠ x), M.offDiagRate x y := by
          simp only [exitRateAt, QMatrix.exitRate, toQMatrix]
          apply Finset.sum_congr rfl
          intro y hy
          have hyx : x ≠ y := Ne.symm (Finset.mem_filter.mp hy).2
          simp [qMatrixRate, hyx]
    _ ≤ ∑ y : Fin d → Fin (M.N + 1), M.offDiagRate x y := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset (fun y => y ≠ x) Finset.univ)
            (by intro y _ hy_not; exact hoff_nonneg y)
    _ ≤ (M.N : ℝ) * ∑ ℓ ∈ M.rateSpec.jumps,
        M.rateSpec.rate ℓ (M.scaledState x) :=
          M.sum_offDiagRate_le_rate_sum x

/-- Uniform total exit-rate bound `exitRate(x) ≤ N*C` on the finite density
lattice. This is the rate-side input for the martingale QV estimate. -/
theorem exists_exitRateAt_bound :
    ∃ C > 0, ∀ x : Fin d → Fin (M.N + 1), M.exitRateAt x ≤ (M.N : ℝ) * C := by
  obtain ⟨B, hBpos, hB⟩ := M.rateSpec.exists_rate_bound_on_ball 1 zero_lt_one
  refine ⟨B * (M.rateSpec.jumps.card : ℝ) + 1, by positivity, ?_⟩
  intro x
  have hsum :
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
  calc
    M.exitRateAt x
        ≤ (M.N : ℝ) * ∑ ℓ ∈ M.rateSpec.jumps,
            M.rateSpec.rate ℓ (M.scaledState x) := M.exitRateAt_le_rate_sum x
    _ ≤ (M.N : ℝ) * ((M.rateSpec.jumps.card : ℝ) * B) := by
          gcongr
    _ = (M.N : ℝ) * (B * (M.rateSpec.jumps.card : ℝ)) := by ring
    _ ≤ (M.N : ℝ) * (B * (M.rateSpec.jumps.card : ℝ) + 1) := by
          gcongr
          linarith

/-- Rate-side quadratic-variation scale:
`total jump rate * (max scaled jump size)^2 = O(1/N)`.

This is deterministic. The stochastic QV theorem still has to connect it to the
canonical CTMC path law and martingale bracket. -/
theorem exists_qvRate_bound :
    ∃ C > 0, ∀ x : Fin d → Fin (M.N + 1),
      M.exitRateAt x * (M.rateSpec.jumpNormBound / (M.N : ℝ)) ^ 2 ≤
        C / (M.N : ℝ) := by
  obtain ⟨C₀, hC₀pos, hExit⟩ := M.exists_exitRateAt_bound
  refine ⟨C₀ * M.rateSpec.jumpNormBound ^ 2 + 1, by positivity, ?_⟩
  intro x
  have hNpos : 0 < (M.N : ℝ) := Nat.cast_pos.mpr M.hN
  have hsq_nonneg : 0 ≤ (M.rateSpec.jumpNormBound / (M.N : ℝ)) ^ 2 := sq_nonneg _
  calc
    M.exitRateAt x * (M.rateSpec.jumpNormBound / (M.N : ℝ)) ^ 2
        ≤ ((M.N : ℝ) * C₀) * (M.rateSpec.jumpNormBound / (M.N : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_right (hExit x) hsq_nonneg
    _ = C₀ * M.rateSpec.jumpNormBound ^ 2 / (M.N : ℝ) := by
          field_simp [ne_of_gt hNpos]
    _ ≤ (C₀ * M.rateSpec.jumpNormBound ^ 2 + 1) / (M.N : ℝ) := by
          gcongr
          linarith

/-- Single-target contribution to the generator-side quadratic variation is
bounded by the corresponding listed jump contributions. -/
theorem offDiagRate_mul_scaledState_sub_sq_le (x y : Fin d → Fin (M.N + 1)) :
    M.offDiagRate x y * ‖M.scaledState y - M.scaledState x‖ ^ 2 ≤
      ∑ ℓ ∈ M.rateSpec.jumps.filter
        (fun ℓ : Fin d → ℤ => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i),
          ((M.N : ℝ) * M.rateSpec.rate ℓ (M.scaledState x)) *
            (M.rateSpec.jumpNormBound / (M.N : ℝ)) ^ 2 := by
  let b := (M.rateSpec.jumpNormBound / (M.N : ℝ)) ^ 2
  let a : (Fin d → ℤ) → ℝ :=
    fun ℓ => (M.N : ℝ) * M.rateSpec.rate ℓ (M.scaledState x)
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    exact sq_nonneg _
  have ha_nonneg : ∀ ℓ ∈ M.rateSpec.jumps, 0 ≤ a ℓ := by
    intro ℓ hℓ
    dsimp [a]
    apply mul_nonneg (Nat.cast_nonneg _)
    exact M.rateSpec.rate_nonneg ℓ hℓ (M.scaledState x) fun i =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  by_cases hxy : x = y
  · rw [offDiagRate, if_pos hxy]
    simp only [zero_mul]
    change 0 ≤ ∑ ℓ ∈ M.rateSpec.jumps.filter
      (fun q : Fin d → ℤ => ∀ i, (y i : ℤ) - (x i : ℤ) = q i), a ℓ * b
    exact Finset.sum_nonneg fun (ℓ : Fin d → ℤ) hℓ => by
      have hℓmem : ℓ ∈ M.rateSpec.jumps :=
        Finset.filter_subset
          (s := M.rateSpec.jumps)
          (p := fun q : Fin d → ℤ => ∀ i, (y i : ℤ) - (x i : ℤ) = q i)
          hℓ
      exact mul_nonneg (ha_nonneg ℓ hℓmem) hb_nonneg
  · rw [offDiagRate, if_neg hxy]
    calc
      (∑ ℓ ∈ M.rateSpec.jumps.filter
          (fun ℓ : Fin d → ℤ => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i),
          (M.N : ℝ) * M.rateSpec.rate ℓ
            (fun i => (x i : ℝ) / (M.N : ℝ))) *
          ‖M.scaledState y - M.scaledState x‖ ^ 2
        = (∑ ℓ ∈ M.rateSpec.jumps.filter
            (fun ℓ : Fin d → ℤ => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i), a ℓ) *
            ‖M.scaledState y - M.scaledState x‖ ^ 2 := by
          rfl
      _ = ∑ ℓ ∈ M.rateSpec.jumps.filter
            (fun ℓ : Fin d → ℤ => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i),
            a ℓ * ‖M.scaledState y - M.scaledState x‖ ^ 2 := by
          rw [Finset.sum_mul]
      _ ≤ ∑ ℓ ∈ M.rateSpec.jumps.filter
            (fun ℓ : Fin d → ℤ => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i), a ℓ * b := by
          apply Finset.sum_le_sum
          intro ℓ hℓ
          have hmem : ℓ ∈ M.rateSpec.jumps := (Finset.mem_filter.mp hℓ).1
          have hmatch :
              ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i :=
            (Finset.mem_filter.mp hℓ).2
          have hnorm := M.scaledState_jump_norm_le_bound hmem hmatch
          have hbroot_nonneg :
              0 ≤ M.rateSpec.jumpNormBound / (M.N : ℝ) := by
            exact div_nonneg M.rateSpec.jumpNormBound_nonneg (Nat.cast_nonneg _)
          have hnormsq :
              ‖M.scaledState y - M.scaledState x‖ ^ 2 ≤ b := by
            dsimp [b]
            nlinarith [hnorm, norm_nonneg (M.scaledState y - M.scaledState x),
              hbroot_nonneg]
          exact mul_le_mul_of_nonneg_left hnormsq (ha_nonneg ℓ hmem)
      _ = ∑ ℓ ∈ M.rateSpec.jumps.filter
            (fun ℓ : Fin d → ℤ => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i),
            ((M.N : ℝ) * M.rateSpec.rate ℓ (M.scaledState x)) *
              (M.rateSpec.jumpNormBound / (M.N : ℝ)) ^ 2 := by
          simp only [a, b]

/-- A single target state's first-moment generator contribution can be
rewritten as a sum over the listed jump vectors that realize that target. -/
theorem offDiagRate_mul_scaledState_sub_apply_eq_sum_jumps
    (x y : Fin d → Fin (M.N + 1)) (i : Fin d) :
    M.offDiagRate x y * (M.scaledState y - M.scaledState x) i =
      ∑ ℓ ∈ M.rateSpec.jumps.filter
        (fun ℓ : Fin d → ℤ => ∀ j, (y j : ℤ) - (x j : ℤ) = ℓ j),
        (ℓ i : ℝ) * M.rateSpec.rate ℓ (M.scaledState x) := by
  by_cases hxy : x = y
  · rw [offDiagRate, if_pos hxy]
    simp only [zero_mul]
    refine (Finset.sum_eq_zero ?_).symm
    intro ℓ hℓ
    have hmatch : ∀ j, (y j : ℤ) - (x j : ℤ) = ℓ j :=
      (Finset.mem_filter.mp hℓ).2
    have hi : ℓ i = 0 := by
      have := hmatch i
      subst y
      simpa using this.symm
    simp [hi]
  · rw [offDiagRate, if_neg hxy]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    have hmatch : ∀ j, (y j : ℤ) - (x j : ℤ) = ℓ j :=
      (Finset.mem_filter.mp hℓ).2
    have hscaled := congr_fun (M.scaledState_sub_eq_of_jump hmatch) i
    simp only [Pi.sub_apply] at hscaled
    change (↑M.N * M.rateSpec.rate ℓ (fun i => ↑↑(x i) / ↑M.N)) *
        (M.scaledState y i - M.scaledState x i) =
      ↑(ℓ i) * M.rateSpec.rate ℓ (M.scaledState x)
    rw [hscaled]
    change (↑M.N * M.rateSpec.rate ℓ (M.scaledState x)) * (↑(ℓ i) / ↑M.N) =
      ↑(ℓ i) * M.rateSpec.rate ℓ (M.scaledState x)
    have hNpos : (M.N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt M.hN
    field_simp [hNpos]

/-- Generator-side instantaneous quadratic-variation rate for the scaled
density process at population state `x`. -/
noncomputable def instantQVRate (x : Fin d → Fin (M.N + 1)) : ℝ :=
  ∑ y : Fin d → Fin (M.N + 1),
    M.offDiagRate x y * ‖M.scaledState y - M.scaledState x‖ ^ 2

/-- Generator-side coordinate instantaneous quadratic-variation rate. -/
noncomputable def instantCoordQVRate (x : Fin d → Fin (M.N + 1)) (i : Fin d) : ℝ :=
  ∑ y : Fin d → Fin (M.N + 1),
    M.offDiagRate x y * ((M.scaledState y - M.scaledState x) i) ^ 2

/-- The actual generator drift of the finite lattice CTMC.  This is the
compensator drift induced by the realizable off-diagonal transitions.  It can
differ from `rateSpec.drift (scaledState x)` at boundaries unless impossible
jumps have zero rate. -/
noncomputable def generatorDrift (x : Fin d → Fin (M.N + 1)) : Fin d → ℝ :=
  fun i => ∑ y : Fin d → Fin (M.N + 1),
    M.offDiagRate x y * (M.scaledState y - M.scaledState x) i

/-- Boundary compatibility for the finite lattice: any listed jump that cannot
be realized from a lattice state has zero rate at that state's density.  This
is what aligns the finite-lattice generator compensator with the abstract
mean-field drift at boundary states. -/
def BoundaryCompatible : Prop :=
  ∀ (x : Fin d → Fin (M.N + 1)) (ℓ : Fin d → ℤ), ℓ ∈ M.rateSpec.jumps →
    ¬ (∃ y : Fin d → Fin (M.N + 1), ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i) →
      M.rateSpec.rate ℓ (M.scaledState x) = 0

/-- Simplex-local boundary compatibility.  This is the version needed for
population protocols when the finite CTMC is encoded on the ambient cube but
canonical paths are proved to stay in the total-population simplex. -/
def BoundaryCompatibleOnSimplex : Prop :=
  ∀ (x : Fin d → Fin (M.N + 1)), M.InSimplex x →
    ∀ (ℓ : Fin d → ℤ), ℓ ∈ M.rateSpec.jumps →
      ¬ (∃ y : Fin d → Fin (M.N + 1), ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i) →
        M.rateSpec.rate ℓ (M.scaledState x) = 0

/-- The instantaneous quadratic-variation rate is non-negative. -/
theorem instantQVRate_nonneg (x : Fin d → Fin (M.N + 1)) :
    0 ≤ M.instantQVRate x := by
  simp only [instantQVRate]
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg (M.offDiagRate_nonneg x y)
    (sq_nonneg ‖M.scaledState y - M.scaledState x‖)

/-- Coordinate instantaneous QV rates are non-negative. -/
theorem instantCoordQVRate_nonneg (x : Fin d → Fin (M.N + 1)) (i : Fin d) :
    0 ≤ M.instantCoordQVRate x i := by
  simp only [instantCoordQVRate]
  exact Finset.sum_nonneg fun y _ =>
    mul_nonneg (M.offDiagRate_nonneg x y) (sq_nonneg _)

/-- Each coordinate instantaneous QV rate is bounded by the vector
instantaneous QV rate. -/
theorem instantCoordQVRate_le_instantQVRate
    (x : Fin d → Fin (M.N + 1)) (i : Fin d) :
    M.instantCoordQVRate x i ≤ M.instantQVRate x := by
  simp only [instantCoordQVRate, instantQVRate]
  refine Finset.sum_le_sum ?_
  intro y _
  have hcoord :
      ((M.scaledState y - M.scaledState x) i) ^ 2 ≤
        ‖M.scaledState y - M.scaledState x‖ ^ 2 := by
    have hle :
        |(M.scaledState y - M.scaledState x) i| ≤
          ‖M.scaledState y - M.scaledState x‖ := by
      simpa [Real.norm_eq_abs] using
        norm_le_pi_norm (M.scaledState y - M.scaledState x) i
    rw [← sq_abs]
    nlinarith [norm_nonneg (M.scaledState y - M.scaledState x),
      abs_nonneg ((M.scaledState y - M.scaledState x) i)]
  exact mul_le_mul_of_nonneg_left hcoord (M.offDiagRate_nonneg x y)

/-- The sum of coordinate instantaneous-QV rates is bounded by `d` times the
vector instantaneous-QV rate. -/
theorem sum_instantCoordQVRate_le_card_mul_instantQVRate
    (x : Fin d → Fin (M.N + 1)) :
    (∑ i : Fin d, M.instantCoordQVRate x i) ≤
      (Fintype.card (Fin d) : ℝ) * M.instantQVRate x := by
  calc
    (∑ i : Fin d, M.instantCoordQVRate x i)
        ≤ ∑ _i : Fin d, M.instantQVRate x := by
          exact Finset.sum_le_sum fun i _ => M.instantCoordQVRate_le_instantQVRate x i
    _ = (Fintype.card (Fin d) : ℝ) * M.instantQVRate x := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The unfiltered sum of off-diagonal rates equals the exit rate, because the
diagonal term is zero by convention. -/
theorem sum_offDiagRate_eq_exitRateAt (x : Fin d → Fin (M.N + 1)) :
    ∑ y, M.offDiagRate x y = M.exitRateAt x := by
  have h0 : M.offDiagRate x x = 0 := if_pos rfl
  calc ∑ y, M.offDiagRate x y
      = M.offDiagRate x x + ∑ y ∈ Finset.univ.erase x, M.offDiagRate x y :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ x)).symm
    _ = ∑ y ∈ Finset.univ.erase x, M.offDiagRate x y := by rw [h0, zero_add]
    _ = M.exitRateAt x := by
        rw [exitRateAt, QMatrix.exitRate, ← Finset.filter_ne' Finset.univ x]
        exact Finset.sum_congr rfl fun y hy => by
          have hne : y ≠ x := (Finset.mem_filter.mp hy).2
          simp [toQMatrix, qMatrixRate, Ne.symm hne]

/-- Cauchy-Schwarz for generator drift and coordinate QV rate:
`drift_i(x)² ≤ exitRate(x) · QVRate_i(x)`.  This is the pointwise algebraic
core of the holding-time residual bound in the Kurtz bridge. -/
theorem generatorDrift_sq_le_exitRateAt_mul_instantCoordQVRate
    (x : Fin d → Fin (M.N + 1)) (i : Fin d) :
    M.generatorDrift x i ^ 2 ≤ M.exitRateAt x * M.instantCoordQVRate x i := by
  let δ : (Fin d → Fin (M.N + 1)) → ℝ := fun y => (M.scaledState y - M.scaledState x) i
  have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
    (r := fun y => M.offDiagRate x y * δ y)
    (f := fun y => M.offDiagRate x y)
    (g := fun y => M.offDiagRate x y * (δ y) ^ 2)
    (fun y _ => M.offDiagRate_nonneg x y)
    (fun y _ => mul_nonneg (M.offDiagRate_nonneg x y) (sq_nonneg _))
    (fun y _ => by ring)
  simp only [generatorDrift, instantCoordQVRate, δ] at hCS ⊢
  calc (∑ y, M.offDiagRate x y * (M.scaledState y - M.scaledState x) i) ^ 2
      ≤ (∑ y, M.offDiagRate x y) *
          ∑ y, M.offDiagRate x y * ((M.scaledState y - M.scaledState x) i) ^ 2 := hCS
    _ = M.exitRateAt x *
          ∑ y, M.offDiagRate x y * ((M.scaledState y - M.scaledState x) i) ^ 2 := by
        rw [M.sum_offDiagRate_eq_exitRateAt x]

/-- Under positive exit rate, the normalized drift squared is bounded by the
coordinate QV rate. -/
theorem generatorDrift_sq_div_exitRateAt_le_instantCoordQVRate
    (x : Fin d → Fin (M.N + 1)) (i : Fin d)
    (hpos : 0 < M.exitRateAt x) :
    M.generatorDrift x i ^ 2 / M.exitRateAt x ≤ M.instantCoordQVRate x i := by
  rw [div_le_iff₀ hpos]
  simpa [mul_comm] using M.generatorDrift_sq_le_exitRateAt_mul_instantCoordQVRate x i

/-- Under `NoAbsorbing`, the normalized drift squared at any coordinate is
bounded by the coordinate QV rate. -/
theorem generatorDrift_sq_div_exitRateAt_le_instantCoordQVRate_of_noAbsorbing
    (hNA : M.NoAbsorbing) (x : Fin d → Fin (M.N + 1)) (i : Fin d) :
    M.generatorDrift x i ^ 2 / M.exitRateAt x ≤ M.instantCoordQVRate x i :=
  M.generatorDrift_sq_div_exitRateAt_le_instantCoordQVRate x i
    (M.exitRateAt_pos_of_noAbsorbing hNA x)

/-- One-step embedded-chain first moment per unit exit rate equals the actual
finite-lattice generator drift. -/
theorem exitRateAt_mul_integral_embeddedStepMeasure_scaledState_sub
    (x : Fin d → Fin (M.N + 1)) (h : ¬M.toQMatrix.IsAbsorbing x) (i : Fin d) :
    M.exitRateAt x *
      (∫ y, (M.scaledState y - M.scaledState x) i
        ∂M.toQMatrix.embeddedStepMeasure x) =
    M.generatorDrift x i := by
  let f : (Fin d → Fin (M.N + 1)) → ℝ :=
    fun y => (M.scaledState y - M.scaledState x) i
  have hsum := M.toQMatrix.exitRate_mul_integral_embeddedStepMeasure_eq_sum_rate h f
  rw [exitRateAt]
  rw [hsum]
  simp only [generatorDrift]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _hy
  by_cases hyx : y ≠ x
  · have hxy : x ≠ y := Ne.symm hyx
    rw [if_pos hyx]
    simp only [toQMatrix, qMatrixRate, if_neg hxy]
    rfl
  · rw [if_neg hyx]
    have hxy : x = y := (not_ne_iff.mp hyx).symm
    subst y
    simp [offDiagRate]

/-- One-step embedded-chain coordinate second moment per unit exit rate equals
the coordinate instantaneous QV rate. -/
theorem exitRateAt_mul_integral_embeddedStepMeasure_scaledState_sub_apply_sq
    (x : Fin d → Fin (M.N + 1)) (h : ¬M.toQMatrix.IsAbsorbing x) (i : Fin d) :
    M.exitRateAt x *
      (∫ y, ((M.scaledState y - M.scaledState x) i) ^ 2
        ∂M.toQMatrix.embeddedStepMeasure x) =
    M.instantCoordQVRate x i := by
  let f : (Fin d → Fin (M.N + 1)) → ℝ :=
    fun y => ((M.scaledState y - M.scaledState x) i) ^ 2
  have hsum := M.toQMatrix.exitRate_mul_integral_embeddedStepMeasure_eq_sum_rate h f
  rw [exitRateAt]
  rw [hsum]
  simp only [instantCoordQVRate]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _hy
  by_cases hyx : y ≠ x
  · have hxy : x ≠ y := Ne.symm hyx
    rw [if_pos hyx]
    simp only [toQMatrix, qMatrixRate, if_neg hxy]
    rfl
  · rw [if_neg hyx]
    have hxy : x = y := (not_ne_iff.mp hyx).symm
    subst y
    simp [offDiagRate]

/-- Under `NoAbsorbing`, integrating the next coordinate jump against the
canonical conditional next-state law is the same as integrating against the
embedded jump-chain row from the finite history state. -/
theorem integral_condDistrib_next_state_scaledState_sub_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (n : ℕ) (i : Fin d) :
    ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
      (∫ y, (M.scaledState y -
            M.scaledState
              (QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) n hist)) i
          ∂ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => (records (n + 1)).2)
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist) =
        ∫ y, (M.scaledState y -
            M.scaledState
              (QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) n hist)) i
          ∂M.toQMatrix.embeddedStepMeasure
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n hist) := by
  filter_upwards
    [M.condDistrib_canonicalRecordMeasure_next_state_of_noAbsorbing x₀ hNA n]
    with hist hcond
  rw [hcond]

/-- First conditional-moment identity, still indexed by finite record history:
the embedded-row first moment times the exit rate is the actual generator
drift. -/
theorem exitRateAt_mul_integral_condDistrib_next_state_scaledState_sub_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (n : ℕ) (i : Fin d) :
    ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
      M.exitRateAt
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n hist) *
        (∫ y, (M.scaledState y -
              M.scaledState
                (QMatrix.currentStateFromHistory
                  (S := Fin d → Fin (M.N + 1)) n hist)) i
            ∂ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).2)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist) =
          M.generatorDrift
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n hist) i := by
  filter_upwards
    [M.integral_condDistrib_next_state_scaledState_sub_of_noAbsorbing
      x₀ hNA n i]
    with hist hcond
  rw [hcond]
  exact M.exitRateAt_mul_integral_embeddedStepMeasure_scaledState_sub
    (QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n hist)
    (hNA _)
    i

/-- Under `NoAbsorbing`, integrating the next squared coordinate jump against
the canonical conditional next-state law is the same as integrating against the
embedded jump-chain row from the finite history state. -/
theorem integral_condDistrib_next_state_scaledState_sub_apply_sq_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (n : ℕ) (i : Fin d) :
    ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
      (∫ y, ((M.scaledState y -
            M.scaledState
              (QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) n hist)) i) ^ 2
          ∂ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => (records (n + 1)).2)
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist) =
        ∫ y, ((M.scaledState y -
            M.scaledState
              (QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) n hist)) i) ^ 2
          ∂M.toQMatrix.embeddedStepMeasure
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n hist) := by
  filter_upwards
    [M.condDistrib_canonicalRecordMeasure_next_state_of_noAbsorbing x₀ hNA n]
    with hist hcond
  rw [hcond]

/-- Second conditional-moment identity, still indexed by finite record history:
the embedded-row coordinate second moment times the exit rate is the coordinate
instantaneous QV rate. -/
theorem exitRateAt_mul_integral_condDistrib_next_state_scaledState_sub_apply_sq_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (n : ℕ) (i : Fin d) :
    ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
      M.exitRateAt
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n hist) *
        (∫ y, ((M.scaledState y -
              M.scaledState
                (QMatrix.currentStateFromHistory
                  (S := Fin d → Fin (M.N + 1)) n hist)) i) ^ 2
            ∂ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).2)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist) =
          M.instantCoordQVRate
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n hist) i := by
  filter_upwards
    [M.integral_condDistrib_next_state_scaledState_sub_apply_sq_of_noAbsorbing
      x₀ hNA n i]
    with hist hcond
  rw [hcond]
  exact M.exitRateAt_mul_integral_embeddedStepMeasure_scaledState_sub_apply_sq
    (QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n hist)
    (hNA _)
    i

/-- Canonical-record a.e. first conditional-moment identity for the next
coordinate jump.  This is the direct martingale-increment compensator form,
conditioned on the finite record history through `n`. -/
theorem exitRateAt_mul_condExp_next_scaledState_sub_apply_eq_generatorDrift_ae_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (n : ℕ) (i : Fin d) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      M.exitRateAt ((M.canonicalPathMap records).stateSeq n) *
        (M.canonicalRecordMeasure x₀)[
          fun records : M.canonicalRecordΩ =>
            (M.scaledState ((records (n + 1)).2) -
              M.scaledState ((M.canonicalPathMap records).stateSeq n)) i
          | MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance] records =
        M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i := by
  have hcond :=
    M.condExp_next_scaledState_sub_apply_eq_integral_condDistrib x₀ n i
  have hhist :=
    M.exitRateAt_mul_integral_condDistrib_next_state_scaledState_sub_of_noAbsorbing
      x₀ hNA n i
  have hrecords :
      ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
        M.exitRateAt
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) *
          (∫ y, (M.scaledState y -
                M.scaledState
                  (QMatrix.currentStateFromHistory
                    (S := Fin d → Fin (M.N + 1)) n
                    (Preorder.frestrictLe n records))) i
              ∂ProbabilityTheory.condDistrib
                (fun records : M.canonicalRecordΩ => (records (n + 1)).2)
                (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀)
                (Preorder.frestrictLe n records)) =
            M.generatorDrift
              (QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) i :=
    MeasureTheory.ae_of_ae_map (Preorder.measurable_frestrictLe n).aemeasurable hhist
  filter_upwards [hcond, hrecords] with records hce hmom
  rw [hce]
  simpa [canonicalPathMap, QMatrix.currentStateFromHistory_frestrictLe] using hmom

/-- Canonical-record a.e. second conditional-moment identity for the squared
next coordinate jump.  This is the direct coordinate bracket-compensator form,
conditioned on the finite record history through `n`. -/
theorem exitRateAt_mul_condExp_next_scaledState_sub_apply_sq_eq_instantCoordQVRate_ae_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (n : ℕ) (i : Fin d) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      M.exitRateAt ((M.canonicalPathMap records).stateSeq n) *
        (M.canonicalRecordMeasure x₀)[
          fun records : M.canonicalRecordΩ =>
            ((M.scaledState ((records (n + 1)).2) -
              M.scaledState ((M.canonicalPathMap records).stateSeq n)) i) ^ 2
          | MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance] records =
        M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq n) i := by
  have hcond :=
    M.condExp_next_scaledState_sub_apply_sq_eq_integral_condDistrib x₀ n i
  have hhist :=
    M.exitRateAt_mul_integral_condDistrib_next_state_scaledState_sub_apply_sq_of_noAbsorbing
      x₀ hNA n i
  have hrecords :
      ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
        M.exitRateAt
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) *
          (∫ y, ((M.scaledState y -
                M.scaledState
                  (QMatrix.currentStateFromHistory
                    (S := Fin d → Fin (M.N + 1)) n
                    (Preorder.frestrictLe n records))) i) ^ 2
              ∂ProbabilityTheory.condDistrib
                (fun records : M.canonicalRecordΩ => (records (n + 1)).2)
                (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀)
                (Preorder.frestrictLe n records)) =
            M.instantCoordQVRate
              (QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) i :=
    MeasureTheory.ae_of_ae_map (Preorder.measurable_frestrictLe n).aemeasurable hhist
  filter_upwards [hcond, hrecords] with records hce hmom
  rw [hce]
  simpa [canonicalPathMap, QMatrix.currentStateFromHistory_frestrictLe] using hmom

/-- Division form of the first conditional-moment identity: the conditional
expectation of the next coordinate jump is the generator drift divided by the
current exit rate. -/
theorem condExp_next_scaledState_sub_apply_eq_generatorDrift_div_exitRate_ae_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (n : ℕ) (i : Fin d) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      (M.canonicalRecordMeasure x₀)[
        fun records : M.canonicalRecordΩ =>
          (M.scaledState ((records (n + 1)).2) -
            M.scaledState ((M.canonicalPathMap records).stateSeq n)) i
        | MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance] records =
        M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i /
          M.exitRateAt ((M.canonicalPathMap records).stateSeq n) := by
  filter_upwards
    [M.exitRateAt_mul_condExp_next_scaledState_sub_apply_eq_generatorDrift_ae_of_noAbsorbing
      x₀ hNA n i]
    with records hmul
  let a := M.exitRateAt ((M.canonicalPathMap records).stateSeq n)
  let ce :=
    (M.canonicalRecordMeasure x₀)[
      fun records : M.canonicalRecordΩ =>
        (M.scaledState ((records (n + 1)).2) -
          M.scaledState ((M.canonicalPathMap records).stateSeq n)) i
      | MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance] records
  let gd := M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i
  have ha : a ≠ 0 := ne_of_gt
    (M.exitRateAt_pos_of_noAbsorbing hNA ((M.canonicalPathMap records).stateSeq n))
  have hmul' : a * ce = gd := by simpa [a, ce, gd] using hmul
  calc
    ce = (a * ce) / a := by field_simp [ha]
    _ = gd / a := by rw [hmul']

/-- Division form of the second conditional-moment identity: the conditional
expectation of the squared next coordinate jump is the coordinate QV rate
divided by the current exit rate. -/
theorem condExp_next_scaledState_sub_apply_sq_eq_instantCoordQVRate_div_exitRate_ae_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (n : ℕ) (i : Fin d) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      (M.canonicalRecordMeasure x₀)[
        fun records : M.canonicalRecordΩ =>
          ((M.scaledState ((records (n + 1)).2) -
            M.scaledState ((M.canonicalPathMap records).stateSeq n)) i) ^ 2
        | MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance] records =
        M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq n) i /
          M.exitRateAt ((M.canonicalPathMap records).stateSeq n) := by
  filter_upwards
    [M.exitRateAt_mul_condExp_next_scaledState_sub_apply_sq_eq_instantCoordQVRate_ae_of_noAbsorbing
      x₀ hNA n i]
    with records hmul
  let a := M.exitRateAt ((M.canonicalPathMap records).stateSeq n)
  let ce :=
    (M.canonicalRecordMeasure x₀)[
      fun records : M.canonicalRecordΩ =>
        ((M.scaledState ((records (n + 1)).2) -
          M.scaledState ((M.canonicalPathMap records).stateSeq n)) i) ^ 2
      | MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance] records
  let qv := M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq n) i
  have ha : a ≠ 0 := ne_of_gt
    (M.exitRateAt_pos_of_noAbsorbing hNA ((M.canonicalPathMap records).stateSeq n))
  have hmul' : a * ce = qv := by simpa [a, ce, qv] using hmul
  calc
    ce = (a * ce) / a := by field_simp [ha]
    _ = qv / a := by rw [hmul']

/-! ## Discrete jump-index compensators -/

/-- Drift compensator for one coordinate along the embedded jump index.  The
summand is the conditional mean of the next scaled coordinate jump. -/
noncomputable def scaledJumpDriftCompensator
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    M.generatorDrift (path.stateSeq k) i / M.exitRateAt (path.stateSeq k)

/-- Completed-holding-time residual for one coordinate along the embedded jump
index.  It is the predictable drift compensator minus the clock time spent in
the completed sojourns. -/
noncomputable def scaledHoldingTimeDriftResidual
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    M.generatorDrift (path.stateSeq k) i *
      ((M.exitRateAt (path.stateSeq k))⁻¹ - path.sojournTime k)

/-- Coordinate QV compensator along the embedded jump index.  The summand is
the conditional second moment of the next scaled coordinate jump. -/
noncomputable def scaledCoordQVCompensator
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    M.instantCoordQVRate (path.stateSeq k) i / M.exitRateAt (path.stateSeq k)

/-- Vector QV compensator along the embedded jump index, using the
generator-side instantaneous vector QV rate. -/
noncomputable def scaledQVCompensator
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    M.instantQVRate (path.stateSeq k) / M.exitRateAt (path.stateSeq k)

/-- Centered coordinate jump-sum process along the embedded jump index. -/
noncomputable def scaledJumpMartingale
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) : ℝ :=
  M.scaledJumpSum path n i - M.scaledJumpDriftCompensator path i n

/-- Centered coordinate squared-jump sum along the embedded jump index. -/
noncomputable def scaledCoordJumpSqMartingale
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) : ℝ :=
  M.scaledCoordJumpSqSum path i n - M.scaledCoordQVCompensator path i n

@[simp]
theorem scaledJumpDriftCompensator_zero
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) :
    M.scaledJumpDriftCompensator path i 0 = 0 := by
  simp [scaledJumpDriftCompensator]

@[simp]
theorem scaledHoldingTimeDriftResidual_zero
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) :
    M.scaledHoldingTimeDriftResidual path i 0 = 0 := by
  simp [scaledHoldingTimeDriftResidual]

/-- Pathwise bridge from the embedded drift compensator to clock time: the
difference between the jump-index drift compensator sampled at `jumpCount t`
and the actual clock integral is the completed holding-time residual minus the
current partial-sojourn drift contribution. -/
theorem scaledJumpDriftCompensator_sub_integral_eq_scaledHoldingTimeDriftResidual_sub_current
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) (i : Fin d) {t : ℝ} (ht : 0 ≤ t)
    (hfuture : ∃ n, t < path.times n)
    (hf_int : IntegrableOn
      (fun s => M.generatorDrift (path.stateAt s) i)
      (Set.Icc (0 : ℝ) t) volume) :
    M.scaledJumpDriftCompensator path i (path.jumpCount t) -
        ∫ s in Set.Icc (0:ℝ) t, M.generatorDrift (path.stateAt s) i =
      M.scaledHoldingTimeDriftResidual path i (path.jumpCount t) -
        M.generatorDrift (path.stateSeq (path.jumpCount t)) i *
          path.currentSojournElapsed t := by
  have hclock :=
    path.sum_sojournTime_mul_add_currentSojourn_eq_setIntegral_Icc
      hstrict hpos (fun x => M.generatorDrift x i) ht hfuture hf_int
  rw [← hclock]
  simp only [scaledJumpDriftCompensator, scaledHoldingTimeDriftResidual,
    div_eq_mul_inv]
  have hsum :
      (∑ x ∈ Finset.range (path.jumpCount t),
          M.generatorDrift (path.stateSeq x) i *
            (M.exitRateAt (path.stateSeq x))⁻¹) -
        (∑ x ∈ Finset.range (path.jumpCount t),
          M.generatorDrift (path.stateSeq x) i * path.sojournTime x) =
        ∑ x ∈ Finset.range (path.jumpCount t),
          M.generatorDrift (path.stateSeq x) i *
            ((M.exitRateAt (path.stateSeq x))⁻¹ - path.sojournTime x) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro x _hx
    ring
  rw [← hsum]
  ring

@[simp]
theorem scaledCoordQVCompensator_zero
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) :
    M.scaledCoordQVCompensator path i 0 = 0 := by
  simp [scaledCoordQVCompensator]

@[simp]
theorem scaledQVCompensator_zero
    (path : CTMCPath (Fin d → Fin (M.N + 1))) :
    M.scaledQVCompensator path 0 = 0 := by
  simp [scaledQVCompensator]

/-- Coordinate QV compensators are non-negative under `NoAbsorbing`, since
each embedded jump denominator is a strictly positive exit rate. -/
theorem scaledCoordQVCompensator_nonneg_of_noAbsorbing
    (hNA : M.NoAbsorbing)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) :
    0 ≤ M.scaledCoordQVCompensator path i n := by
  simp only [scaledCoordQVCompensator]
  exact Finset.sum_nonneg fun k _ =>
    div_nonneg (M.instantCoordQVRate_nonneg (path.stateSeq k) i)
      (le_of_lt (M.exitRateAt_pos_of_noAbsorbing hNA (path.stateSeq k)))

/-- Vector QV compensators are non-negative under `NoAbsorbing`. -/
theorem scaledQVCompensator_nonneg_of_noAbsorbing
    (hNA : M.NoAbsorbing)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (n : ℕ) :
    0 ≤ M.scaledQVCompensator path n := by
  simp only [scaledQVCompensator]
  exact Finset.sum_nonneg fun k _ =>
    div_nonneg (M.instantQVRate_nonneg (path.stateSeq k))
      (le_of_lt (M.exitRateAt_pos_of_noAbsorbing hNA (path.stateSeq k)))

/-- One-step recursion for the coordinate QV compensator. -/
theorem scaledCoordQVCompensator_succ
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) :
    M.scaledCoordQVCompensator path i (n + 1) =
      M.scaledCoordQVCompensator path i n +
        M.instantCoordQVRate (path.stateSeq n) i / M.exitRateAt (path.stateSeq n) := by
  simp [scaledCoordQVCompensator, Finset.sum_range_succ]

/-- One-step recursion for the completed holding-time drift residual. -/
theorem scaledHoldingTimeDriftResidual_succ
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) :
    M.scaledHoldingTimeDriftResidual path i (n + 1) =
      M.scaledHoldingTimeDriftResidual path i n +
        M.generatorDrift (path.stateSeq n) i *
          ((M.exitRateAt (path.stateSeq n))⁻¹ - path.sojournTime n) := by
  simp [scaledHoldingTimeDriftResidual, Finset.sum_range_succ]

/-- One-step increment of the completed holding-time drift residual. -/
theorem scaledHoldingTimeDriftResidual_succ_sub
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) :
    M.scaledHoldingTimeDriftResidual path i (n + 1) -
        M.scaledHoldingTimeDriftResidual path i n =
      M.generatorDrift (path.stateSeq n) i *
        ((M.exitRateAt (path.stateSeq n))⁻¹ - path.sojournTime n) := by
  rw [M.scaledHoldingTimeDriftResidual_succ]
  ring

/-- Coordinate QV compensators are monotone in the jump index under
`NoAbsorbing`. -/
theorem scaledCoordQVCompensator_mono_of_noAbsorbing
    (hNA : M.NoAbsorbing)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) {m n : ℕ}
    (hmn : m ≤ n) :
    M.scaledCoordQVCompensator path i m ≤ M.scaledCoordQVCompensator path i n := by
  simp only [scaledCoordQVCompensator]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by
      intro k hk
      exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hmn))
    (fun k _ _ =>
      div_nonneg (M.instantCoordQVRate_nonneg (path.stateSeq k) i)
        (le_of_lt (M.exitRateAt_pos_of_noAbsorbing hNA (path.stateSeq k))))

/-- Coordinate QV compensators sampled at `jumpCount` are monotone in clock time
on non-explosive paths. -/
theorem scaledCoordQVCompensator_jumpCount_mono_of_noAbsorbing
    (hNA : M.NoAbsorbing)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d)
    (hne : path.NonExplosive)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    {s t : ℝ} (hst : s ≤ t) :
    M.scaledCoordQVCompensator path i (path.jumpCount s) ≤
      M.scaledCoordQVCompensator path i (path.jumpCount t) := by
  have hs_future : ∃ n, s < path.times n := path.exists_bound_of_nonExplosive hne s
  have ht_future : ∃ n, t < path.times n := path.exists_bound_of_nonExplosive hne t
  exact M.scaledCoordQVCompensator_mono_of_noAbsorbing hNA path i
    (path.jumpCount_mono hstrict hst hs_future ht_future)

/-- The sum of `drift_i²/λ²` along the jump chain is bounded by the coordinate
QV compensator.  This follows from the pointwise Jensen/Cauchy-Schwarz bound
`drift_i²/λ ≤ QVRate_i` divided by `λ`. -/
theorem sum_generatorDrift_sq_div_exitRateAt_sq_le_scaledCoordQVCompensator_of_noAbsorbing
    (hNA : M.NoAbsorbing)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) :
    ∑ k ∈ Finset.range n,
      M.generatorDrift (path.stateSeq k) i ^ 2 /
        M.exitRateAt (path.stateSeq k) ^ 2 ≤
    M.scaledCoordQVCompensator path i n := by
  simp only [scaledCoordQVCompensator]
  apply Finset.sum_le_sum
  intro k _
  have hpos := M.exitRateAt_pos_of_noAbsorbing hNA (path.stateSeq k)
  have hle := M.generatorDrift_sq_le_exitRateAt_mul_instantCoordQVRate (path.stateSeq k) i
  rw [div_le_div_iff₀ (sq_pos_of_pos hpos) hpos]
  calc M.generatorDrift (path.stateSeq k) i ^ 2 * M.exitRateAt (path.stateSeq k)
      ≤ (M.exitRateAt (path.stateSeq k) *
          M.instantCoordQVRate (path.stateSeq k) i) *
          M.exitRateAt (path.stateSeq k) :=
        mul_le_mul_of_nonneg_right hle (le_of_lt hpos)
    _ = M.instantCoordQVRate (path.stateSeq k) i *
          M.exitRateAt (path.stateSeq k) ^ 2 := by ring

/-- Canonical a.s. monotonicity of the embedded coordinate QV compensator sampled
at `jumpCount`. -/
theorem canonicalPathMap_scaledCoordQVCompensator_jumpCount_mono_ae_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) (i : Fin d) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ s t : ℝ, s ≤ t →
      M.scaledCoordQVCompensator (M.canonicalPathMap records) i
          ((M.canonicalPathMap records).jumpCount s) ≤
        M.scaledCoordQVCompensator (M.canonicalPathMap records) i
          ((M.canonicalPathMap records).jumpCount t) := by
  filter_upwards
    [M.canonicalPathMap_isCompatible_ae_of_noAbsorbing x₀ hNA,
      M.canonicalPathMap_nonExplosive_ae_of_noAbsorbing x₀ hNA]
    with records hcompat hne s t hst
  exact M.scaledCoordQVCompensator_jumpCount_mono_of_noAbsorbing hNA
    (M.canonicalPathMap records) i hne hcompat.2.1 hst

/-- Vector QV compensators are monotone in the jump index under
`NoAbsorbing`. -/
theorem scaledQVCompensator_mono_of_noAbsorbing
    (hNA : M.NoAbsorbing)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) {m n : ℕ}
    (hmn : m ≤ n) :
    M.scaledQVCompensator path m ≤ M.scaledQVCompensator path n := by
  simp only [scaledQVCompensator]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by
      intro k hk
      exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hmn))
    (fun k _ _ =>
      div_nonneg (M.instantQVRate_nonneg (path.stateSeq k))
        (le_of_lt (M.exitRateAt_pos_of_noAbsorbing hNA (path.stateSeq k))))

/-- Vector QV compensators sampled at `jumpCount` are monotone in clock time
on non-explosive paths. -/
theorem scaledQVCompensator_jumpCount_mono_of_noAbsorbing
    (hNA : M.NoAbsorbing)
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (hne : path.NonExplosive)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    {s t : ℝ} (hst : s ≤ t) :
    M.scaledQVCompensator path (path.jumpCount s) ≤
      M.scaledQVCompensator path (path.jumpCount t) := by
  have hs_future : ∃ n, s < path.times n := path.exists_bound_of_nonExplosive hne s
  have ht_future : ∃ n, t < path.times n := path.exists_bound_of_nonExplosive hne t
  exact M.scaledQVCompensator_mono_of_noAbsorbing hNA path
    (path.jumpCount_mono hstrict hst hs_future ht_future)

/-- Canonical a.s. monotonicity of the embedded vector QV compensator sampled
at `jumpCount`. -/
theorem canonicalPathMap_scaledQVCompensator_jumpCount_mono_ae_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ s t : ℝ, s ≤ t →
      M.scaledQVCompensator (M.canonicalPathMap records)
          ((M.canonicalPathMap records).jumpCount s) ≤
        M.scaledQVCompensator (M.canonicalPathMap records)
          ((M.canonicalPathMap records).jumpCount t) := by
  filter_upwards
    [M.canonicalPathMap_isCompatible_ae_of_noAbsorbing x₀ hNA,
      M.canonicalPathMap_nonExplosive_ae_of_noAbsorbing x₀ hNA]
    with records hcompat hne s t hst
  exact M.scaledQVCompensator_jumpCount_mono_of_noAbsorbing hNA
    (M.canonicalPathMap records) hne hcompat.2.1 hst

/-- Summed coordinate embedded QV compensators are bounded by the vector QV
compensator, up to the dimension factor inherited from the coordinate-to-vector
instantaneous QV comparison. -/
theorem sum_scaledCoordQVCompensator_le_card_mul_scaledQVCompensator_of_noAbsorbing
    (hNA : M.NoAbsorbing)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (n : ℕ) :
    (∑ i : Fin d, M.scaledCoordQVCompensator path i n) ≤
      (Fintype.card (Fin d) : ℝ) * M.scaledQVCompensator path n := by
  simp only [scaledCoordQVCompensator, scaledQVCompensator]
  rw [Finset.sum_comm]
  calc
    (∑ x ∈ Finset.range n,
        ∑ i : Fin d,
          M.instantCoordQVRate (path.stateSeq x) i /
            M.exitRateAt (path.stateSeq x))
        ≤ ∑ x ∈ Finset.range n,
          (Fintype.card (Fin d) : ℝ) *
            (M.instantQVRate (path.stateSeq x) /
              M.exitRateAt (path.stateSeq x)) := by
          refine Finset.sum_le_sum ?_
          intro x _
          have hden_nonneg :
              0 ≤ M.exitRateAt (path.stateSeq x) :=
            le_of_lt (M.exitRateAt_pos_of_noAbsorbing hNA (path.stateSeq x))
          calc
            (∑ i : Fin d,
                M.instantCoordQVRate (path.stateSeq x) i /
                  M.exitRateAt (path.stateSeq x))
                = (∑ i : Fin d, M.instantCoordQVRate (path.stateSeq x) i) /
                    M.exitRateAt (path.stateSeq x) := by
                    simp [div_eq_mul_inv, Finset.sum_mul]
            _ ≤ ((Fintype.card (Fin d) : ℝ) *
                  M.instantQVRate (path.stateSeq x)) /
                  M.exitRateAt (path.stateSeq x) := by
                exact div_le_div_of_nonneg_right
                  (M.sum_instantCoordQVRate_le_card_mul_instantQVRate
                    (path.stateSeq x))
                  hden_nonneg
            _ = (Fintype.card (Fin d) : ℝ) *
                  (M.instantQVRate (path.stateSeq x) /
                    M.exitRateAt (path.stateSeq x)) := by
                ring
    _ = (Fintype.card (Fin d) : ℝ) *
        (∑ x ∈ Finset.range n,
          M.instantQVRate (path.stateSeq x) / M.exitRateAt (path.stateSeq x)) := by
        rw [Finset.mul_sum]

@[simp]
theorem scaledJumpMartingale_zero
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) :
    M.scaledJumpMartingale path i 0 = 0 := by
  simp [scaledJumpMartingale, scaledJumpSum]

@[simp]
theorem scaledCoordJumpSqMartingale_zero
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) :
    M.scaledCoordJumpSqMartingale path i 0 = 0 := by
  simp [scaledCoordJumpSqMartingale]

/-- The drift-over-exit summand is bounded on the finite state space. -/
theorem exists_generatorDrift_div_exitRate_bound (i : Fin d) :
    ∃ C : ℝ, ∀ x : Fin d → Fin (M.N + 1),
      ‖M.generatorDrift x i / M.exitRateAt x‖ ≤ C := by
  refine ⟨∑ x : Fin d → Fin (M.N + 1),
    ‖M.generatorDrift x i / M.exitRateAt x‖, ?_⟩
  intro x
  exact Finset.single_le_sum
    (fun y _ => norm_nonneg (M.generatorDrift y i / M.exitRateAt y))
    (Finset.mem_univ x)

/-- The coordinate generator drift is bounded on the finite state space. -/
theorem exists_generatorDrift_abs_bound (i : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Fin d → Fin (M.N + 1),
      ‖M.generatorDrift x i‖ ≤ C := by
  refine ⟨∑ x : Fin d → Fin (M.N + 1), ‖M.generatorDrift x i‖, ?_, ?_⟩
  · exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  · intro x
    exact Finset.single_le_sum
      (fun y _ => norm_nonneg (M.generatorDrift y i))
      (Finset.mem_univ x)

/-- The coordinate-QV-over-exit summand is bounded on the finite state space. -/
theorem exists_instantCoordQVRate_div_exitRate_bound (i : Fin d) :
    ∃ C : ℝ, ∀ x : Fin d → Fin (M.N + 1),
      ‖M.instantCoordQVRate x i / M.exitRateAt x‖ ≤ C := by
  refine ⟨∑ x : Fin d → Fin (M.N + 1),
    ‖M.instantCoordQVRate x i / M.exitRateAt x‖, ?_⟩
  intro x
  exact Finset.single_le_sum
    (fun y _ => norm_nonneg (M.instantCoordQVRate y i / M.exitRateAt y))
    (Finset.mem_univ x)

/-- The coordinate instantaneous-QV summand is bounded on the finite state
space. -/
theorem exists_instantCoordQVRate_abs_bound (i : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Fin d → Fin (M.N + 1),
      ‖M.instantCoordQVRate x i‖ ≤ C := by
  refine ⟨∑ x : Fin d → Fin (M.N + 1), ‖M.instantCoordQVRate x i‖, ?_, ?_⟩
  · exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  · intro x
    exact Finset.single_le_sum
      (fun y _ => norm_nonneg (M.instantCoordQVRate y i))
      (Finset.mem_univ x)

/-- The vector-QV-over-exit summand is bounded on the finite state space. -/
theorem exists_instantQVRate_div_exitRate_bound :
    ∃ C : ℝ, ∀ x : Fin d → Fin (M.N + 1),
      ‖M.instantQVRate x / M.exitRateAt x‖ ≤ C := by
  refine ⟨∑ x : Fin d → Fin (M.N + 1),
    ‖M.instantQVRate x / M.exitRateAt x‖, ?_⟩
  intro x
  exact Finset.single_le_sum
    (fun y _ => norm_nonneg (M.instantQVRate y / M.exitRateAt y))
    (Finset.mem_univ x)

/-- The drift compensator is measurable with respect to the record history
through the same jump index. -/
theorem measurable_scaledJumpDriftCompensator_canonicalRecordFiltration
    (i : Fin d) (n : ℕ) :
    Measurable[M.canonicalRecordFiltration n]
      (fun records : M.canonicalRecordΩ =>
        M.scaledJumpDriftCompensator (M.canonicalPathMap records) i n) := by
  simp only [scaledJumpDriftCompensator]
  refine Finset.measurable_sum _ ?_
  intro k hk
  have hk_le : k ≤ n := le_of_lt (Finset.mem_range.mp hk)
  have hstate :
      Measurable[M.canonicalRecordFiltration n]
        (fun records : M.canonicalRecordΩ =>
          (M.canonicalPathMap records).stateSeq k) :=
    M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration_le hk_le
  exact (Measurable.of_discrete
    (f := fun x : Fin d → Fin (M.N + 1) =>
      M.generatorDrift x i / M.exitRateAt x)).comp hstate

/-- A completed sojourn time at index `k` is measurable with respect to any
record history through `n`, provided the raw holding record `k+1` is included. -/
theorem measurable_canonicalPathMap_sojournTime_canonicalRecordFiltration_le
    {k n : ℕ} (hkn : k + 1 ≤ n) :
    Measurable[M.canonicalRecordFiltration n]
      (fun records : M.canonicalRecordΩ =>
        (M.canonicalPathMap records).sojournTime k) := by
  simpa [canonicalPathMap, QMatrix.recordTrajectoryToPath_sojournTime] using
    (QMatrix.measurable_record_canonicalRecordFiltration_le
      (S := Fin d → Fin (M.N + 1)) hkn).fst

/-- The completed holding-time drift residual is measurable with respect to
the record history through the same jump index. -/
theorem measurable_scaledHoldingTimeDriftResidual_canonicalRecordFiltration
    (i : Fin d) (n : ℕ) :
    Measurable[M.canonicalRecordFiltration n]
      (fun records : M.canonicalRecordΩ =>
        M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n) := by
  simp only [scaledHoldingTimeDriftResidual]
  refine Finset.measurable_sum _ ?_
  intro k hk
  have hk_le : k ≤ n := le_of_lt (Finset.mem_range.mp hk)
  have hk_succ_le : k + 1 ≤ n := Finset.mem_range.mp hk
  have hstate :
      Measurable[M.canonicalRecordFiltration n]
        (fun records : M.canonicalRecordΩ =>
          (M.canonicalPathMap records).stateSeq k) :=
    M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration_le hk_le
  have hgd :
      Measurable[M.canonicalRecordFiltration n]
        (fun records : M.canonicalRecordΩ =>
          M.generatorDrift ((M.canonicalPathMap records).stateSeq k) i) :=
    (Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) => M.generatorDrift x i)).comp hstate
  have hinv :
      Measurable[M.canonicalRecordFiltration n]
        (fun records : M.canonicalRecordΩ =>
          (M.exitRateAt ((M.canonicalPathMap records).stateSeq k))⁻¹) :=
    (Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) => (M.exitRateAt x)⁻¹)).comp hstate
  have hsoj :
      Measurable[M.canonicalRecordFiltration n]
        (fun records : M.canonicalRecordΩ =>
          (M.canonicalPathMap records).sojournTime k) :=
    M.measurable_canonicalPathMap_sojournTime_canonicalRecordFiltration_le
      hk_succ_le
  exact hgd.mul (hinv.sub hsoj)

/-- The coordinate QV compensator is measurable with respect to the record
history through the same jump index. -/
theorem measurable_scaledCoordQVCompensator_canonicalRecordFiltration
    (i : Fin d) (n : ℕ) :
    Measurable[M.canonicalRecordFiltration n]
      (fun records : M.canonicalRecordΩ =>
        M.scaledCoordQVCompensator (M.canonicalPathMap records) i n) := by
  simp only [scaledCoordQVCompensator]
  refine Finset.measurable_sum _ ?_
  intro k hk
  have hk_le : k ≤ n := le_of_lt (Finset.mem_range.mp hk)
  have hstate :
      Measurable[M.canonicalRecordFiltration n]
        (fun records : M.canonicalRecordΩ =>
          (M.canonicalPathMap records).stateSeq k) :=
    M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration_le hk_le
  exact (Measurable.of_discrete
    (f := fun x : Fin d → Fin (M.N + 1) =>
      M.instantCoordQVRate x i / M.exitRateAt x)).comp hstate

/-- The vector QV compensator is measurable with respect to the record history
through the same jump index. -/
theorem measurable_scaledQVCompensator_canonicalRecordFiltration
    (n : ℕ) :
    Measurable[M.canonicalRecordFiltration n]
      (fun records : M.canonicalRecordΩ =>
        M.scaledQVCompensator (M.canonicalPathMap records) n) := by
  simp only [scaledQVCompensator]
  refine Finset.measurable_sum _ ?_
  intro k hk
  have hk_le : k ≤ n := le_of_lt (Finset.mem_range.mp hk)
  have hstate :
      Measurable[M.canonicalRecordFiltration n]
        (fun records : M.canonicalRecordΩ =>
          (M.canonicalPathMap records).stateSeq k) :=
    M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration_le hk_le
  exact (Measurable.of_discrete
    (f := fun x : Fin d → Fin (M.N + 1) =>
      M.instantQVRate x / M.exitRateAt x)).comp hstate

/-- The drift compensator is strongly adapted to the canonical record
filtration. -/
theorem stronglyAdapted_scaledJumpDriftCompensator_canonicalRecordFiltration
    (i : Fin d) :
    MeasureTheory.StronglyAdapted M.canonicalRecordFiltration
      (fun n records =>
        M.scaledJumpDriftCompensator (M.canonicalPathMap records) i n) :=
  fun n =>
    (M.measurable_scaledJumpDriftCompensator_canonicalRecordFiltration i n).stronglyMeasurable

/-- The completed holding-time drift residual is strongly adapted to the
canonical record filtration. -/
theorem stronglyAdapted_scaledHoldingTimeDriftResidual_canonicalRecordFiltration
    (i : Fin d) :
    MeasureTheory.StronglyAdapted M.canonicalRecordFiltration
      (fun n records =>
        M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n) :=
  fun n =>
    (M.measurable_scaledHoldingTimeDriftResidual_canonicalRecordFiltration i n).stronglyMeasurable

/-- The coordinate QV compensator is strongly adapted to the canonical record
filtration. -/
theorem stronglyAdapted_scaledCoordQVCompensator_canonicalRecordFiltration
    (i : Fin d) :
    MeasureTheory.StronglyAdapted M.canonicalRecordFiltration
      (fun n records =>
        M.scaledCoordQVCompensator (M.canonicalPathMap records) i n) :=
  fun n => (M.measurable_scaledCoordQVCompensator_canonicalRecordFiltration i n).stronglyMeasurable

/-- The vector QV compensator is strongly adapted to the canonical record
filtration. -/
theorem stronglyAdapted_scaledQVCompensator_canonicalRecordFiltration :
    MeasureTheory.StronglyAdapted M.canonicalRecordFiltration
      (fun n records =>
        M.scaledQVCompensator (M.canonicalPathMap records) n) :=
  fun n => (M.measurable_scaledQVCompensator_canonicalRecordFiltration n).stronglyMeasurable

/-- The current drift-over-exit summand is measurable with respect to the
current record history. -/
theorem measurable_generatorDrift_stateSeq_canonicalRecordFiltration
    (i : Fin d) (n : ℕ) :
    Measurable[M.canonicalRecordFiltration n]
      (fun records : M.canonicalRecordΩ =>
        M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i) := by
  exact (Measurable.of_discrete
    (f := fun x : Fin d → Fin (M.N + 1) => M.generatorDrift x i)).comp
      (M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration n)

/-- The current drift-over-exit summand is measurable with respect to the
current record history. -/
theorem measurable_generatorDrift_div_exitRate_stateSeq_canonicalRecordFiltration
    (i : Fin d) (n : ℕ) :
    Measurable[M.canonicalRecordFiltration n]
      (fun records : M.canonicalRecordΩ =>
        M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i /
          M.exitRateAt ((M.canonicalPathMap records).stateSeq n)) := by
  exact (Measurable.of_discrete
    (f := fun x : Fin d → Fin (M.N + 1) =>
      M.generatorDrift x i / M.exitRateAt x)).comp
        (M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration n)

/-- The current coordinate-QV-over-exit summand is measurable with respect to
the current record history. -/
theorem measurable_instantCoordQVRate_div_exitRate_stateSeq_canonicalRecordFiltration
    (i : Fin d) (n : ℕ) :
    Measurable[M.canonicalRecordFiltration n]
      (fun records : M.canonicalRecordΩ =>
        M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq n) i /
          M.exitRateAt ((M.canonicalPathMap records).stateSeq n)) := by
  exact (Measurable.of_discrete
    (f := fun x : Fin d → Fin (M.N + 1) =>
      M.instantCoordQVRate x i / M.exitRateAt x)).comp
        (M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration n)

/-- The current coordinate instantaneous-QV summand is measurable with respect
to the current record history. -/
theorem measurable_instantCoordQVRate_stateSeq_canonicalRecordFiltration
    (i : Fin d) (n : ℕ) :
    Measurable[M.canonicalRecordFiltration n]
      (fun records : M.canonicalRecordΩ =>
        M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq n) i) := by
  exact (Measurable.of_discrete
    (f := fun x : Fin d → Fin (M.N + 1) =>
      M.instantCoordQVRate x i)).comp
        (M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration n)

/-- The drift compensator is integrable at every jump index under the canonical
record law. -/
theorem integrable_scaledJumpDriftCompensator_canonicalRecordMeasure
    (x₀ : Fin d → Fin (M.N + 1)) (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.scaledJumpDriftCompensator (M.canonicalPathMap records) i n)
      (M.canonicalRecordMeasure x₀) := by
  obtain ⟨C, hC⟩ := M.exists_generatorDrift_div_exitRate_bound i
  refine Integrable.of_bound
    ((M.measurable_scaledJumpDriftCompensator_canonicalRecordFiltration i n).mono
      (M.canonicalRecordFiltration.le n) le_rfl).aestronglyMeasurable
    ((n : ℝ) * C) ?_
  refine ae_of_all _ fun records => ?_
  simp only [scaledJumpDriftCompensator]
  calc
    ‖∑ k ∈ Finset.range n,
        M.generatorDrift ((M.canonicalPathMap records).stateSeq k) i /
          M.exitRateAt ((M.canonicalPathMap records).stateSeq k)‖
        ≤ ∑ k ∈ Finset.range n,
            ‖M.generatorDrift ((M.canonicalPathMap records).stateSeq k) i /
              M.exitRateAt ((M.canonicalPathMap records).stateSeq k)‖ :=
          norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range n, C := by
          exact Finset.sum_le_sum fun k _ =>
            hC ((M.canonicalPathMap records).stateSeq k)
    _ = (n : ℝ) * C := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The current drift-over-exit summand is integrable under the canonical
record law. -/
theorem integrable_generatorDrift_div_exitRate_stateSeq_canonicalRecordMeasure
    (x₀ : Fin d → Fin (M.N + 1)) (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i /
          M.exitRateAt ((M.canonicalPathMap records).stateSeq n))
      (M.canonicalRecordMeasure x₀) := by
  obtain ⟨C, hC⟩ := M.exists_generatorDrift_div_exitRate_bound i
  refine Integrable.of_bound
    ((M.measurable_generatorDrift_div_exitRate_stateSeq_canonicalRecordFiltration i n).mono
      (M.canonicalRecordFiltration.le n) le_rfl).aestronglyMeasurable
    C ?_
  exact ae_of_all _ fun records =>
    hC ((M.canonicalPathMap records).stateSeq n)

/-- The square of the current drift-over-exit summand is integrable under the
canonical record law. -/
theorem integrable_generatorDrift_div_exitRate_stateSeq_sq_canonicalRecordMeasure
    (x₀ : Fin d → Fin (M.N + 1)) (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        (M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i /
          M.exitRateAt ((M.canonicalPathMap records).stateSeq n)) ^ 2)
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let B : M.canonicalRecordΩ → ℝ := fun records =>
    M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i /
      M.exitRateAt ((M.canonicalPathMap records).stateSeq n)
  obtain ⟨C, hC⟩ := M.exists_generatorDrift_div_exitRate_bound i
  have hC_nonneg : 0 ≤ C := by
    exact le_trans (norm_nonneg (M.generatorDrift (fun _ => 0) i /
      M.exitRateAt (fun _ => 0))) (hC (fun _ => 0))
  have hB_meas : Measurable B := by
    exact (M.measurable_generatorDrift_div_exitRate_stateSeq_canonicalRecordFiltration i n).mono
      (M.canonicalRecordFiltration.le n) le_rfl
  have hB_sq_sm : AEStronglyMeasurable (fun records => (B records) ^ 2) μ := by
    simpa [pow_two] using
      (hB_meas.aestronglyMeasurable.mul hB_meas.aestronglyMeasurable)
  refine Integrable.of_bound hB_sq_sm (C ^ 2) ?_
  refine ae_of_all _ fun records => ?_
  have hB_bound := hC ((M.canonicalPathMap records).stateSeq n)
  calc
    ‖B records ^ 2‖ = ‖B records‖ ^ 2 := by simp
    _ ≤ C ^ 2 := by
      apply sq_le_sq'
      · have hnonneg : 0 ≤ ‖B records‖ := norm_nonneg _
        linarith
      · exact hB_bound

/-- The coordinate QV compensator is integrable at every jump index under the
canonical record law. -/
theorem integrable_scaledCoordQVCompensator_canonicalRecordMeasure
    (x₀ : Fin d → Fin (M.N + 1)) (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.scaledCoordQVCompensator (M.canonicalPathMap records) i n)
      (M.canonicalRecordMeasure x₀) := by
  obtain ⟨C, hC⟩ := M.exists_instantCoordQVRate_div_exitRate_bound i
  refine Integrable.of_bound
    ((M.measurable_scaledCoordQVCompensator_canonicalRecordFiltration i n).mono
      (M.canonicalRecordFiltration.le n) le_rfl).aestronglyMeasurable
    ((n : ℝ) * C) ?_
  refine ae_of_all _ fun records => ?_
  simp only [scaledCoordQVCompensator]
  calc
    ‖∑ k ∈ Finset.range n,
        M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i /
          M.exitRateAt ((M.canonicalPathMap records).stateSeq k)‖
        ≤ ∑ k ∈ Finset.range n,
            ‖M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i /
              M.exitRateAt ((M.canonicalPathMap records).stateSeq k)‖ :=
          norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range n, C := by
          exact Finset.sum_le_sum fun k _ =>
            hC ((M.canonicalPathMap records).stateSeq k)
    _ = (n : ℝ) * C := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The vector QV compensator is integrable at every jump index under the
canonical record law. -/
theorem integrable_scaledQVCompensator_canonicalRecordMeasure
    (x₀ : Fin d → Fin (M.N + 1)) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.scaledQVCompensator (M.canonicalPathMap records) n)
      (M.canonicalRecordMeasure x₀) := by
  obtain ⟨C, hC⟩ := M.exists_instantQVRate_div_exitRate_bound
  refine Integrable.of_bound
    ((M.measurable_scaledQVCompensator_canonicalRecordFiltration n).mono
      (M.canonicalRecordFiltration.le n) le_rfl).aestronglyMeasurable
    ((n : ℝ) * C) ?_
  refine ae_of_all _ fun records => ?_
  simp only [scaledQVCompensator]
  calc
    ‖∑ k ∈ Finset.range n,
        M.instantQVRate ((M.canonicalPathMap records).stateSeq k) /
          M.exitRateAt ((M.canonicalPathMap records).stateSeq k)‖
        ≤ ∑ k ∈ Finset.range n,
            ‖M.instantQVRate ((M.canonicalPathMap records).stateSeq k) /
              M.exitRateAt ((M.canonicalPathMap records).stateSeq k)‖ :=
          norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range n, C := by
          exact Finset.sum_le_sum fun k _ =>
            hC ((M.canonicalPathMap records).stateSeq k)
    _ = (n : ℝ) * C := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The current coordinate-QV-over-exit summand is integrable under the
canonical record law. -/
theorem integrable_instantCoordQVRate_div_exitRate_stateSeq_canonicalRecordMeasure
    (x₀ : Fin d → Fin (M.N + 1)) (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq n) i /
          M.exitRateAt ((M.canonicalPathMap records).stateSeq n))
      (M.canonicalRecordMeasure x₀) := by
  obtain ⟨C, hC⟩ := M.exists_instantCoordQVRate_div_exitRate_bound i
  refine Integrable.of_bound
    ((M.measurable_instantCoordQVRate_div_exitRate_stateSeq_canonicalRecordFiltration i n).mono
      (M.canonicalRecordFiltration.le n) le_rfl).aestronglyMeasurable
    C ?_
  exact ae_of_all _ fun records =>
    hC ((M.canonicalPathMap records).stateSeq n)

/-- Multiplying the next holding time by a predictable finite-state
coordinate-QV coefficient preserves integrability. -/
theorem integrable_instantCoordQVRate_mul_next_holdingTime
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq n) i *
          (records (n + 1)).1)
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let A : M.canonicalRecordΩ → ℝ := fun records =>
    M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq n) i
  let Y : M.canonicalRecordΩ → ℝ := fun records => (records (n + 1)).1
  obtain ⟨C, hC_nonneg, hC⟩ := M.exists_instantCoordQVRate_abs_bound i
  have hA_meas : Measurable A := by
    exact (M.measurable_instantCoordQVRate_stateSeq_canonicalRecordFiltration i n).mono
      (M.canonicalRecordFiltration.le n) le_rfl
  have hY_int : Integrable Y μ := by
    simpa [Y, μ] using
      M.integrable_next_holdingTime_canonicalRecordMeasure_of_noAbsorbing x₀ hNA n
  have hAY_sm : AEStronglyMeasurable (fun records => A records * Y records) μ :=
    hA_meas.aestronglyMeasurable.mul hY_int.aestronglyMeasurable
  have hbound :
      ∀ᵐ records ∂μ, ‖A records * Y records‖ ≤ C * ‖Y records‖ := by
    refine ae_of_all _ fun records => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (hC ((M.canonicalPathMap records).stateSeq n)) (norm_nonneg _)
  have hdom : Integrable (fun records => C * ‖Y records‖) μ :=
    hY_int.norm.const_mul C
  exact hdom.mono' hAY_sm hbound

/-- Multiplying the completed sojourn time by a predictable finite-state
coordinate drift coefficient preserves integrability. -/
theorem integrable_generatorDrift_mul_sojournTime
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i *
          (M.canonicalPathMap records).sojournTime n)
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let A : M.canonicalRecordΩ → ℝ := fun records =>
    M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i
  let Y : M.canonicalRecordΩ → ℝ := fun records =>
    (M.canonicalPathMap records).sojournTime n
  obtain ⟨C, _hC_nonneg, hC⟩ := M.exists_generatorDrift_abs_bound i
  have hA_meas : Measurable A := by
    exact (M.measurable_generatorDrift_stateSeq_canonicalRecordFiltration i n).mono
      (M.canonicalRecordFiltration.le n) le_rfl
  have hY_int : Integrable Y μ := by
    simpa [Y, μ, canonicalPathMap, QMatrix.recordTrajectoryToPath_sojournTime] using
      M.integrable_next_holdingTime_canonicalRecordMeasure_of_noAbsorbing x₀ hNA n
  have hAY_sm : AEStronglyMeasurable (fun records => A records * Y records) μ :=
    hA_meas.aestronglyMeasurable.mul hY_int.aestronglyMeasurable
  have hbound :
      ∀ᵐ records ∂μ, ‖A records * Y records‖ ≤ C * ‖Y records‖ := by
    refine ae_of_all _ fun records => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (hC ((M.canonicalPathMap records).stateSeq n)) (norm_nonneg _)
  have hdom : Integrable (fun records => C * ‖Y records‖) μ :=
    hY_int.norm.const_mul C
  exact hdom.mono' hAY_sm hbound

/-- The square of a predictable drift coefficient times a completed sojourn time
is integrable under the canonical non-absorbing law. -/
theorem integrable_generatorDrift_mul_sojournTime_sq
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        (M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i *
          (M.canonicalPathMap records).sojournTime n) ^ 2)
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let A : M.canonicalRecordΩ → ℝ := fun records =>
    M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i
  let Y : M.canonicalRecordΩ → ℝ := fun records =>
    (M.canonicalPathMap records).sojournTime n
  obtain ⟨C, hC_nonneg, hC⟩ := M.exists_generatorDrift_abs_bound i
  have hA_meas : Measurable A := by
    exact (M.measurable_generatorDrift_stateSeq_canonicalRecordFiltration i n).mono
      (M.canonicalRecordFiltration.le n) le_rfl
  have hY_meas : Measurable Y := by
    exact (M.measurable_canonicalPathMap_sojournTime_canonicalRecordFiltration_le
      (Nat.le_refl (n + 1))).mono (M.canonicalRecordFiltration.le (n + 1)) le_rfl
  have hY_sq_int : Integrable (fun records => (Y records) ^ 2) μ := by
    simpa [Y, μ, canonicalPathMap, QMatrix.recordTrajectoryToPath_sojournTime] using
      M.integrable_next_holdingTime_sq_canonicalRecordMeasure_of_noAbsorbing x₀ hNA n
  have hAY_sq_sm :
      AEStronglyMeasurable (fun records => (A records * Y records) ^ 2) μ :=
    ((hA_meas.aestronglyMeasurable.mul hY_meas.aestronglyMeasurable).pow 2)
  have hbound :
      ∀ᵐ records ∂μ,
        ‖(A records * Y records) ^ 2‖ ≤ C ^ 2 * ‖(Y records) ^ 2‖ := by
    refine ae_of_all _ fun records => ?_
    have hA_bound := hC ((M.canonicalPathMap records).stateSeq n)
    have hmul_bound :
        ‖A records * Y records‖ ≤ C * ‖Y records‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hA_bound (norm_nonneg _)
    calc
      ‖(A records * Y records) ^ 2‖ = ‖A records * Y records‖ ^ 2 := by
        simp
      _ ≤ (C * ‖Y records‖) ^ 2 := by
        apply sq_le_sq'
        · have hnonneg : 0 ≤ C * ‖Y records‖ :=
            mul_nonneg hC_nonneg (norm_nonneg _)
          have hleft : 0 ≤ ‖A records * Y records‖ := norm_nonneg _
          linarith
        · exact hmul_bound
      _ = C ^ 2 * ‖(Y records) ^ 2‖ := by
        rw [mul_pow, norm_pow]
  have hdom : Integrable (fun records => C ^ 2 * ‖(Y records) ^ 2‖) μ :=
    hY_sq_int.norm.const_mul (C ^ 2)
  exact hdom.mono' hAY_sq_sm hbound

/-- The completed holding-time drift residual is integrable at every fixed
jump index under the canonical non-absorbing law. -/
theorem integrable_scaledHoldingTimeDriftResidual_canonicalRecordMeasure
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n)
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let Cmp : M.canonicalRecordΩ → ℝ := fun records =>
    M.scaledJumpDriftCompensator (M.canonicalPathMap records) i n
  let Clock : M.canonicalRecordΩ → ℝ := fun records =>
    ∑ k ∈ Finset.range n,
      M.generatorDrift ((M.canonicalPathMap records).stateSeq k) i *
        (M.canonicalPathMap records).sojournTime k
  have hCmp_int : Integrable Cmp μ := by
    simpa [Cmp, μ] using
      M.integrable_scaledJumpDriftCompensator_canonicalRecordMeasure x₀ i n
  have hClock_int : Integrable Clock μ := by
    simp only [Clock]
    exact integrable_finset_sum (Finset.range n) fun k _ =>
      M.integrable_generatorDrift_mul_sojournTime x₀ hNA i k
  have hres :
      (fun records : M.canonicalRecordΩ =>
        M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n)
        =ᵐ[μ]
      fun records => Cmp records - Clock records := by
    refine ae_of_all _ fun records => ?_
    simp only [scaledHoldingTimeDriftResidual, scaledJumpDriftCompensator,
      Cmp, Clock]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro k _hk
    rw [div_eq_mul_inv]
    ring
  exact (hCmp_int.sub hClock_int).congr hres.symm

/-- The completed holding-time drift residual has an integrable square at every
fixed jump index under the canonical non-absorbing law. -/
theorem integrable_scaledHoldingTimeDriftResidual_sq_canonicalRecordMeasure
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        (M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n) ^ 2)
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let term : ℕ → M.canonicalRecordΩ → ℝ := fun k records =>
    M.generatorDrift ((M.canonicalPathMap records).stateSeq k) i *
      ((M.exitRateAt ((M.canonicalPathMap records).stateSeq k))⁻¹ -
        (M.canonicalPathMap records).sojournTime k)
  have hterm_memLp : ∀ k ∈ Finset.range n, MemLp (term k) 2 μ := by
    intro k _hk
    let Div : M.canonicalRecordΩ → ℝ := fun records =>
      M.generatorDrift ((M.canonicalPathMap records).stateSeq k) i /
        M.exitRateAt ((M.canonicalPathMap records).stateSeq k)
    let Clock : M.canonicalRecordΩ → ℝ := fun records =>
      M.generatorDrift ((M.canonicalPathMap records).stateSeq k) i *
        (M.canonicalPathMap records).sojournTime k
    have hDiv_meas : AEStronglyMeasurable Div μ := by
      exact ((M.measurable_generatorDrift_div_exitRate_stateSeq_canonicalRecordFiltration
        i k).mono (M.canonicalRecordFiltration.le k) le_rfl).aestronglyMeasurable
    have hDiv_memLp : MemLp Div 2 μ :=
      (memLp_two_iff_integrable_sq hDiv_meas).2
        (by
          simpa [Div, μ] using
            M.integrable_generatorDrift_div_exitRate_stateSeq_sq_canonicalRecordMeasure x₀ i k)
    have hClock_meas : AEStronglyMeasurable Clock μ := by
      have hgd : Measurable fun records : M.canonicalRecordΩ =>
          M.generatorDrift ((M.canonicalPathMap records).stateSeq k) i :=
        (M.measurable_generatorDrift_stateSeq_canonicalRecordFiltration i k).mono
          (M.canonicalRecordFiltration.le k) le_rfl
      have hsoj : Measurable fun records : M.canonicalRecordΩ =>
          (M.canonicalPathMap records).sojournTime k :=
        (M.measurable_canonicalPathMap_sojournTime_canonicalRecordFiltration_le
          (Nat.le_refl (k + 1))).mono
          (M.canonicalRecordFiltration.le (k + 1)) le_rfl
      exact (hgd.mul hsoj).aestronglyMeasurable
    have hClock_memLp : MemLp Clock 2 μ :=
      (memLp_two_iff_integrable_sq hClock_meas).2
        (by
          simpa [Clock, μ] using
            M.integrable_generatorDrift_mul_sojournTime_sq x₀ hNA i k)
    have hterm_eq : term k = Div - Clock := by
      funext records
      simp [term, Div, Clock, div_eq_mul_inv]
      ring
    simpa [hterm_eq] using hDiv_memLp.sub hClock_memLp
  have hsum_memLp :
      MemLp (fun records : M.canonicalRecordΩ =>
        ∑ k ∈ Finset.range n, term k records) 2 μ :=
    memLp_finset_sum (Finset.range n) hterm_memLp
  simpa [scaledHoldingTimeDriftResidual, term, μ] using hsum_memLp.integrable_sq

/-- The completed holding-time drift residual has zero conditional expected
increment with respect to the canonical record filtration. -/
theorem condExp_scaledHoldingTimeDriftResidual_increment_eq_zero_ae_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (n : ℕ) (i : Fin d) :
    (M.canonicalRecordMeasure x₀)[
      (fun records : M.canonicalRecordΩ =>
        M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i (n + 1) -
          M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n)
      | M.canonicalRecordFiltration n] =ᵐ[M.canonicalRecordMeasure x₀] 0 := by
  let μ := M.canonicalRecordMeasure x₀
  let A : M.canonicalRecordΩ → ℝ := fun records =>
    M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i
  let Y : M.canonicalRecordΩ → ℝ := fun records =>
    (M.canonicalPathMap records).sojournTime n
  let comp : M.canonicalRecordΩ → ℝ := fun records =>
    M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i /
      M.exitRateAt ((M.canonicalPathMap records).stateSeq n)
  let clock : M.canonicalRecordΩ → ℝ := fun records => A records * Y records
  have hA_sm :
      StronglyMeasurable[M.canonicalRecordFiltration n] A :=
    (M.measurable_generatorDrift_stateSeq_canonicalRecordFiltration
      i n).stronglyMeasurable
  have hY_int : Integrable Y μ := by
    simpa [Y, μ, canonicalPathMap, QMatrix.recordTrajectoryToPath_sojournTime] using
      M.integrable_next_holdingTime_canonicalRecordMeasure_of_noAbsorbing x₀ hNA n
  have hclock_int : Integrable clock μ := by
    simpa [clock, A, Y, μ] using
      M.integrable_generatorDrift_mul_sojournTime x₀ hNA i n
  have hcomp_int : Integrable comp μ := by
    simpa [comp, μ] using
      M.integrable_generatorDrift_div_exitRate_stateSeq_canonicalRecordMeasure x₀ i n
  have hY_cond :
      μ[Y | M.canonicalRecordFiltration n] =ᵐ[μ]
        fun records => (M.exitRateAt ((M.canonicalPathMap records).stateSeq n))⁻¹ := by
    have h :=
      M.condExp_next_holdingTime_eq_inv_exitRate_of_noAbsorbing x₀ hNA n
    dsimp [μ, Y]
    rw [canonicalRecordFiltration,
      QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe]
    simpa [canonicalPathMap, QMatrix.recordTrajectoryToPath_sojournTime] using h
  have hpull :
      μ[clock | M.canonicalRecordFiltration n] =ᵐ[μ]
        fun records => A records *
          (μ[Y | M.canonicalRecordFiltration n]) records := by
    simpa [clock] using
      MeasureTheory.condExp_mul_of_stronglyMeasurable_left
        hA_sm hclock_int hY_int
  have hclock_cond :
      μ[clock | M.canonicalRecordFiltration n] =ᵐ[μ] comp := by
    filter_upwards [hpull, hY_cond] with records hpull_records hY_records
    rw [hpull_records, hY_records]
    simp [A, comp, div_eq_mul_inv]
  have hcomp_cond :
      μ[comp | M.canonicalRecordFiltration n] = comp := by
    exact MeasureTheory.condExp_of_stronglyMeasurable
      (M.canonicalRecordFiltration.le n)
      (M.measurable_generatorDrift_div_exitRate_stateSeq_canonicalRecordFiltration
        i n).stronglyMeasurable
      hcomp_int
  have hsub :
      μ[comp - clock | M.canonicalRecordFiltration n] =ᵐ[μ]
        μ[comp | M.canonicalRecordFiltration n] -
          μ[clock | M.canonicalRecordFiltration n] :=
    MeasureTheory.condExp_sub hcomp_int hclock_int
      (M.canonicalRecordFiltration n)
  have hinc :
      (fun records : M.canonicalRecordΩ =>
        M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i (n + 1) -
          M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n)
        =ᵐ[μ]
      comp - clock := by
    refine ae_of_all _ fun records => ?_
    simp [comp, clock, A, Y, M.scaledHoldingTimeDriftResidual_succ_sub,
      div_eq_mul_inv]
    ring
  refine (MeasureTheory.condExp_congr_ae hinc).trans ?_
  change μ[comp - clock | M.canonicalRecordFiltration n] =ᵐ[μ] 0
  rw [hcomp_cond] at hsub
  filter_upwards [hsub, hclock_cond] with records hsub_records hclock_records
  rw [hsub_records]
  simp [Pi.sub_apply, hclock_records]

/-- The completed holding-time drift residual is a martingale along the embedded
jump index under the canonical non-absorbing record law. -/
theorem scaledHoldingTimeDriftResidual_martingale_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) (i : Fin d) :
    MeasureTheory.Martingale
      (fun n records =>
        M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n)
      M.canonicalRecordFiltration (M.canonicalRecordMeasure x₀) :=
  MeasureTheory.martingale_of_condExp_sub_eq_zero_nat
    (M.stronglyAdapted_scaledHoldingTimeDriftResidual_canonicalRecordFiltration i)
    (M.integrable_scaledHoldingTimeDriftResidual_canonicalRecordMeasure x₀ hNA i)
    (fun n =>
      M.condExp_scaledHoldingTimeDriftResidual_increment_eq_zero_ae_of_noAbsorbing
        x₀ hNA n i)

/-- Orthogonality of a completed holding-time residual increment against the
previous embedded-time residual value. -/
theorem integral_scaledHoldingTimeDriftResidual_mul_increment_eq_zero_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    ∫ records,
        M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n *
          (M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i (n + 1) -
            M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n)
        ∂M.canonicalRecordMeasure x₀ = 0 := by
  let μ := M.canonicalRecordMeasure x₀
  let Z : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n
  let inc : M.canonicalRecordΩ → ℝ := fun records => Z (n + 1) records - Z n records
  have hZ_memLp : MemLp (Z n) 2 μ := by
    exact (memLp_two_iff_integrable_sq
      (((M.stronglyAdapted_scaledHoldingTimeDriftResidual_canonicalRecordFiltration i n).mono
        (M.canonicalRecordFiltration.le n)).aestronglyMeasurable)).2
      (by
        simpa [Z, μ] using
          M.integrable_scaledHoldingTimeDriftResidual_sq_canonicalRecordMeasure x₀ hNA i n)
  have hZ_succ_memLp : MemLp (Z (n + 1)) 2 μ := by
    exact (memLp_two_iff_integrable_sq
      (((M.stronglyAdapted_scaledHoldingTimeDriftResidual_canonicalRecordFiltration i (n + 1)).mono
        (M.canonicalRecordFiltration.le (n + 1))).aestronglyMeasurable)).2
      (by
        simpa [Z, μ] using
          M.integrable_scaledHoldingTimeDriftResidual_sq_canonicalRecordMeasure
            x₀ hNA i (n + 1))
  have hinc_memLp : MemLp inc 2 μ := by
    simpa [inc, Pi.sub_apply] using hZ_succ_memLp.sub hZ_memLp
  have hinc_int : Integrable inc μ := hinc_memLp.integrable one_le_two
  have hprod_int : Integrable (fun records => Z n records * inc records) μ := by
    simpa [mul_comm] using hinc_memLp.integrable_mul hZ_memLp
  have hpull :
      μ[(fun records => Z n records * inc records) | M.canonicalRecordFiltration n]
        =ᵐ[μ]
      fun records => Z n records *
        (μ[inc | M.canonicalRecordFiltration n]) records := by
    exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (M.stronglyAdapted_scaledHoldingTimeDriftResidual_canonicalRecordFiltration i n)
      hprod_int hinc_int
  have hcond_inc :
      μ[inc | M.canonicalRecordFiltration n] =ᵐ[μ] 0 := by
    simpa [inc, Z, μ] using
      M.condExp_scaledHoldingTimeDriftResidual_increment_eq_zero_ae_of_noAbsorbing
        x₀ hNA n i
  have hcond_prod :
      μ[(fun records => Z n records * inc records) | M.canonicalRecordFiltration n]
        =ᵐ[μ] 0 := by
    filter_upwards [hpull, hcond_inc] with records hpull_records hinc_records
    rw [hpull_records, hinc_records]
    simp
  calc
    ∫ records, Z n records * inc records ∂μ
        = ∫ records,
            (μ[(fun records => Z n records * inc records) |
              M.canonicalRecordFiltration n]) records ∂μ := by
            exact (integral_condExp
              (μ := μ)
              (m := M.canonicalRecordFiltration n)
              (f := fun records => Z n records * inc records)
              (M.canonicalRecordFiltration.le n)).symm
    _ = 0 := by
          simpa using integral_congr_ae hcond_prod

/-- L2 recursion for the completed holding-time drift residual. -/
theorem integral_scaledHoldingTimeDriftResidual_sq_succ_eq_add_increment_sq_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    ∫ records,
        (M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i (n + 1)) ^ 2
        ∂M.canonicalRecordMeasure x₀ =
      ∫ records,
        (M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n) ^ 2
        ∂M.canonicalRecordMeasure x₀ +
      ∫ records,
        (M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i (n + 1) -
          M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n) ^ 2
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let Z : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n
  let inc : M.canonicalRecordΩ → ℝ := fun records => Z (n + 1) records - Z n records
  have hZ_memLp : MemLp (Z n) 2 μ := by
    exact (memLp_two_iff_integrable_sq
      (((M.stronglyAdapted_scaledHoldingTimeDriftResidual_canonicalRecordFiltration i n).mono
        (M.canonicalRecordFiltration.le n)).aestronglyMeasurable)).2
      (by
        simpa [Z, μ] using
          M.integrable_scaledHoldingTimeDriftResidual_sq_canonicalRecordMeasure x₀ hNA i n)
  have hZ_succ_memLp : MemLp (Z (n + 1)) 2 μ := by
    exact (memLp_two_iff_integrable_sq
      (((M.stronglyAdapted_scaledHoldingTimeDriftResidual_canonicalRecordFiltration i (n + 1)).mono
        (M.canonicalRecordFiltration.le (n + 1))).aestronglyMeasurable)).2
      (by
        simpa [Z, μ] using
          M.integrable_scaledHoldingTimeDriftResidual_sq_canonicalRecordMeasure
            x₀ hNA i (n + 1))
  have hinc_memLp : MemLp inc 2 μ := by
    simpa [inc, Pi.sub_apply] using hZ_succ_memLp.sub hZ_memLp
  have hZ_sq_int : Integrable (fun records => (Z n records) ^ 2) μ :=
    hZ_memLp.integrable_sq
  have hinc_sq_int : Integrable (fun records => (inc records) ^ 2) μ :=
    hinc_memLp.integrable_sq
  have hprod_int : Integrable (fun records => Z n records * inc records) μ := by
    simpa [mul_comm] using hinc_memLp.integrable_mul hZ_memLp
  have hcross :
      ∫ records, Z n records * inc records ∂μ = 0 := by
    simpa [Z, inc, μ] using
      M.integral_scaledHoldingTimeDriftResidual_mul_increment_eq_zero_of_noAbsorbing
        x₀ hNA i n
  let A : M.canonicalRecordΩ → ℝ := fun records => (Z n records) ^ 2
  let B : M.canonicalRecordΩ → ℝ := fun records => 2 * (Z n records * inc records)
  let C : M.canonicalRecordΩ → ℝ := fun records => (inc records) ^ 2
  have hA_int : Integrable A μ := by simpa [A] using hZ_sq_int
  have hB_int : Integrable B μ := by simpa [B] using hprod_int.const_mul 2
  have hC_int : Integrable C μ := by simpa [C] using hinc_sq_int
  have hsum :
      ∫ records, ((A + (B + C)) records) ∂μ =
        ∫ records, A records ∂μ +
          ∫ records, B records ∂μ +
          ∫ records, C records ∂μ := by
    have h1 :
        ∫ records, ((A + (B + C)) records) ∂μ =
          ∫ records, A records ∂μ + ∫ records, ((B + C) records) ∂μ := by
      simpa only [Pi.add_apply] using integral_add hA_int (hB_int.add hC_int)
    have h2 :
        ∫ records, ((B + C) records) ∂μ =
          ∫ records, B records ∂μ + ∫ records, C records ∂μ := by
      simpa only [Pi.add_apply] using integral_add hB_int hC_int
    rw [h1, h2]
    ring
  have hB_zero : ∫ records, B records ∂μ = 0 := by
    calc
      ∫ records, B records ∂μ = 2 * ∫ records, Z n records * inc records ∂μ := by
        simpa [B] using
          (integral_const_mul (μ := μ) (r := (2 : ℝ))
            (f := fun records => Z n records * inc records))
      _ = 0 := by rw [hcross, mul_zero]
  calc
    ∫ records, (Z (n + 1) records) ^ 2 ∂μ
        = ∫ records, A records + B records + C records ∂μ := by
            apply integral_congr_ae
            exact ae_of_all _ fun records => by
              dsimp [A, B, C, inc]
              ring
    _ = ∫ records, ((A + (B + C)) records) ∂μ := by
          apply integral_congr_ae
          exact ae_of_all _ fun records => by
            dsimp [A, B, C]
            ring
    _ = ∫ records, A records ∂μ +
          ∫ records, B records ∂μ +
          ∫ records, C records ∂μ := hsum
    _ = ∫ records, (Z n records) ^ 2 ∂μ +
          ∫ records, (inc records) ^ 2 ∂μ := by
          rw [hB_zero]
          simp [A, C]
    _ = ∫ records,
          (M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n) ^ 2
          ∂M.canonicalRecordMeasure x₀ +
        ∫ records,
          (M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i (n + 1) -
            M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n) ^ 2
          ∂M.canonicalRecordMeasure x₀ := by
          rfl

/-- Terminal L2 identity for the completed holding-time drift residual as the
sum of its orthogonal increment squares. -/
theorem integral_scaledHoldingTimeDriftResidual_sq_eq_sum_increment_sq_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    ∫ records,
        (M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n) ^ 2
        ∂M.canonicalRecordMeasure x₀ =
      ∑ k ∈ Finset.range n,
        ∫ records,
          (M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i (k + 1) -
            M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k) ^ 2
          ∂M.canonicalRecordMeasure x₀ := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [M.integral_scaledHoldingTimeDriftResidual_sq_succ_eq_add_increment_sq_of_noAbsorbing
        x₀ hNA i n, ih]
      rw [Finset.sum_range_succ]

/-- Fixed-step second-moment bridge for completed holding times with predictable
coordinate drift-squared coefficient. -/
theorem integral_generatorDrift_sq_mul_sojournTime_sq_eq_two_integral_div_exitRate_sq
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    ∫ records,
        (M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i) ^ 2 *
          ((M.canonicalPathMap records).sojournTime n) ^ 2
        ∂M.canonicalRecordMeasure x₀ =
      ∫ records,
        2 * ((M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i) ^ 2 /
          (M.exitRateAt ((M.canonicalPathMap records).stateSeq n)) ^ 2)
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let A : M.canonicalRecordΩ → ℝ := fun records =>
    (M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i) ^ 2
  let Y2 : M.canonicalRecordΩ → ℝ := fun records =>
    ((M.canonicalPathMap records).sojournTime n) ^ 2
  let B : M.canonicalRecordΩ → ℝ := fun records =>
    2 * ((M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i) ^ 2 /
      (M.exitRateAt ((M.canonicalPathMap records).stateSeq n)) ^ 2)
  have hA_sm :
      StronglyMeasurable[M.canonicalRecordFiltration n] A := by
    exact ((M.measurable_generatorDrift_stateSeq_canonicalRecordFiltration
      i n).pow measurable_const).stronglyMeasurable
  have hY2_int : Integrable Y2 μ := by
    simpa [Y2, μ, canonicalPathMap, QMatrix.recordTrajectoryToPath_sojournTime] using
      M.integrable_next_holdingTime_sq_canonicalRecordMeasure_of_noAbsorbing x₀ hNA n
  have hAY2_int : Integrable (fun records => A records * Y2 records) μ := by
    exact (M.integrable_generatorDrift_mul_sojournTime_sq x₀ hNA i n).congr
      (ae_of_all _ fun records => by
        dsimp [A, Y2]
        ring)
  have hY2_cond :
      μ[Y2 | M.canonicalRecordFiltration n] =ᵐ[μ]
        fun records => 2 * (M.exitRateAt ((M.canonicalPathMap records).stateSeq n))⁻¹ ^ 2 := by
    have h :=
      M.condExp_next_holdingTime_sq_eq_two_div_exitRate_sq_of_noAbsorbing x₀ hNA n
    dsimp [μ, Y2]
    rw [canonicalRecordFiltration,
      QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe]
    simpa [canonicalPathMap, QMatrix.recordTrajectoryToPath_sojournTime] using h
  have hpull :
      μ[(fun records => A records * Y2 records) | M.canonicalRecordFiltration n]
        =ᵐ[μ]
      fun records => A records * (μ[Y2 | M.canonicalRecordFiltration n]) records := by
    exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      hA_sm hAY2_int hY2_int
  have hcond_prod :
      μ[(fun records => A records * Y2 records) | M.canonicalRecordFiltration n]
        =ᵐ[μ] B := by
    filter_upwards [hpull, hY2_cond] with records hpull_records hY2_records
    rw [hpull_records, hY2_records]
    simp [A, B, div_eq_mul_inv]
    ring
  calc
    ∫ records, A records * Y2 records ∂μ
        = ∫ records,
            (μ[(fun records => A records * Y2 records) |
              M.canonicalRecordFiltration n]) records ∂μ := by
            exact (integral_condExp
              (μ := μ)
              (m := M.canonicalRecordFiltration n)
              (f := fun records => A records * Y2 records)
              (M.canonicalRecordFiltration.le n)).symm
    _ = ∫ records, B records ∂μ := by
          exact integral_congr_ae hcond_prod
    _ = ∫ records,
        2 * ((M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i) ^ 2 /
          (M.exitRateAt ((M.canonicalPathMap records).stateSeq n)) ^ 2)
        ∂M.canonicalRecordMeasure x₀ := by
          simp [B, μ]

/-- The product `(drift² / exitRate) * holdingTime` is integrable under the
canonical non-absorbing law. -/
theorem integrable_generatorDrift_sq_div_exitRate_mul_sojournTime
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        ((M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i) ^ 2 /
          M.exitRateAt ((M.canonicalPathMap records).stateSeq n)) *
          (M.canonicalPathMap records).sojournTime n)
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let A : M.canonicalRecordΩ → ℝ := fun records =>
    (M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i) ^ 2 /
      M.exitRateAt ((M.canonicalPathMap records).stateSeq n)
  let Y : M.canonicalRecordΩ → ℝ := fun records =>
    (M.canonicalPathMap records).sojournTime n
  have hA_meas : Measurable A :=
    ((Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) =>
        (M.generatorDrift x i) ^ 2 / M.exitRateAt x)).comp
          (M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration n)).mono
            (M.canonicalRecordFiltration.le n) le_rfl
  have hY_int : Integrable Y μ := by
    simpa [Y, μ, canonicalPathMap, QMatrix.recordTrajectoryToPath_sojournTime] using
      M.integrable_next_holdingTime_canonicalRecordMeasure_of_noAbsorbing x₀ hNA n
  let C : ℝ := ∑ x : Fin d → Fin (M.N + 1),
    ‖(M.generatorDrift x i) ^ 2 / M.exitRateAt x‖
  have hC_bound : ∀ x : Fin d → Fin (M.N + 1),
      ‖(M.generatorDrift x i) ^ 2 / M.exitRateAt x‖ ≤ C := by
    intro x
    exact Finset.single_le_sum
      (fun y _ => norm_nonneg ((M.generatorDrift y i) ^ 2 / M.exitRateAt y))
      (Finset.mem_univ x)
  have hAY_sm : AEStronglyMeasurable (fun records => A records * Y records) μ :=
    hA_meas.aestronglyMeasurable.mul hY_int.aestronglyMeasurable
  have hbound :
      ∀ᵐ records ∂μ, ‖A records * Y records‖ ≤ C * ‖Y records‖ := by
    refine ae_of_all _ fun records => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (hC_bound ((M.canonicalPathMap records).stateSeq n)) (norm_nonneg _)
  have hdom : Integrable (fun records => C * ‖Y records‖) μ :=
    hY_int.norm.const_mul C
  exact hdom.mono' hAY_sm hbound

/-- Fixed-step first-moment bridge for completed holding times with predictable
`drift² / exitRate` coefficient. -/
theorem integral_generatorDrift_sq_div_exitRate_mul_sojournTime_eq_integral_div_exitRate_sq
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    ∫ records,
        ((M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i) ^ 2 /
          M.exitRateAt ((M.canonicalPathMap records).stateSeq n)) *
          (M.canonicalPathMap records).sojournTime n
        ∂M.canonicalRecordMeasure x₀ =
      ∫ records,
        (M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i) ^ 2 /
          (M.exitRateAt ((M.canonicalPathMap records).stateSeq n)) ^ 2
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let A : M.canonicalRecordΩ → ℝ := fun records =>
    (M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i) ^ 2 /
      M.exitRateAt ((M.canonicalPathMap records).stateSeq n)
  let Y : M.canonicalRecordΩ → ℝ := fun records =>
    (M.canonicalPathMap records).sojournTime n
  let B : M.canonicalRecordΩ → ℝ := fun records =>
    (M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i) ^ 2 /
      (M.exitRateAt ((M.canonicalPathMap records).stateSeq n)) ^ 2
  have hA_meas : Measurable A :=
    ((Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) =>
        (M.generatorDrift x i) ^ 2 / M.exitRateAt x)).comp
          (M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration n)).mono
            (M.canonicalRecordFiltration.le n) le_rfl
  have hA_sm :
      StronglyMeasurable[M.canonicalRecordFiltration n] A := by
    exact (Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) =>
        (M.generatorDrift x i) ^ 2 / M.exitRateAt x)).comp
          (M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration n) |>.stronglyMeasurable
  have hY_int : Integrable Y μ := by
    simpa [Y, μ, canonicalPathMap, QMatrix.recordTrajectoryToPath_sojournTime] using
      M.integrable_next_holdingTime_canonicalRecordMeasure_of_noAbsorbing x₀ hNA n
  have hAY_int : Integrable (fun records => A records * Y records) μ := by
    let C : ℝ := ∑ x : Fin d → Fin (M.N + 1),
      ‖(M.generatorDrift x i) ^ 2 / M.exitRateAt x‖
    have hC_bound : ∀ x : Fin d → Fin (M.N + 1),
        ‖(M.generatorDrift x i) ^ 2 / M.exitRateAt x‖ ≤ C := by
      intro x
      exact Finset.single_le_sum
        (fun y _ => norm_nonneg ((M.generatorDrift y i) ^ 2 / M.exitRateAt y))
        (Finset.mem_univ x)
    have hAY_sm : AEStronglyMeasurable (fun records => A records * Y records) μ :=
      hA_meas.aestronglyMeasurable.mul hY_int.aestronglyMeasurable
    have hbound :
        ∀ᵐ records ∂μ, ‖A records * Y records‖ ≤ C * ‖Y records‖ := by
      refine ae_of_all _ fun records => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hC_bound ((M.canonicalPathMap records).stateSeq n)) (norm_nonneg _)
    have hdom : Integrable (fun records => C * ‖Y records‖) μ :=
      hY_int.norm.const_mul C
    exact hdom.mono' hAY_sm hbound
  have hY_cond :
      μ[Y | M.canonicalRecordFiltration n] =ᵐ[μ]
        fun records => (M.exitRateAt ((M.canonicalPathMap records).stateSeq n))⁻¹ := by
    have h :=
      M.condExp_next_holdingTime_eq_inv_exitRate_of_noAbsorbing x₀ hNA n
    dsimp [μ, Y]
    rw [canonicalRecordFiltration,
      QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe]
    simpa [canonicalPathMap, QMatrix.recordTrajectoryToPath_sojournTime] using h
  have hpull :
      μ[(fun records => A records * Y records) | M.canonicalRecordFiltration n]
        =ᵐ[μ]
      fun records => A records * (μ[Y | M.canonicalRecordFiltration n]) records := by
    exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      hA_sm hAY_int hY_int
  have hcond_prod :
      μ[(fun records => A records * Y records) | M.canonicalRecordFiltration n]
        =ᵐ[μ] B := by
    filter_upwards [hpull, hY_cond] with records hpull_records hY_records
    rw [hpull_records, hY_records]
    simp [A, B, div_eq_mul_inv]
    ring
  calc
    ∫ records, A records * Y records ∂μ
        = ∫ records,
            (μ[(fun records => A records * Y records) |
              M.canonicalRecordFiltration n]) records ∂μ := by
            exact (integral_condExp
              (μ := μ)
              (m := M.canonicalRecordFiltration n)
              (f := fun records => A records * Y records)
              (M.canonicalRecordFiltration.le n)).symm
    _ = ∫ records, B records ∂μ := by
          exact integral_congr_ae hcond_prod
    _ = ∫ records,
        (M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i) ^ 2 /
          (M.exitRateAt ((M.canonicalPathMap records).stateSeq n)) ^ 2
        ∂M.canonicalRecordMeasure x₀ := by
          simp [B, μ]

/-- One-step L2 identity for the completed holding-time drift residual increment. -/
theorem integral_residual_increment_sq_eq_integral_drift_sq_div_exit_sq
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    ∫ records,
        (M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i (n + 1) -
          M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n) ^ 2
        ∂M.canonicalRecordMeasure x₀ =
      ∫ records,
        (M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i) ^ 2 /
          (M.exitRateAt ((M.canonicalPathMap records).stateSeq n)) ^ 2
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let T1 : M.canonicalRecordΩ → ℝ := fun records =>
    (M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i) ^ 2 *
      ((M.canonicalPathMap records).sojournTime n) ^ 2
  let T2 : M.canonicalRecordΩ → ℝ := fun records =>
    ((M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i) ^ 2 /
      M.exitRateAt ((M.canonicalPathMap records).stateSeq n)) *
      (M.canonicalPathMap records).sojournTime n
  let T3 : M.canonicalRecordΩ → ℝ := fun records =>
    (M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i) ^ 2 /
      (M.exitRateAt ((M.canonicalPathMap records).stateSeq n)) ^ 2
  have hT1_int : Integrable T1 μ := by
    exact (M.integrable_generatorDrift_mul_sojournTime_sq x₀ hNA i n).congr
      (ae_of_all _ fun records => by
        dsimp [T1]
        ring)
  have hT2_int : Integrable T2 μ := by
    simpa [T2, μ] using
      M.integrable_generatorDrift_sq_div_exitRate_mul_sojournTime x₀ hNA i n
  have hT3_int : Integrable T3 μ := by
    exact (M.integrable_generatorDrift_div_exitRate_stateSeq_sq_canonicalRecordMeasure
      x₀ i n).congr
      (ae_of_all _ fun records => by
        dsimp [T3]
        ring)
  have hT1 :
      ∫ records, T1 records ∂μ =
        ∫ records, 2 * T3 records ∂μ := by
    simpa [T1, T3, μ] using
      M.integral_generatorDrift_sq_mul_sojournTime_sq_eq_two_integral_div_exitRate_sq
        x₀ hNA i n
  have hT2 :
      ∫ records, T2 records ∂μ =
        ∫ records, T3 records ∂μ := by
    simpa [T2, T3, μ] using
      M.integral_generatorDrift_sq_div_exitRate_mul_sojournTime_eq_integral_div_exitRate_sq
        x₀ hNA i n
  have hlin :
      ∫ records, (T1 records - 2 * T2 records + T3 records) ∂μ =
        ∫ records, T1 records ∂μ -
          2 * ∫ records, T2 records ∂μ +
          ∫ records, T3 records ∂μ := by
    have h2T2_int : Integrable (fun records => 2 * T2 records) μ :=
      hT2_int.const_mul 2
    calc
      ∫ records, (T1 records - 2 * T2 records + T3 records) ∂μ
          = ∫ records, (T1 records - (2 * T2 records)) ∂μ +
              ∫ records, T3 records ∂μ := by
              simpa [sub_eq_add_neg, add_assoc] using
                integral_add (hT1_int.sub h2T2_int) hT3_int
      _ = (∫ records, T1 records ∂μ - ∫ records, 2 * T2 records ∂μ) +
              ∫ records, T3 records ∂μ := by
              rw [integral_sub hT1_int h2T2_int]
      _ = ∫ records, T1 records ∂μ -
              2 * ∫ records, T2 records ∂μ +
              ∫ records, T3 records ∂μ := by
              rw [integral_const_mul]
  have htwoT3 :
      ∫ records, 2 * T3 records ∂μ = 2 * ∫ records, T3 records ∂μ := by
    exact integral_const_mul (μ := μ) (r := (2 : ℝ)) (f := T3)
  calc
    ∫ records,
        (M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i (n + 1) -
          M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n) ^ 2
        ∂M.canonicalRecordMeasure x₀
        = ∫ records, (T1 records - 2 * T2 records + T3 records) ∂μ := by
            apply integral_congr_ae
            refine ae_of_all _ fun records => ?_
            simp [T1, T2, T3, M.scaledHoldingTimeDriftResidual_succ_sub,
              div_eq_mul_inv]
            ring
    _ = ∫ records, T1 records ∂μ -
          2 * ∫ records, T2 records ∂μ +
          ∫ records, T3 records ∂μ := hlin
    _ = ∫ records, T3 records ∂μ := by
          rw [hT1, hT2, htwoT3]
          ring
    _ = ∫ records,
        (M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i) ^ 2 /
          (M.exitRateAt ((M.canonicalPathMap records).stateSeq n)) ^ 2
        ∂M.canonicalRecordMeasure x₀ := by
          simp [T3, μ]

/-- Terminal L2 identity for the completed holding-time residual against the
sum of `drift² / exitRate²` along the embedded chain. -/
theorem integral_scaledHoldingTimeDriftResidual_sq_eq_integral_sum_drift_sq_div_exit_sq
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    ∫ records,
        (M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n) ^ 2
        ∂M.canonicalRecordMeasure x₀ =
      ∫ records,
        (∑ k ∈ Finset.range n,
          (M.generatorDrift ((M.canonicalPathMap records).stateSeq k) i) ^ 2 /
            (M.exitRateAt ((M.canonicalPathMap records).stateSeq k)) ^ 2)
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  have hright_int : ∀ k ∈ Finset.range n,
      Integrable
        (fun records : M.canonicalRecordΩ =>
          (M.generatorDrift ((M.canonicalPathMap records).stateSeq k) i) ^ 2 /
            (M.exitRateAt ((M.canonicalPathMap records).stateSeq k)) ^ 2) μ := by
    intro k _hk
    exact (M.integrable_generatorDrift_div_exitRate_stateSeq_sq_canonicalRecordMeasure
      x₀ i k).congr
      (ae_of_all _ fun records => by
        ring)
  calc
    ∫ records,
        (M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n) ^ 2
        ∂M.canonicalRecordMeasure x₀
        = ∑ k ∈ Finset.range n,
            ∫ records,
              (M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i (k + 1) -
                M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k) ^ 2
              ∂M.canonicalRecordMeasure x₀ :=
          M.integral_scaledHoldingTimeDriftResidual_sq_eq_sum_increment_sq_of_noAbsorbing
            x₀ hNA i n
    _ = ∑ k ∈ Finset.range n,
          ∫ records,
            (M.generatorDrift ((M.canonicalPathMap records).stateSeq k) i) ^ 2 /
              (M.exitRateAt ((M.canonicalPathMap records).stateSeq k)) ^ 2
            ∂M.canonicalRecordMeasure x₀ := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          exact M.integral_residual_increment_sq_eq_integral_drift_sq_div_exit_sq
            x₀ hNA i k
    _ = ∫ records,
        (∑ k ∈ Finset.range n,
          (M.generatorDrift ((M.canonicalPathMap records).stateSeq k) i) ^ 2 /
            (M.exitRateAt ((M.canonicalPathMap records).stateSeq k)) ^ 2)
        ∂M.canonicalRecordMeasure x₀ := by
          rw [integral_finset_sum (Finset.range n)]
          exact hright_int

/-- Terminal L2 bound for the completed holding-time residual by the coordinate
QV compensator at a fixed embedded index. -/
theorem integral_scaledHoldingTimeDriftResidual_sq_le_integral_scaledCoordQVCompensator
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    ∫ records,
        (M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      ∫ records,
        M.scaledCoordQVCompensator (M.canonicalPathMap records) i n
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let S : M.canonicalRecordΩ → ℝ := fun records =>
    ∑ k ∈ Finset.range n,
      (M.generatorDrift ((M.canonicalPathMap records).stateSeq k) i) ^ 2 /
        (M.exitRateAt ((M.canonicalPathMap records).stateSeq k)) ^ 2
  have hS_int : Integrable S μ := by
    simp only [S]
    refine integrable_finset_sum (Finset.range n) ?_
    intro k _hk
    exact (M.integrable_generatorDrift_div_exitRate_stateSeq_sq_canonicalRecordMeasure
      x₀ i k).congr
      (ae_of_all _ fun records => by
        ring)
  have hQV_int :
      Integrable
        (fun records : M.canonicalRecordΩ =>
          M.scaledCoordQVCompensator (M.canonicalPathMap records) i n) μ := by
    simpa [μ] using M.integrable_scaledCoordQVCompensator_canonicalRecordMeasure x₀ i n
  have hle :
      ∀ᵐ records ∂μ,
        S records ≤ M.scaledCoordQVCompensator (M.canonicalPathMap records) i n := by
    refine ae_of_all _ fun records => ?_
    simpa [S] using
      M.sum_generatorDrift_sq_div_exitRateAt_sq_le_scaledCoordQVCompensator_of_noAbsorbing
        hNA (M.canonicalPathMap records) i n
  calc
    ∫ records,
        (M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n) ^ 2
        ∂M.canonicalRecordMeasure x₀
        = ∫ records, S records ∂μ := by
          simpa [S, μ] using
            M.integral_scaledHoldingTimeDriftResidual_sq_eq_integral_sum_drift_sq_div_exit_sq
              x₀ hNA i n
    _ ≤ ∫ records,
        M.scaledCoordQVCompensator (M.canonicalPathMap records) i n ∂μ :=
          integral_mono_ae hS_int hQV_int hle
    _ = ∫ records,
        M.scaledCoordQVCompensator (M.canonicalPathMap records) i n
        ∂M.canonicalRecordMeasure x₀ := by
          rfl

/-- The square of the completed holding-time residual is a nonnegative
submartingale along the embedded jump index. -/
theorem scaledHoldingTimeDriftResidual_sq_submartingale_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) (i : Fin d) :
    MeasureTheory.Submartingale
      (fun n records =>
        (M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n) ^ 2)
      M.canonicalRecordFiltration (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let Z : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n
  have hmart : MeasureTheory.Martingale Z M.canonicalRecordFiltration μ := by
    simpa [Z, μ] using
      M.scaledHoldingTimeDriftResidual_martingale_of_noAbsorbing x₀ hNA i
  refine MeasureTheory.submartingale_nat ?hadp ?hint ?hstep
  · intro n
    simpa [Z] using
      (M.stronglyAdapted_scaledHoldingTimeDriftResidual_canonicalRecordFiltration
        i n).pow 2
  · intro n
    simpa [Z] using
      M.integrable_scaledHoldingTimeDriftResidual_sq_canonicalRecordMeasure x₀ hNA i n
  · intro n
    have hcvx : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) := by
      simpa using (show Even (2 : ℕ) by norm_num).convexOn_pow (𝕜 := ℝ)
    have hJ :
        (fun records : M.canonicalRecordΩ =>
          ((μ[Z (n + 1) | M.canonicalRecordFiltration n]) records) ^ 2)
          ≤ᵐ[μ]
        μ[(fun records : M.canonicalRecordΩ => (Z (n + 1) records) ^ 2)
          | M.canonicalRecordFiltration n] := by
      simpa [Function.comp_def] using
        (ConvexOn.map_condExp_le_univ
          (μ := μ) (m := M.canonicalRecordFiltration n)
          (f := Z (n + 1)) (φ := fun x : ℝ => x ^ 2)
          (M.canonicalRecordFiltration.le n)
          hcvx (continuous_pow 2).lowerSemicontinuous
          (hmart.integrable (n + 1))
          (by
            simpa [Z] using
              M.integrable_scaledHoldingTimeDriftResidual_sq_canonicalRecordMeasure
                x₀ hNA i (n + 1)))
    have hcond : μ[Z (n + 1) | M.canonicalRecordFiltration n] =ᵐ[μ] Z n :=
      hmart.condExp_ae_eq (Nat.le_succ n)
    filter_upwards [hJ, hcond] with records hJrecords hcond_records
    simpa [Z, hcond_records] using hJrecords

/-- The norm of the completed holding-time residual is a nonnegative
submartingale along the embedded jump index. -/
theorem scaledHoldingTimeDriftResidual_norm_submartingale_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) (i : Fin d) :
    MeasureTheory.Submartingale
      (fun n records =>
        ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n‖)
      M.canonicalRecordFiltration (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let Z : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n
  have hmart : MeasureTheory.Martingale Z M.canonicalRecordFiltration μ := by
    simpa [Z, μ] using
      M.scaledHoldingTimeDriftResidual_martingale_of_noAbsorbing x₀ hNA i
  refine MeasureTheory.submartingale_nat ?hadp ?hint ?hstep
  · intro n
    simpa [Z] using
      (M.stronglyAdapted_scaledHoldingTimeDriftResidual_canonicalRecordFiltration
        i n).norm
  · intro n
    simpa [Z] using
      (M.integrable_scaledHoldingTimeDriftResidual_canonicalRecordMeasure
        x₀ hNA i n).norm
  · intro n
    have hJ :
        (fun records : M.canonicalRecordΩ =>
          ‖(μ[Z (n + 1) | M.canonicalRecordFiltration n]) records‖)
          ≤ᵐ[μ]
        μ[(fun records : M.canonicalRecordΩ => ‖Z (n + 1) records‖)
          | M.canonicalRecordFiltration n] :=
      AEStronglyMeasurable.norm_condExp_le
        (((M.stronglyAdapted_scaledHoldingTimeDriftResidual_canonicalRecordFiltration
          i (n + 1)).mono
          (M.canonicalRecordFiltration.le (n + 1))).aestronglyMeasurable)
    have hcond : μ[Z (n + 1) | M.canonicalRecordFiltration n] =ᵐ[μ] Z n :=
      hmart.condExp_ae_eq (Nat.le_succ n)
    filter_upwards [hJ, hcond] with records hJrecords hcond_records
    simpa [Z, hcond_records] using hJrecords

/-- Doob's available maximal inequality, specialized to the norm of the
completed holding-time residual. -/
theorem scaledHoldingTimeDriftResidual_norm_maximal_ineq_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (ε : NNReal) (n : ℕ) :
    ((ε : ENNReal) * (M.canonicalRecordMeasure x₀)
        {records | (ε : ℝ) ≤
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k =>
              ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖)})
      ≤ ENNReal.ofReal
        (∫ records in
          {records | (ε : ℝ) ≤
            (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
              (fun k =>
                ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖)},
          ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n‖
          ∂M.canonicalRecordMeasure x₀) := by
  exact MeasureTheory.maximal_ineq
    (M.scaledHoldingTimeDriftResidual_norm_submartingale_of_noAbsorbing x₀ hNA i)
    (by
      intro n records
      exact norm_nonneg _)
    (ε := ε) n

/-- The finite embedded-index supremum of the completed holding-time residual
has an integrable square. -/
theorem integrable_scaledHoldingTimeDriftResidual_sup_sq_canonicalRecordMeasure
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k =>
            ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖)) ^ 2)
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let R : ℕ → M.canonicalRecordΩ → ℝ := fun k records =>
    M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k
  let X : M.canonicalRecordΩ → ℝ := fun records =>
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ‖R k records‖)
  let Y : M.canonicalRecordΩ → ℝ := fun records =>
    ∑ k ∈ Finset.range (n + 1), ‖R k records‖
  have hX_meas : Measurable X := by
    exact Finset.measurable_range_sup'' (fun k _hk =>
      (((M.stronglyAdapted_scaledHoldingTimeDriftResidual_canonicalRecordFiltration
        i k).mono (M.canonicalRecordFiltration.le k)).measurable.norm))
  have hY_memLp : MemLp Y 2 μ := by
    dsimp [Y, R]
    refine memLp_finset_sum (Finset.range (n + 1)) ?_
    intro k _hk
    have hR_meas : AEStronglyMeasurable
        (fun records : M.canonicalRecordΩ =>
          M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k)
        μ :=
      (((M.stronglyAdapted_scaledHoldingTimeDriftResidual_canonicalRecordFiltration
        i k).mono (M.canonicalRecordFiltration.le k)).aestronglyMeasurable)
    have hR_memLp : MemLp
        (fun records : M.canonicalRecordΩ =>
          M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k)
        2 μ :=
      (memLp_two_iff_integrable_sq hR_meas).2
        (M.integrable_scaledHoldingTimeDriftResidual_sq_canonicalRecordMeasure
          x₀ hNA i k)
    simpa using hR_memLp.norm
  have hY_sq_int : Integrable (fun records => (Y records) ^ 2) μ :=
    hY_memLp.integrable_sq
  have hbound :
      ∀ᵐ records ∂μ, ‖X records ^ 2‖ ≤ Y records ^ 2 := by
    refine ae_of_all _ fun records => ?_
    have hX_nonneg : 0 ≤ X records := by
      dsimp [X]
      exact (norm_nonneg _).trans
        (Finset.le_sup'
          (fun k => ‖R k records‖)
          (Finset.mem_range.mpr (Nat.succ_pos n)))
    have hY_nonneg : 0 ≤ Y records := by
      dsimp [Y]
      exact Finset.sum_nonneg fun k _ => abs_nonneg _
    have hXY : X records ≤ Y records := by
      dsimp [X, Y]
      refine Finset.sup'_le _ _ ?_
      intro k hk
      exact Finset.single_le_sum
        (fun m _ => abs_nonneg (R m records)) hk
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (by nlinarith) hXY
  exact hY_sq_int.mono' (hX_meas.pow_const 2).aestronglyMeasurable hbound

/-- Finite jump-index Doob L2 layer-cake step for the completed holding-time
residual. -/
theorem integral_sup_residual_norm_sq_le_two_mul_sup_mul_norm_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    ∫ records,
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k =>
            ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖)) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      2 * ∫ records,
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k =>
            ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖) *
        ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n‖
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let X : M.canonicalRecordΩ → ℝ := fun records =>
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k =>
        ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖)
  let Y : M.canonicalRecordΩ → ℝ := fun records =>
    ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n‖
  have hX_meas : Measurable X := by
    exact Finset.measurable_range_sup'' (fun k _hk =>
      (((M.stronglyAdapted_scaledHoldingTimeDriftResidual_canonicalRecordFiltration
        i k).mono (M.canonicalRecordFiltration.le k)).measurable.norm))
  have hY_meas : Measurable Y :=
    (((M.stronglyAdapted_scaledHoldingTimeDriftResidual_canonicalRecordFiltration
      i n).mono (M.canonicalRecordFiltration.le n)).measurable.norm)
  have hX_nonneg : 0 ≤ᵐ[μ] X := by
    refine ae_of_all _ fun records => ?_
    dsimp [X]
    exact (norm_nonneg _).trans
      (Finset.le_sup'
        (fun k =>
          ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖)
        (Finset.mem_range.mpr (Nat.succ_pos n)))
  have hY_nonneg : 0 ≤ᵐ[μ] Y :=
    ae_of_all _ fun records => norm_nonneg _
  have hXsq_int : Integrable (fun records => X records ^ 2) μ := by
    simpa [X, μ] using
      M.integrable_scaledHoldingTimeDriftResidual_sup_sq_canonicalRecordMeasure
        x₀ hNA i n
  have hY_int : Integrable Y μ := by
    simpa [Y, μ] using
      (M.integrable_scaledHoldingTimeDriftResidual_canonicalRecordMeasure
        x₀ hNA i n).norm
  have hX_memLp_nat : MemLp X 2 μ :=
    (memLp_two_iff_integrable_sq hX_meas.aestronglyMeasurable).2 hXsq_int
  have hY_sq_int : Integrable (fun records => Y records ^ 2) μ := by
    have hterminal :=
      M.integrable_scaledHoldingTimeDriftResidual_sq_canonicalRecordMeasure
        x₀ hNA i n
    refine hterminal.congr ?_
    refine ae_of_all _ fun records => ?_
    dsimp [Y]
    exact (sq_abs
      (M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n)).symm
  have hY_memLp_nat : MemLp Y 2 μ :=
    (memLp_two_iff_integrable_sq hY_meas.aestronglyMeasurable).2 hY_sq_int
  have hXY_int : Integrable (fun records => X records * Y records) μ :=
    MemLp.integrable_mul hX_memLp_nat hY_memLp_nat
  have hMax : ∀ ε : NNReal,
      ((ε : ENNReal) * μ {records | (ε : ℝ) ≤ X records}) ≤
        ENNReal.ofReal (∫ records in {records | (ε : ℝ) ≤ X records},
          Y records ∂μ) := by
    intro ε
    simpa [X, Y, μ] using
      M.scaledHoldingTimeDriftResidual_norm_maximal_ineq_of_noAbsorbing
        x₀ hNA i ε n
  simpa [X, Y, μ] using
    integral_sq_le_two_integral_mul_of_maximal_ineq
      hX_meas hY_meas hX_nonneg hY_nonneg hXsq_int hY_int hXY_int hMax

/-- Cauchy/Hölder bound for the completed holding-time residual finite
supremum and terminal norm. -/
theorem integral_residual_sup_mul_terminal_norm_le_L2_mul_L2
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    ∫ records,
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k =>
            ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖) *
        ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n‖
        ∂M.canonicalRecordMeasure x₀ ≤
      (∫ records,
          ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k =>
              ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖)) ^ 2
          ∂M.canonicalRecordMeasure x₀) ^ ((1 : ℝ) / 2) *
        (∫ records,
          ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n‖ ^ 2
          ∂M.canonicalRecordMeasure x₀) ^ ((1 : ℝ) / 2) := by
  let μ := M.canonicalRecordMeasure x₀
  let X : M.canonicalRecordΩ → ℝ := fun records =>
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k =>
        ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖)
  let Y : M.canonicalRecordΩ → ℝ := fun records =>
    ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n‖
  have hX_meas : Measurable X := by
    exact Finset.measurable_range_sup'' (fun k _hk =>
      (((M.stronglyAdapted_scaledHoldingTimeDriftResidual_canonicalRecordFiltration
        i k).mono (M.canonicalRecordFiltration.le k)).measurable.norm))
  have hY_meas : Measurable Y :=
    (((M.stronglyAdapted_scaledHoldingTimeDriftResidual_canonicalRecordFiltration
      i n).mono (M.canonicalRecordFiltration.le n)).measurable.norm)
  have hX_nonneg : 0 ≤ᵐ[μ] X := by
    refine ae_of_all _ fun records => ?_
    dsimp [X]
    exact (norm_nonneg _).trans
      (Finset.le_sup'
        (fun k =>
          ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖)
        (Finset.mem_range.mpr (Nat.succ_pos n)))
  have hY_nonneg : 0 ≤ᵐ[μ] Y :=
    ae_of_all _ fun records => norm_nonneg _
  have hX_memLp_nat : MemLp X 2 μ :=
    (memLp_two_iff_integrable_sq hX_meas.aestronglyMeasurable).2
      (by
        simpa [X, μ] using
          M.integrable_scaledHoldingTimeDriftResidual_sup_sq_canonicalRecordMeasure
            x₀ hNA i n)
  have hX_memLp : MemLp X (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hX_memLp_nat
  have hY_sq_int : Integrable (fun records => Y records ^ 2) μ := by
    have hterminal :=
      M.integrable_scaledHoldingTimeDriftResidual_sq_canonicalRecordMeasure
        x₀ hNA i n
    refine hterminal.congr ?_
    refine ae_of_all _ fun records => ?_
    dsimp [Y]
    exact (sq_abs
      (M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n)).symm
  have hY_memLp_nat : MemLp Y 2 μ :=
    (memLp_two_iff_integrable_sq hY_meas.aestronglyMeasurable).2 hY_sq_int
  have hY_memLp : MemLp Y (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hY_memLp_nat
  have hholder :=
    integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := μ) Real.HolderConjugate.two_two
      hX_nonneg hY_nonneg hX_memLp hY_memLp
  simpa [X, Y, μ] using hholder

/-- Algebraic landing step for completed residual Doob L2 after layer-cake and
Cauchy. -/
theorem integral_residual_sup_sq_le_four_terminal_norm_sq_of_layercake
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ)
    (hLayer :
      ∫ records,
          ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k =>
              ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖)) ^ 2
          ∂M.canonicalRecordMeasure x₀ ≤
        2 * ∫ records,
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k =>
              ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖) *
          ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n‖
          ∂M.canonicalRecordMeasure x₀) :
    ∫ records,
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k =>
            ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖)) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      4 * ∫ records,
        ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ := by
  let A : ℝ :=
    ∫ records,
      ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k =>
          ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖)) ^ 2
      ∂M.canonicalRecordMeasure x₀
  let B : ℝ :=
    ∫ records,
      ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n‖ ^ 2
      ∂M.canonicalRecordMeasure x₀
  let C : ℝ :=
    ∫ records,
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k =>
          ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖) *
      ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n‖
      ∂M.canonicalRecordMeasure x₀
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun records => sq_nonneg _
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg fun records => sq_nonneg _
  have hCauchy : C ≤ A ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2) := by
    simpa [A, B, C] using
      M.integral_residual_sup_mul_terminal_norm_le_L2_mul_L2 x₀ hNA i n
  have hA_le_sqrt : A ≤ 2 * (Real.sqrt A * Real.sqrt B) := by
    have hA_le : A ≤ 2 * (A ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2)) := by
      exact hLayer.trans (mul_le_mul_of_nonneg_left hCauchy (by norm_num))
    simpa [Real.sqrt_eq_rpow] using hA_le
  have hsq_nonneg : 0 ≤ (Real.sqrt A - 2 * Real.sqrt B) ^ 2 :=
    sq_nonneg _
  have hsqrtA_sq : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA_nonneg
  have hsqrtB_sq : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB_nonneg
  change A ≤ 4 * B
  nlinarith [hA_le_sqrt, hsq_nonneg, hsqrtA_sq, hsqrtB_sq]

/-- Fixed embedded-index Doob/QV estimate for the completed holding-time
residual. -/
theorem integral_residual_sup_sq_le_scaledCoordQV_of_noAbsorbing_maximal
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    ∫ records,
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k =>
            ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖)) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      4 * ∫ records,
        M.scaledCoordQVCompensator (M.canonicalPathMap records) i n
        ∂M.canonicalRecordMeasure x₀ := by
  have hLayer :=
    M.integral_sup_residual_norm_sq_le_two_mul_sup_mul_norm_of_noAbsorbing
      x₀ hNA i n
  have hDoob :=
    M.integral_residual_sup_sq_le_four_terminal_norm_sq_of_layercake
      x₀ hNA i n hLayer
  have hterminal_eq :
      ∫ records,
          ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n‖ ^ 2
          ∂M.canonicalRecordMeasure x₀ =
        ∫ records,
          (M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n) ^ 2
          ∂M.canonicalRecordMeasure x₀ := by
    apply integral_congr_ae
    refine ae_of_all _ fun records => ?_
    change |M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n| ^ 2 =
      (M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n) ^ 2
    exact sq_abs (M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n)
  calc
    ∫ records,
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k =>
            ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖)) ^ 2
        ∂M.canonicalRecordMeasure x₀
        ≤ 4 * ∫ records,
          ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n‖ ^ 2
          ∂M.canonicalRecordMeasure x₀ := hDoob
    _ = 4 * ∫ records,
          (M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n) ^ 2
          ∂M.canonicalRecordMeasure x₀ := by rw [hterminal_eq]
    _ ≤ 4 * ∫ records,
        M.scaledCoordQVCompensator (M.canonicalPathMap records) i n
        ∂M.canonicalRecordMeasure x₀ := by
          exact mul_le_mul_of_nonneg_left
            (M.integral_scaledHoldingTimeDriftResidual_sq_le_integral_scaledCoordQVCompensator
              x₀ hNA i n)
            (by norm_num)

/-- Fixed-step compensator bridge: a predictable coordinate-QV rate times the
next raw holding time has expectation equal to the corresponding embedded
QV-compensator summand. -/
theorem integral_instantCoordQVRate_mul_next_holdingTime_eq_integral_div_exitRate
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    ∫ records,
        M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq n) i *
          (records (n + 1)).1
        ∂M.canonicalRecordMeasure x₀ =
      ∫ records,
        M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq n) i /
          M.exitRateAt ((M.canonicalPathMap records).stateSeq n)
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let A : M.canonicalRecordΩ → ℝ := fun records =>
    M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq n) i
  let Y : M.canonicalRecordΩ → ℝ := fun records => (records (n + 1)).1
  let B : M.canonicalRecordΩ → ℝ := fun records =>
    M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq n) i /
      M.exitRateAt ((M.canonicalPathMap records).stateSeq n)
  have hA_sm :
      StronglyMeasurable[M.canonicalRecordFiltration n] A :=
    (M.measurable_instantCoordQVRate_stateSeq_canonicalRecordFiltration
      i n).stronglyMeasurable
  have hY_int : Integrable Y μ := by
    simpa [Y, μ] using
      M.integrable_next_holdingTime_canonicalRecordMeasure_of_noAbsorbing x₀ hNA n
  have hAY_int : Integrable (fun records => A records * Y records) μ := by
    simpa [A, Y, μ] using
      M.integrable_instantCoordQVRate_mul_next_holdingTime x₀ hNA i n
  have hY_cond :
      μ[Y | M.canonicalRecordFiltration n] =ᵐ[μ]
        fun records => (M.exitRateAt ((M.canonicalPathMap records).stateSeq n))⁻¹ := by
    have h :=
      M.condExp_next_holdingTime_eq_inv_exitRate_of_noAbsorbing x₀ hNA n
    dsimp [μ, Y]
    rw [canonicalRecordFiltration,
      QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe]
    simpa using h
  have hpull :
      μ[(fun records => A records * Y records) | M.canonicalRecordFiltration n]
        =ᵐ[μ]
      fun records => A records * (μ[Y | M.canonicalRecordFiltration n]) records := by
    exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      hA_sm hAY_int hY_int
  have hcond_prod :
      μ[(fun records => A records * Y records) | M.canonicalRecordFiltration n]
        =ᵐ[μ] B := by
    filter_upwards [hpull, hY_cond] with records hpull_records hY_records
    rw [hpull_records, hY_records]
    simp [A, B, div_eq_mul_inv]
  calc
    ∫ records, A records * Y records ∂μ
        = ∫ records,
            (μ[(fun records => A records * Y records) |
              M.canonicalRecordFiltration n]) records ∂μ := by
            exact (integral_condExp
              (μ := μ)
              (m := M.canonicalRecordFiltration n)
              (f := fun records => A records * Y records)
              (M.canonicalRecordFiltration.le n)).symm
    _ = ∫ records, B records ∂μ := by
          exact integral_congr_ae hcond_prod
    _ = ∫ records,
        M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq n) i /
          M.exitRateAt ((M.canonicalPathMap records).stateSeq n)
        ∂M.canonicalRecordMeasure x₀ := by
          simp [B, μ]

/-- Fixed finite-sum compensator bridge: summing the predictable-coordinate-QV
holding-time identity gives the embedded coordinate QV compensator. -/
theorem integral_sum_instantCoordQVRate_mul_next_holdingTime_eq_integral_qvComp
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    ∫ records,
        (∑ k ∈ Finset.range n,
          M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
            (records (k + 1)).1)
        ∂M.canonicalRecordMeasure x₀ =
      ∫ records,
        M.scaledCoordQVCompensator (M.canonicalPathMap records) i n
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  have hleft_int : ∀ k ∈ Finset.range n,
      Integrable
        (fun records : M.canonicalRecordΩ =>
          M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
            (records (k + 1)).1) μ := by
    intro k _hk
    simpa [μ] using
      M.integrable_instantCoordQVRate_mul_next_holdingTime x₀ hNA i k
  have hright_int : ∀ k ∈ Finset.range n,
      Integrable
        (fun records : M.canonicalRecordΩ =>
          M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i /
            M.exitRateAt ((M.canonicalPathMap records).stateSeq k)) μ := by
    intro k _hk
    simpa [μ] using
      M.integrable_instantCoordQVRate_div_exitRate_stateSeq_canonicalRecordMeasure
        x₀ i k
  calc
    ∫ records,
        (∑ k ∈ Finset.range n,
          M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
            (records (k + 1)).1) ∂μ
        = ∑ k ∈ Finset.range n,
            ∫ records,
              M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
                (records (k + 1)).1 ∂μ := by
            rw [integral_finset_sum (Finset.range n)]
            exact hleft_int
    _ = ∑ k ∈ Finset.range n,
          ∫ records,
            M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i /
              M.exitRateAt ((M.canonicalPathMap records).stateSeq k) ∂μ := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          simpa [μ] using
            M.integral_instantCoordQVRate_mul_next_holdingTime_eq_integral_div_exitRate
              x₀ hNA i k
    _ = ∫ records,
        (∑ k ∈ Finset.range n,
          M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i /
            M.exitRateAt ((M.canonicalPathMap records).stateSeq k)) ∂μ := by
          rw [integral_finset_sum (Finset.range n)]
          exact hright_int
    _ = ∫ records,
        M.scaledCoordQVCompensator (M.canonicalPathMap records) i n
        ∂M.canonicalRecordMeasure x₀ := by
          simp [scaledCoordQVCompensator, μ]

/-- Path-language version of the fixed finite-sum compensator bridge, using
the sojourn time of each `stateSeq` entry. -/
theorem integral_sum_instantCoordQVRate_mul_sojournTime_eq_integral_qvComp
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    ∫ records,
        (∑ k ∈ Finset.range n,
          M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
            (M.canonicalPathMap records).sojournTime k)
        ∂M.canonicalRecordMeasure x₀ =
      ∫ records,
        M.scaledCoordQVCompensator (M.canonicalPathMap records) i n
        ∂M.canonicalRecordMeasure x₀ := by
  simpa [canonicalPathMap, QMatrix.recordTrajectoryToPath_sojournTime] using
    M.integral_sum_instantCoordQVRate_mul_next_holdingTime_eq_integral_qvComp
      x₀ hNA i n

/-- The centered coordinate jump-sum process is strongly adapted. -/
theorem stronglyAdapted_scaledJumpMartingale_canonicalRecordFiltration
    (i : Fin d) :
    MeasureTheory.StronglyAdapted M.canonicalRecordFiltration
      (fun n records =>
        M.scaledJumpMartingale (M.canonicalPathMap records) i n) :=
  (M.stronglyAdapted_scaledJumpSum_apply_canonicalRecordFiltration i).sub
    (M.stronglyAdapted_scaledJumpDriftCompensator_canonicalRecordFiltration i)

/-- The centered coordinate squared-jump process is strongly adapted. -/
theorem stronglyAdapted_scaledCoordJumpSqMartingale_canonicalRecordFiltration
    (i : Fin d) :
    MeasureTheory.StronglyAdapted M.canonicalRecordFiltration
      (fun n records =>
        M.scaledCoordJumpSqMartingale (M.canonicalPathMap records) i n) :=
  (M.stronglyAdapted_scaledCoordJumpSqSum_canonicalRecordFiltration i).sub
    (M.stronglyAdapted_scaledCoordQVCompensator_canonicalRecordFiltration i)

/-- The centered coordinate jump-sum process is integrable at every jump
index. -/
theorem integrable_scaledJumpMartingale_canonicalRecordMeasure
    (x₀ : Fin d → Fin (M.N + 1)) (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.scaledJumpMartingale (M.canonicalPathMap records) i n)
      (M.canonicalRecordMeasure x₀) :=
  (M.integrable_scaledJumpSum_apply_canonicalRecordMeasure x₀ i n).sub
    (M.integrable_scaledJumpDriftCompensator_canonicalRecordMeasure x₀ i n)

/-- The square of the centered coordinate jump-sum process is integrable at
every jump index. -/
theorem integrable_scaledJumpMartingale_sq_canonicalRecordMeasure
    (x₀ : Fin d → Fin (M.N + 1)) (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        (M.scaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2)
      (M.canonicalRecordMeasure x₀) := by
  obtain ⟨C, hC⟩ := M.exists_generatorDrift_div_exitRate_bound i
  have hC_nonneg : 0 ≤ C := by
    let x : Fin d → Fin (M.N + 1) := Classical.arbitrary _
    exact (norm_nonneg (M.generatorDrift x i / M.exitRateAt x)).trans (hC x)
  let B : ℝ := (n : ℝ) * 2 + (n : ℝ) * C
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (by norm_num))
      (mul_nonneg (Nat.cast_nonneg _) hC_nonneg)
  refine Integrable.of_bound
    (((M.stronglyAdapted_scaledJumpMartingale_canonicalRecordFiltration i n).mono
      (M.canonicalRecordFiltration.le n)).pow 2).aestronglyMeasurable
    (B ^ 2) ?_
  refine ae_of_all _ fun records => ?_
  have hsum :
      ‖M.scaledJumpSum (M.canonicalPathMap records) n i‖ ≤ (n : ℝ) * 2 := by
    simp only [scaledJumpSum]
    calc
      ‖∑ k ∈ Finset.range n,
          (M.scaledState ((M.canonicalPathMap records).stateSeq (k + 1)) -
            M.scaledState ((M.canonicalPathMap records).stateSeq k)) i‖
          ≤ ∑ k ∈ Finset.range n,
              ‖(M.scaledState ((M.canonicalPathMap records).stateSeq (k + 1)) -
                M.scaledState ((M.canonicalPathMap records).stateSeq k)) i‖ :=
            norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range n, (2 : ℝ) := by
            exact Finset.sum_le_sum fun k _ =>
              M.scaledState_sub_apply_norm_le_two
                ((M.canonicalPathMap records).stateSeq k)
                ((M.canonicalPathMap records).stateSeq (k + 1)) i
      _ = (n : ℝ) * 2 := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hcomp :
      ‖M.scaledJumpDriftCompensator (M.canonicalPathMap records) i n‖ ≤
        (n : ℝ) * C := by
    simp only [scaledJumpDriftCompensator]
    calc
      ‖∑ k ∈ Finset.range n,
          M.generatorDrift ((M.canonicalPathMap records).stateSeq k) i /
            M.exitRateAt ((M.canonicalPathMap records).stateSeq k)‖
          ≤ ∑ k ∈ Finset.range n,
              ‖M.generatorDrift ((M.canonicalPathMap records).stateSeq k) i /
                M.exitRateAt ((M.canonicalPathMap records).stateSeq k)‖ :=
            norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range n, C := by
            exact Finset.sum_le_sum fun k _ =>
              hC ((M.canonicalPathMap records).stateSeq k)
      _ = (n : ℝ) * C := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hZ :
      ‖M.scaledJumpMartingale (M.canonicalPathMap records) i n‖ ≤ B := by
    dsimp [B]
    calc
      ‖M.scaledJumpMartingale (M.canonicalPathMap records) i n‖
          = ‖M.scaledJumpSum (M.canonicalPathMap records) n i -
              M.scaledJumpDriftCompensator (M.canonicalPathMap records) i n‖ := rfl
      _ ≤ ‖M.scaledJumpSum (M.canonicalPathMap records) n i‖ +
            ‖M.scaledJumpDriftCompensator (M.canonicalPathMap records) i n‖ :=
          norm_sub_le _ _
      _ ≤ (n : ℝ) * 2 + (n : ℝ) * C := by gcongr
  change ‖(M.scaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2‖ ≤ B ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [Real.norm_eq_abs] at hZ
  rw [← sq_abs]
  have hlow :
      -B ≤ |M.scaledJumpMartingale (M.canonicalPathMap records) i n| := by
    nlinarith [hB_nonneg,
      abs_nonneg (M.scaledJumpMartingale (M.canonicalPathMap records) i n)]
  exact sq_le_sq' hlow hZ

/-- The finite jump-index supremum of the centered coordinate martingale has
an integrable square.  This supplies the real-integrability side of the
finite-time Doob L2 estimate. -/
theorem integrable_scaledJumpMartingale_sup_sq_canonicalRecordMeasure
    (x₀ : Fin d → Fin (M.N + 1)) (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2)
      (M.canonicalRecordMeasure x₀) := by
  obtain ⟨C, hC⟩ := M.exists_generatorDrift_div_exitRate_bound i
  have hC_nonneg : 0 ≤ C := by
    let x : Fin d → Fin (M.N + 1) := Classical.arbitrary _
    exact (norm_nonneg (M.generatorDrift x i / M.exitRateAt x)).trans (hC x)
  let B : ℝ := (n : ℝ) * 2 + (n : ℝ) * C
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (by norm_num))
      (mul_nonneg (Nat.cast_nonneg _) hC_nonneg)
  have hmeas :
      Measurable (fun records : M.canonicalRecordΩ =>
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2) := by
    exact (Finset.measurable_range_sup'' (fun k _hk =>
      (((M.stronglyAdapted_scaledJumpMartingale_canonicalRecordFiltration i k).mono
        (M.canonicalRecordFiltration.le k)).measurable.norm))).pow_const 2
  refine Integrable.of_bound hmeas.aestronglyMeasurable (B ^ 2) ?_
  refine ae_of_all _ fun records => ?_
  have hsup_le :
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖) ≤ B := by
    refine Finset.sup'_le _ _ ?_
    intro k hk
    have hk_le_n : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hsum :
        ‖M.scaledJumpSum (M.canonicalPathMap records) k i‖ ≤ (k : ℝ) * 2 := by
      simp only [scaledJumpSum]
      calc
        ‖∑ m ∈ Finset.range k,
            (M.scaledState ((M.canonicalPathMap records).stateSeq (m + 1)) -
              M.scaledState ((M.canonicalPathMap records).stateSeq m)) i‖
            ≤ ∑ m ∈ Finset.range k,
                ‖(M.scaledState ((M.canonicalPathMap records).stateSeq (m + 1)) -
                  M.scaledState ((M.canonicalPathMap records).stateSeq m)) i‖ :=
              norm_sum_le _ _
        _ ≤ ∑ _m ∈ Finset.range k, (2 : ℝ) := by
              exact Finset.sum_le_sum fun m _ =>
                M.scaledState_sub_apply_norm_le_two
                  ((M.canonicalPathMap records).stateSeq m)
                  ((M.canonicalPathMap records).stateSeq (m + 1)) i
        _ = (k : ℝ) * 2 := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hcomp :
        ‖M.scaledJumpDriftCompensator (M.canonicalPathMap records) i k‖ ≤
          (k : ℝ) * C := by
      simp only [scaledJumpDriftCompensator]
      calc
        ‖∑ m ∈ Finset.range k,
            M.generatorDrift ((M.canonicalPathMap records).stateSeq m) i /
              M.exitRateAt ((M.canonicalPathMap records).stateSeq m)‖
            ≤ ∑ m ∈ Finset.range k,
                ‖M.generatorDrift ((M.canonicalPathMap records).stateSeq m) i /
                  M.exitRateAt ((M.canonicalPathMap records).stateSeq m)‖ :=
              norm_sum_le _ _
        _ ≤ ∑ _m ∈ Finset.range k, C := by
              exact Finset.sum_le_sum fun m _ =>
                hC ((M.canonicalPathMap records).stateSeq m)
        _ = (k : ℝ) * C := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hZ :
        ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖ ≤
          (k : ℝ) * 2 + (k : ℝ) * C := by
      calc
        ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖
            = ‖M.scaledJumpSum (M.canonicalPathMap records) k i -
                M.scaledJumpDriftCompensator (M.canonicalPathMap records) i k‖ := rfl
        _ ≤ ‖M.scaledJumpSum (M.canonicalPathMap records) k i‖ +
              ‖M.scaledJumpDriftCompensator (M.canonicalPathMap records) i k‖ :=
            norm_sub_le _ _
        _ ≤ (k : ℝ) * 2 + (k : ℝ) * C := by gcongr
    have hk_real : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk_le_n
    have hterm₁ : (k : ℝ) * 2 ≤ (n : ℝ) * 2 :=
      mul_le_mul_of_nonneg_right hk_real (by norm_num)
    have hterm₂ : (k : ℝ) * C ≤ (n : ℝ) * C :=
      mul_le_mul_of_nonneg_right hk_real hC_nonneg
    exact hZ.trans (by
      dsimp [B]
      linarith)
  have hsup_nonneg :
      0 ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖) := by
    exact (norm_nonneg _).trans
      (Finset.le_sup'
        (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)
        (Finset.mem_range.mpr (Nat.succ_pos n)))
  change ‖((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2‖ ≤ B ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith

/-- Cauchy/Hölder bound for the finite jump-index supremum and the terminal
coordinate martingale norm.  This is the Cauchy side of the standard Doob L2
argument after the layer-cake/maximal-inequality step has reduced the estimate
to `∫ sup |M| * |M_n|`. -/
theorem integral_scaledJumpMartingale_sup_mul_terminal_norm_le_L2_mul_L2
    (x₀ : Fin d → Fin (M.N + 1)) (i : Fin d) (n : ℕ) :
    ∫ records,
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖) *
        ‖M.scaledJumpMartingale (M.canonicalPathMap records) i n‖
        ∂M.canonicalRecordMeasure x₀ ≤
      (∫ records,
          ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2
          ∂M.canonicalRecordMeasure x₀) ^ ((1 : ℝ) / 2) *
        (∫ records,
          ‖M.scaledJumpMartingale (M.canonicalPathMap records) i n‖ ^ 2
          ∂M.canonicalRecordMeasure x₀) ^ ((1 : ℝ) / 2) := by
  let μ := M.canonicalRecordMeasure x₀
  let X : M.canonicalRecordΩ → ℝ := fun records =>
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)
  let Y : M.canonicalRecordΩ → ℝ := fun records =>
    ‖M.scaledJumpMartingale (M.canonicalPathMap records) i n‖
  have hX_meas : Measurable X := by
    exact Finset.measurable_range_sup'' (fun k _hk =>
      (((M.stronglyAdapted_scaledJumpMartingale_canonicalRecordFiltration i k).mono
        (M.canonicalRecordFiltration.le k)).measurable.norm))
  have hY_meas : Measurable Y :=
    (((M.stronglyAdapted_scaledJumpMartingale_canonicalRecordFiltration i n).mono
      (M.canonicalRecordFiltration.le n)).measurable.norm)
  have hX_nonneg : 0 ≤ᵐ[μ] X := by
    refine ae_of_all _ fun records => ?_
    dsimp [X]
    exact (norm_nonneg _).trans
      (Finset.le_sup'
        (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)
        (Finset.mem_range.mpr (Nat.succ_pos n)))
  have hY_nonneg : 0 ≤ᵐ[μ] Y :=
    ae_of_all _ fun records => norm_nonneg _
  have hX_memLp_nat : MemLp X 2 μ := by
    exact (memLp_two_iff_integrable_sq hX_meas.aestronglyMeasurable).2
      (by
        simpa [X, μ] using
          M.integrable_scaledJumpMartingale_sup_sq_canonicalRecordMeasure x₀ i n)
  have hX_memLp : MemLp X (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hX_memLp_nat
  have hY_sq_int : Integrable (fun records => Y records ^ 2) μ := by
    have hterminal :=
      M.integrable_scaledJumpMartingale_sq_canonicalRecordMeasure x₀ i n
    refine hterminal.congr ?_
    refine ae_of_all _ fun records => ?_
    dsimp [Y]
    exact (sq_abs (M.scaledJumpMartingale (M.canonicalPathMap records) i n)).symm
  have hY_memLp_nat : MemLp Y 2 μ := by
    exact (memLp_two_iff_integrable_sq hY_meas.aestronglyMeasurable).2 hY_sq_int
  have hY_memLp : MemLp Y (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hY_memLp_nat
  have hholder :=
    integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := μ) Real.HolderConjugate.two_two
      hX_nonneg hY_nonneg hX_memLp hY_memLp
  simpa [X, Y, μ] using hholder

/-- Algebraic landing step for Doob L2 after layer-cake and Cauchy: if the
maximal inequality/layer-cake part proves `E X^2 ≤ 2 E[X Y]`, then the
Cauchy wrapper upgrades it to `E X^2 ≤ 4 E Y^2`. -/
theorem integral_scaledJumpMartingale_sup_sq_le_four_terminal_norm_sq_of_layercake
    (x₀ : Fin d → Fin (M.N + 1)) (i : Fin d) (n : ℕ)
    (hLayer :
      ∫ records,
          ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2
          ∂M.canonicalRecordMeasure x₀ ≤
        2 * ∫ records,
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖) *
          ‖M.scaledJumpMartingale (M.canonicalPathMap records) i n‖
          ∂M.canonicalRecordMeasure x₀) :
    ∫ records,
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      4 * ∫ records,
        ‖M.scaledJumpMartingale (M.canonicalPathMap records) i n‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ := by
  let A : ℝ :=
    ∫ records,
      ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2
      ∂M.canonicalRecordMeasure x₀
  let B : ℝ :=
    ∫ records,
      ‖M.scaledJumpMartingale (M.canonicalPathMap records) i n‖ ^ 2
      ∂M.canonicalRecordMeasure x₀
  let C : ℝ :=
    ∫ records,
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖) *
      ‖M.scaledJumpMartingale (M.canonicalPathMap records) i n‖
      ∂M.canonicalRecordMeasure x₀
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun records => sq_nonneg _
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg fun records => sq_nonneg _
  have hCauchy : C ≤ A ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2) := by
    simpa [A, B, C] using
      M.integral_scaledJumpMartingale_sup_mul_terminal_norm_le_L2_mul_L2 x₀ i n
  have hA_le_sqrt : A ≤ 2 * (Real.sqrt A * Real.sqrt B) := by
    have hA_le : A ≤ 2 * (A ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2)) := by
      exact hLayer.trans (mul_le_mul_of_nonneg_left hCauchy (by norm_num))
    simpa [Real.sqrt_eq_rpow] using hA_le
  have hsq_nonneg : 0 ≤ (Real.sqrt A - 2 * Real.sqrt B) ^ 2 :=
    sq_nonneg _
  have hsqrtA_sq : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA_nonneg
  have hsqrtB_sq : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB_nonneg
  change A ≤ 4 * B
  nlinarith [hA_le_sqrt, hsq_nonneg, hsqrtA_sq, hsqrtB_sq]

/-- The centered coordinate squared-jump process is integrable at every jump
index. -/
theorem integrable_scaledCoordJumpSqMartingale_canonicalRecordMeasure
    (x₀ : Fin d → Fin (M.N + 1)) (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.scaledCoordJumpSqMartingale (M.canonicalPathMap records) i n)
      (M.canonicalRecordMeasure x₀) :=
  (M.integrable_scaledCoordJumpSqSum_canonicalRecordMeasure x₀ i n).sub
    (M.integrable_scaledCoordQVCompensator_canonicalRecordMeasure x₀ i n)

/-- One-step increment of the centered coordinate jump-sum process. -/
theorem scaledJumpMartingale_succ_sub
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) :
    M.scaledJumpMartingale path i (n + 1) - M.scaledJumpMartingale path i n =
      (M.scaledState (path.stateSeq (n + 1)) -
          M.scaledState (path.stateSeq n)) i -
        M.generatorDrift (path.stateSeq n) i / M.exitRateAt (path.stateSeq n) := by
  simp only [scaledJumpMartingale, scaledJumpSum, scaledJumpDriftCompensator,
    Finset.sum_range_succ]
  ring

/-- One-step increment of the centered coordinate squared-jump process. -/
theorem scaledCoordJumpSqMartingale_succ_sub
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) :
    M.scaledCoordJumpSqMartingale path i (n + 1) -
        M.scaledCoordJumpSqMartingale path i n =
      ((M.scaledState (path.stateSeq (n + 1)) -
          M.scaledState (path.stateSeq n)) i) ^ 2 -
        M.instantCoordQVRate (path.stateSeq n) i / M.exitRateAt (path.stateSeq n) := by
  simp only [scaledCoordJumpSqMartingale, scaledCoordJumpSqSum, scaledCoordQVCompensator,
    Finset.sum_range_succ]
  ring

/-- The centered coordinate jump-sum has zero conditional expected increment
with respect to the canonical record filtration. -/
theorem condExp_scaledJumpMartingale_increment_eq_zero_ae_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (n : ℕ) (i : Fin d) :
    (M.canonicalRecordMeasure x₀)[
      (fun records : M.canonicalRecordΩ =>
        M.scaledJumpMartingale (M.canonicalPathMap records) i (n + 1) -
          M.scaledJumpMartingale (M.canonicalPathMap records) i n)
      | M.canonicalRecordFiltration n] =ᵐ[M.canonicalRecordMeasure x₀] 0 := by
  let μ := M.canonicalRecordMeasure x₀
  let nextJump : M.canonicalRecordΩ → ℝ := fun records =>
    (M.scaledState ((records (n + 1)).2) -
      M.scaledState ((M.canonicalPathMap records).stateSeq n)) i
  let comp : M.canonicalRecordΩ → ℝ := fun records =>
    M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i /
      M.exitRateAt ((M.canonicalPathMap records).stateSeq n)
  have hinc :
      (fun records : M.canonicalRecordΩ =>
        M.scaledJumpMartingale (M.canonicalPathMap records) i (n + 1) -
          M.scaledJumpMartingale (M.canonicalPathMap records) i n)
        =ᵐ[μ] fun records => nextJump records - comp records := by
    refine ae_of_all _ fun records => ?_
    simp [nextJump, comp, M.scaledJumpMartingale_succ_sub, canonicalPathMap,
      QMatrix.recordTrajectoryToPath_stateSeq]
  have hnext :
      μ[nextJump | M.canonicalRecordFiltration n] =ᵐ[μ] comp := by
    have h :=
      M.condExp_next_scaledState_sub_apply_eq_generatorDrift_div_exitRate_ae_of_noAbsorbing
        x₀ hNA n i
    dsimp [μ, nextJump, comp]
    rw [canonicalRecordFiltration,
      QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe]
    simpa [Pi.sub_apply] using h
  have hcomp :
      μ[comp | M.canonicalRecordFiltration n] = comp := by
    exact MeasureTheory.condExp_of_stronglyMeasurable
      (M.canonicalRecordFiltration.le n)
      (M.measurable_generatorDrift_div_exitRate_stateSeq_canonicalRecordFiltration
        i n).stronglyMeasurable
      (M.integrable_generatorDrift_div_exitRate_stateSeq_canonicalRecordMeasure x₀ i n)
  have hsub :
      μ[nextJump - comp | M.canonicalRecordFiltration n] =ᵐ[μ]
        μ[nextJump | M.canonicalRecordFiltration n] -
          μ[comp | M.canonicalRecordFiltration n] :=
    MeasureTheory.condExp_sub
      (M.integrable_next_scaledState_sub_apply x₀ n i)
      (M.integrable_generatorDrift_div_exitRate_stateSeq_canonicalRecordMeasure x₀ i n)
      (M.canonicalRecordFiltration n)
  refine (MeasureTheory.condExp_congr_ae hinc).trans ?_
  change μ[nextJump - comp | M.canonicalRecordFiltration n] =ᵐ[μ] 0
  rw [hcomp] at hsub
  filter_upwards [hsub, hnext] with records hsub_eq hnext_eq
  rw [hsub_eq]
  simp [Pi.sub_apply, hnext_eq]

/-- The centered coordinate jump-sum process is a martingale along the embedded
jump index under the canonical non-absorbing record law. -/
theorem scaledJumpMartingale_martingale_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) (i : Fin d) :
    MeasureTheory.Martingale
      (fun n records =>
        M.scaledJumpMartingale (M.canonicalPathMap records) i n)
      M.canonicalRecordFiltration (M.canonicalRecordMeasure x₀) :=
  MeasureTheory.martingale_of_condExp_sub_eq_zero_nat
    (M.stronglyAdapted_scaledJumpMartingale_canonicalRecordFiltration i)
    (M.integrable_scaledJumpMartingale_canonicalRecordMeasure x₀ i)
    (fun n => M.condExp_scaledJumpMartingale_increment_eq_zero_ae_of_noAbsorbing
      x₀ hNA n i)

/-- The square of the centered coordinate jump-sum is a nonnegative
submartingale along the embedded jump index.  This is the input needed to use
Mathlib's available Doob maximal inequality. -/
theorem scaledJumpMartingale_sq_submartingale_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) (i : Fin d) :
    MeasureTheory.Submartingale
      (fun n records =>
        (M.scaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2)
      M.canonicalRecordFiltration (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let Z : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.scaledJumpMartingale (M.canonicalPathMap records) i n
  have hmart : MeasureTheory.Martingale Z M.canonicalRecordFiltration μ := by
    simpa [Z, μ] using M.scaledJumpMartingale_martingale_of_noAbsorbing x₀ hNA i
  refine MeasureTheory.submartingale_nat ?hadp ?hint ?hstep
  · intro n
    simpa [Z] using
      (M.stronglyAdapted_scaledJumpMartingale_canonicalRecordFiltration i n).pow 2
  · intro n
    simpa [Z] using
      M.integrable_scaledJumpMartingale_sq_canonicalRecordMeasure x₀ i n
  · intro n
    have hcvx : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) := by
      simpa using (show Even (2 : ℕ) by norm_num).convexOn_pow (𝕜 := ℝ)
    have hJ :
        (fun records : M.canonicalRecordΩ =>
          ((μ[Z (n + 1) | M.canonicalRecordFiltration n]) records) ^ 2)
          ≤ᵐ[μ]
        μ[(fun records : M.canonicalRecordΩ => (Z (n + 1) records) ^ 2)
          | M.canonicalRecordFiltration n] := by
      simpa [Function.comp_def] using
        (ConvexOn.map_condExp_le_univ
          (μ := μ) (m := M.canonicalRecordFiltration n)
          (f := Z (n + 1)) (φ := fun x : ℝ => x ^ 2)
          (M.canonicalRecordFiltration.le n)
          hcvx (continuous_pow 2).lowerSemicontinuous
          (hmart.integrable (n + 1))
          (by
            simpa [Z] using
              M.integrable_scaledJumpMartingale_sq_canonicalRecordMeasure x₀ i (n + 1)))
    have hcond : μ[Z (n + 1) | M.canonicalRecordFiltration n] =ᵐ[μ] Z n :=
      hmart.condExp_ae_eq (Nat.le_succ n)
    filter_upwards [hJ, hcond] with records hJrecords hcond_records
    simpa [Z, hcond_records] using hJrecords

/-- Doob's available Mathlib maximal inequality, specialized to the square of
the centered coordinate jump-sum martingale. -/
theorem scaledJumpMartingale_sq_maximal_ineq_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (ε : NNReal) (n : ℕ) :
    ((ε : ENNReal) * (M.canonicalRecordMeasure x₀)
        {records | (ε : ℝ) ≤
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k => (M.scaledJumpMartingale (M.canonicalPathMap records) i k) ^ 2)})
      ≤ ENNReal.ofReal
        (∫ records in
          {records | (ε : ℝ) ≤
            (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
              (fun k => (M.scaledJumpMartingale (M.canonicalPathMap records) i k) ^ 2)},
          (M.scaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2
          ∂M.canonicalRecordMeasure x₀) := by
  exact MeasureTheory.maximal_ineq
    (M.scaledJumpMartingale_sq_submartingale_of_noAbsorbing x₀ hNA i)
    (by
      intro n records
      exact sq_nonneg _)
    (ε := ε) n

/-- The norm of the centered coordinate jump-sum is a nonnegative
submartingale along the embedded jump index.  This is the standard input for
deriving Doob's L2 inequality from the weak maximal inequality. -/
theorem scaledJumpMartingale_norm_submartingale_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) (i : Fin d) :
    MeasureTheory.Submartingale
      (fun n records =>
        ‖M.scaledJumpMartingale (M.canonicalPathMap records) i n‖)
      M.canonicalRecordFiltration (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let Z : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.scaledJumpMartingale (M.canonicalPathMap records) i n
  have hmart : MeasureTheory.Martingale Z M.canonicalRecordFiltration μ := by
    simpa [Z, μ] using M.scaledJumpMartingale_martingale_of_noAbsorbing x₀ hNA i
  refine MeasureTheory.submartingale_nat ?hadp ?hint ?hstep
  · intro n
    simpa [Z] using
      (M.stronglyAdapted_scaledJumpMartingale_canonicalRecordFiltration i n).norm
  · intro n
    simpa [Z] using
      (M.integrable_scaledJumpMartingale_canonicalRecordMeasure x₀ i n).norm
  · intro n
    have hJ :
        (fun records : M.canonicalRecordΩ =>
          ‖(μ[Z (n + 1) | M.canonicalRecordFiltration n]) records‖)
          ≤ᵐ[μ]
        μ[(fun records : M.canonicalRecordΩ => ‖Z (n + 1) records‖)
          | M.canonicalRecordFiltration n] :=
      AEStronglyMeasurable.norm_condExp_le
        (((M.stronglyAdapted_scaledJumpMartingale_canonicalRecordFiltration i (n + 1)).mono
          (M.canonicalRecordFiltration.le (n + 1))).aestronglyMeasurable)
    have hcond : μ[Z (n + 1) | M.canonicalRecordFiltration n] =ᵐ[μ] Z n :=
      hmart.condExp_ae_eq (Nat.le_succ n)
    filter_upwards [hJ, hcond] with records hJrecords hcond_records
    simpa [Z, hcond_records] using hJrecords

/-- Doob's available Mathlib maximal inequality, specialized to the norm of
the centered coordinate jump-sum martingale. -/
theorem scaledJumpMartingale_norm_maximal_ineq_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (ε : NNReal) (n : ℕ) :
    ((ε : ENNReal) * (M.canonicalRecordMeasure x₀)
        {records | (ε : ℝ) ≤
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)})
      ≤ ENNReal.ofReal
        (∫ records in
          {records | (ε : ℝ) ≤
            (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
              (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)},
          ‖M.scaledJumpMartingale (M.canonicalPathMap records) i n‖
          ∂M.canonicalRecordMeasure x₀) := by
  exact MeasureTheory.maximal_ineq
    (M.scaledJumpMartingale_norm_submartingale_of_noAbsorbing x₀ hNA i)
    (by
      intro n records
      exact norm_nonneg _)
    (ε := ε) n

/-- Finite jump-index Doob L2 layer-cake step for the centered coordinate
jump-sum martingale.  This is the missing integration step between Mathlib's
maximal inequality and the Cauchy/algebraic L2 landing below. -/
theorem integral_sup_scaledJumpMartingale_norm_sq_le_two_mul_sup_mul_norm_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    ∫ records,
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      2 * ∫ records,
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖) *
        ‖M.scaledJumpMartingale (M.canonicalPathMap records) i n‖
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let X : M.canonicalRecordΩ → ℝ := fun records =>
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)
  let Y : M.canonicalRecordΩ → ℝ := fun records =>
    ‖M.scaledJumpMartingale (M.canonicalPathMap records) i n‖
  have hX_meas : Measurable X := by
    exact Finset.measurable_range_sup'' (fun k _hk =>
      (((M.stronglyAdapted_scaledJumpMartingale_canonicalRecordFiltration i k).mono
        (M.canonicalRecordFiltration.le k)).measurable.norm))
  have hY_meas : Measurable Y :=
    (((M.stronglyAdapted_scaledJumpMartingale_canonicalRecordFiltration i n).mono
      (M.canonicalRecordFiltration.le n)).measurable.norm)
  have hX_nonneg : 0 ≤ᵐ[μ] X := by
    refine ae_of_all _ fun records => ?_
    dsimp [X]
    exact (norm_nonneg _).trans
      (Finset.le_sup'
        (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)
        (Finset.mem_range.mpr (Nat.succ_pos n)))
  have hY_nonneg : 0 ≤ᵐ[μ] Y :=
    ae_of_all _ fun records => norm_nonneg _
  have hXsq_int : Integrable (fun records => X records ^ 2) μ := by
    simpa [X, μ] using
      M.integrable_scaledJumpMartingale_sup_sq_canonicalRecordMeasure x₀ i n
  have hY_int : Integrable Y μ := by
    simpa [Y, μ] using
      (M.integrable_scaledJumpMartingale_canonicalRecordMeasure x₀ i n).norm
  have hX_memLp_nat : MemLp X 2 μ := by
    exact (memLp_two_iff_integrable_sq hX_meas.aestronglyMeasurable).2 hXsq_int
  have hX_memLp : MemLp X (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hX_memLp_nat
  have hY_sq_int : Integrable (fun records => Y records ^ 2) μ := by
    have hterminal :=
      M.integrable_scaledJumpMartingale_sq_canonicalRecordMeasure x₀ i n
    refine hterminal.congr ?_
    refine ae_of_all _ fun records => ?_
    dsimp [Y]
    exact (sq_abs (M.scaledJumpMartingale (M.canonicalPathMap records) i n)).symm
  have hY_memLp_nat : MemLp Y 2 μ := by
    exact (memLp_two_iff_integrable_sq hY_meas.aestronglyMeasurable).2 hY_sq_int
  have hY_memLp : MemLp Y (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hY_memLp_nat
  have hXY_int : Integrable (fun records => X records * Y records) μ := by
    exact MemLp.integrable_mul hX_memLp_nat hY_memLp_nat
  have hMax : ∀ ε : NNReal,
      ((ε : ENNReal) * μ {records | (ε : ℝ) ≤ X records}) ≤
        ENNReal.ofReal (∫ records in {records | (ε : ℝ) ≤ X records},
          Y records ∂μ) := by
    intro ε
    simpa [X, Y, μ] using
      M.scaledJumpMartingale_norm_maximal_ineq_of_noAbsorbing x₀ hNA i ε n
  simpa [X, Y, μ] using
    integral_sq_le_two_integral_mul_of_maximal_ineq
      hX_meas hY_meas hX_nonneg hY_nonneg hXsq_int hY_int hXY_int hMax

/-- The centered coordinate squared-jump process has zero conditional expected
increment with respect to the canonical record filtration. -/
theorem condExp_scaledCoordJumpSqMartingale_increment_eq_zero_ae_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (n : ℕ) (i : Fin d) :
    (M.canonicalRecordMeasure x₀)[
      (fun records : M.canonicalRecordΩ =>
        M.scaledCoordJumpSqMartingale (M.canonicalPathMap records) i (n + 1) -
          M.scaledCoordJumpSqMartingale (M.canonicalPathMap records) i n)
      | M.canonicalRecordFiltration n] =ᵐ[M.canonicalRecordMeasure x₀] 0 := by
  let μ := M.canonicalRecordMeasure x₀
  let nextSqJump : M.canonicalRecordΩ → ℝ := fun records =>
    ((M.scaledState ((records (n + 1)).2) -
      M.scaledState ((M.canonicalPathMap records).stateSeq n)) i) ^ 2
  let comp : M.canonicalRecordΩ → ℝ := fun records =>
    M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq n) i /
      M.exitRateAt ((M.canonicalPathMap records).stateSeq n)
  have hinc :
      (fun records : M.canonicalRecordΩ =>
        M.scaledCoordJumpSqMartingale (M.canonicalPathMap records) i (n + 1) -
          M.scaledCoordJumpSqMartingale (M.canonicalPathMap records) i n)
        =ᵐ[μ] fun records => nextSqJump records - comp records := by
    refine ae_of_all _ fun records => ?_
    simp [nextSqJump, comp, M.scaledCoordJumpSqMartingale_succ_sub,
      canonicalPathMap, QMatrix.recordTrajectoryToPath_stateSeq]
  have hnext :
      μ[nextSqJump | M.canonicalRecordFiltration n] =ᵐ[μ] comp := by
    have h :=
      M.condExp_next_scaledState_sub_apply_sq_eq_instantCoordQVRate_div_exitRate_ae_of_noAbsorbing
        x₀ hNA n i
    dsimp [μ, nextSqJump, comp]
    rw [canonicalRecordFiltration,
      QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe]
    simpa [Pi.sub_apply] using h
  have hcomp :
      μ[comp | M.canonicalRecordFiltration n] = comp := by
    exact MeasureTheory.condExp_of_stronglyMeasurable
      (M.canonicalRecordFiltration.le n)
      (M.measurable_instantCoordQVRate_div_exitRate_stateSeq_canonicalRecordFiltration
        i n).stronglyMeasurable
      (M.integrable_instantCoordQVRate_div_exitRate_stateSeq_canonicalRecordMeasure x₀ i n)
  have hsub :
      μ[nextSqJump - comp | M.canonicalRecordFiltration n] =ᵐ[μ]
        μ[nextSqJump | M.canonicalRecordFiltration n] -
          μ[comp | M.canonicalRecordFiltration n] :=
    MeasureTheory.condExp_sub
      (M.integrable_next_scaledState_sub_apply_sq x₀ n i)
      (M.integrable_instantCoordQVRate_div_exitRate_stateSeq_canonicalRecordMeasure x₀ i n)
      (M.canonicalRecordFiltration n)
  refine (MeasureTheory.condExp_congr_ae hinc).trans ?_
  change μ[nextSqJump - comp | M.canonicalRecordFiltration n] =ᵐ[μ] 0
  rw [hcomp] at hsub
  filter_upwards [hsub, hnext] with records hsub_eq hnext_eq
  rw [hsub_eq]
  simp [Pi.sub_apply, hnext_eq]

/-- The centered coordinate squared-jump process is a martingale along the
embedded jump index under the canonical non-absorbing record law. -/
theorem scaledCoordJumpSqMartingale_martingale_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) (i : Fin d) :
    MeasureTheory.Martingale
      (fun n records =>
        M.scaledCoordJumpSqMartingale (M.canonicalPathMap records) i n)
      M.canonicalRecordFiltration (M.canonicalRecordMeasure x₀) :=
  MeasureTheory.martingale_of_condExp_sub_eq_zero_nat
    (M.stronglyAdapted_scaledCoordJumpSqMartingale_canonicalRecordFiltration i)
    (M.integrable_scaledCoordJumpSqMartingale_canonicalRecordMeasure x₀ i)
    (fun n =>
      M.condExp_scaledCoordJumpSqMartingale_increment_eq_zero_ae_of_noAbsorbing
        x₀ hNA n i)

/-- The centered coordinate jump-sum martingale has zero expectation at every
jump index. -/
theorem integral_scaledJumpMartingale_eq_zero_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    ∫ records, M.scaledJumpMartingale (M.canonicalPathMap records) i n
      ∂M.canonicalRecordMeasure x₀ = 0 := by
  let Z : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.scaledJumpMartingale (M.canonicalPathMap records) i n
  have hmart : MeasureTheory.Martingale Z M.canonicalRecordFiltration
      (M.canonicalRecordMeasure x₀) := by
    simpa [Z] using M.scaledJumpMartingale_martingale_of_noAbsorbing x₀ hNA i
  have hset := hmart.setIntegral_eq (Nat.zero_le n)
    (s := Set.univ) (by simp)
  simpa [Z] using hset.symm

/-- The centered coordinate squared-jump martingale has zero expectation at
every jump index. -/
theorem integral_scaledCoordJumpSqMartingale_eq_zero_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    ∫ records, M.scaledCoordJumpSqMartingale (M.canonicalPathMap records) i n
      ∂M.canonicalRecordMeasure x₀ = 0 := by
  let Z : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.scaledCoordJumpSqMartingale (M.canonicalPathMap records) i n
  have hmart : MeasureTheory.Martingale Z M.canonicalRecordFiltration
      (M.canonicalRecordMeasure x₀) := by
    simpa [Z] using M.scaledCoordJumpSqMartingale_martingale_of_noAbsorbing x₀ hNA i
  have hset := hmart.setIntegral_eq (Nat.zero_le n)
    (s := Set.univ) (by simp)
  simpa [Z] using hset.symm

/-- The expected raw coordinate squared-jump sum equals the expected coordinate
QV compensator. -/
theorem integral_scaledCoordJumpSqSum_eq_integral_scaledCoordQVCompensator_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    ∫ records, M.scaledCoordJumpSqSum (M.canonicalPathMap records) i n
      ∂M.canonicalRecordMeasure x₀ =
    ∫ records, M.scaledCoordQVCompensator (M.canonicalPathMap records) i n
      ∂M.canonicalRecordMeasure x₀ := by
  have hzero :=
    M.integral_scaledCoordJumpSqMartingale_eq_zero_of_noAbsorbing x₀ hNA i n
  have hsub :
      ∫ records,
          (M.scaledCoordJumpSqSum (M.canonicalPathMap records) i n -
            M.scaledCoordQVCompensator (M.canonicalPathMap records) i n)
          ∂M.canonicalRecordMeasure x₀ =
        ∫ records, M.scaledCoordJumpSqSum (M.canonicalPathMap records) i n
          ∂M.canonicalRecordMeasure x₀ -
        ∫ records, M.scaledCoordQVCompensator (M.canonicalPathMap records) i n
          ∂M.canonicalRecordMeasure x₀ := by
    exact integral_sub
      (M.integrable_scaledCoordJumpSqSum_canonicalRecordMeasure x₀ i n)
      (M.integrable_scaledCoordQVCompensator_canonicalRecordMeasure x₀ i n)
  have hdiff :
      ∫ records, M.scaledCoordJumpSqSum (M.canonicalPathMap records) i n
          ∂M.canonicalRecordMeasure x₀ -
        ∫ records, M.scaledCoordQVCompensator (M.canonicalPathMap records) i n
          ∂M.canonicalRecordMeasure x₀ = 0 := by
    rw [← hsub]
    simpa [scaledCoordJumpSqMartingale] using hzero
  linarith

/-- One-step conditional-variance estimate for the centered coordinate
jump martingale.  This is the local L2 input for the terminal bracket bound. -/
theorem integral_scaledJumpMartingale_increment_sq_le_integral_next_sq_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    ∫ records,
        (M.scaledJumpMartingale (M.canonicalPathMap records) i (n + 1) -
          M.scaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
    ∫ records,
        ((M.scaledState ((records (n + 1)).2) -
          M.scaledState ((M.canonicalPathMap records).stateSeq n)) i) ^ 2
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let nextJump : M.canonicalRecordΩ → ℝ := fun records =>
    (M.scaledState ((records (n + 1)).2) -
      M.scaledState ((M.canonicalPathMap records).stateSeq n)) i
  let comp : M.canonicalRecordΩ → ℝ := fun records =>
    M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i /
      M.exitRateAt ((M.canonicalPathMap records).stateSeq n)
  have hX_memLp : MemLp nextJump 2 μ := by
    exact (memLp_two_iff_integrable_sq
      (M.measurable_next_scaledState_sub_apply n i).aestronglyMeasurable).2
      (by
        simpa [nextJump, μ] using
          M.integrable_next_scaledState_sub_apply_sq x₀ n i)
  have hcenter_int :
      Integrable
        (fun records : M.canonicalRecordΩ =>
          (nextJump records -
            (μ[nextJump | M.canonicalRecordFiltration n]) records) ^ 2) μ := by
    simpa [Pi.sub_apply] using
      (hX_memLp.sub hX_memLp.condExp).integrable_sq
  have hnext :
      μ[nextJump | M.canonicalRecordFiltration n] =ᵐ[μ] comp := by
    have h :=
      M.condExp_next_scaledState_sub_apply_eq_generatorDrift_div_exitRate_ae_of_noAbsorbing
        x₀ hNA n i
    dsimp [μ, nextJump, comp]
    rw [canonicalRecordFiltration,
      QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe]
    simpa [Pi.sub_apply] using h
  have hinc :
      (fun records : M.canonicalRecordΩ =>
        (M.scaledJumpMartingale (M.canonicalPathMap records) i (n + 1) -
          M.scaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2)
        =ᵐ[μ]
      fun records =>
        (nextJump records -
          (μ[nextJump | M.canonicalRecordFiltration n]) records) ^ 2 := by
    filter_upwards [hnext] with records hnext_records
    have hstep :
        M.scaledJumpMartingale (M.canonicalPathMap records) i (n + 1) -
            M.scaledJumpMartingale (M.canonicalPathMap records) i n =
          nextJump records - comp records := by
      simp [nextJump, comp, M.scaledJumpMartingale_succ_sub, canonicalPathMap,
        QMatrix.recordTrajectoryToPath_stateSeq]
    rw [hstep, ← hnext_records]
  have hvar_eq :
      ∫ records,
          (ProbabilityTheory.condVar (M.canonicalRecordFiltration n) nextJump μ) records
          ∂μ =
        ∫ records,
          (nextJump records -
            (μ[nextJump | M.canonicalRecordFiltration n]) records) ^ 2 ∂μ := by
    simpa using
      (ProbabilityTheory.setIntegral_condVar
        (hm := M.canonicalRecordFiltration.le n)
        (X := nextJump) (μ := μ) (s := Set.univ)
        hcenter_int (by simp))
  have hvar_le :
      ProbabilityTheory.condVar (M.canonicalRecordFiltration n) nextJump μ
        ≤ᵐ[μ]
      μ[(nextJump ^ 2) | M.canonicalRecordFiltration n] :=
    ProbabilityTheory.condVar_ae_le_condExp_sq
      (hm := M.canonicalRecordFiltration.le n)
      (X := nextJump) (μ := μ) hX_memLp
  have hvar_int_le :
      ∫ records,
          (ProbabilityTheory.condVar (M.canonicalRecordFiltration n) nextJump μ) records
          ∂μ ≤
        ∫ records, (μ[(nextJump ^ 2) | M.canonicalRecordFiltration n]) records ∂μ := by
    exact integral_mono_ae ProbabilityTheory.integrable_condVar integrable_condExp hvar_le
  have hcond_int :
      ∫ records, (μ[(nextJump ^ 2) | M.canonicalRecordFiltration n]) records ∂μ =
        ∫ records, nextJump records ^ 2 ∂μ := by
    simpa [Pi.pow_apply] using
      (integral_condExp (μ := μ)
        (m := M.canonicalRecordFiltration n)
        (f := nextJump ^ 2)
        (M.canonicalRecordFiltration.le n))
  calc
    ∫ records,
        (M.scaledJumpMartingale (M.canonicalPathMap records) i (n + 1) -
          M.scaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2
        ∂M.canonicalRecordMeasure x₀
        = ∫ records,
          (nextJump records -
            (μ[nextJump | M.canonicalRecordFiltration n]) records) ^ 2 ∂μ := by
            simpa [μ] using integral_congr_ae hinc
    _ = ∫ records,
          (ProbabilityTheory.condVar (M.canonicalRecordFiltration n) nextJump μ) records
          ∂μ := hvar_eq.symm
    _ ≤ ∫ records, (μ[(nextJump ^ 2) | M.canonicalRecordFiltration n]) records ∂μ :=
          hvar_int_le
    _ = ∫ records, nextJump records ^ 2 ∂μ := hcond_int
    _ = ∫ records,
        ((M.scaledState ((records (n + 1)).2) -
          M.scaledState ((M.canonicalPathMap records).stateSeq n)) i) ^ 2
        ∂M.canonicalRecordMeasure x₀ := by
          simp [nextJump, μ]

/-- Orthogonality of a centered coordinate jump-martingale increment against
the previous embedded-time martingale value. -/
theorem integral_scaledJumpMartingale_mul_increment_eq_zero_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    ∫ records,
        M.scaledJumpMartingale (M.canonicalPathMap records) i n *
          (M.scaledJumpMartingale (M.canonicalPathMap records) i (n + 1) -
            M.scaledJumpMartingale (M.canonicalPathMap records) i n)
        ∂M.canonicalRecordMeasure x₀ = 0 := by
  let μ := M.canonicalRecordMeasure x₀
  let Z : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.scaledJumpMartingale (M.canonicalPathMap records) i n
  let inc : M.canonicalRecordΩ → ℝ := fun records => Z (n + 1) records - Z n records
  have hZ_memLp : MemLp (Z n) 2 μ := by
    exact (memLp_two_iff_integrable_sq
      (((M.stronglyAdapted_scaledJumpMartingale_canonicalRecordFiltration i n).mono
        (M.canonicalRecordFiltration.le n)).aestronglyMeasurable)).2
      (by
        simpa [Z, μ] using
          M.integrable_scaledJumpMartingale_sq_canonicalRecordMeasure x₀ i n)
  have hZ_succ_memLp : MemLp (Z (n + 1)) 2 μ := by
    exact (memLp_two_iff_integrable_sq
      (((M.stronglyAdapted_scaledJumpMartingale_canonicalRecordFiltration i (n + 1)).mono
        (M.canonicalRecordFiltration.le (n + 1))).aestronglyMeasurable)).2
      (by
        simpa [Z, μ] using
          M.integrable_scaledJumpMartingale_sq_canonicalRecordMeasure x₀ i (n + 1))
  have hinc_memLp : MemLp inc 2 μ := by
    simpa [inc, Pi.sub_apply] using hZ_succ_memLp.sub hZ_memLp
  have hinc_int : Integrable inc μ := hinc_memLp.integrable one_le_two
  have hprod_int : Integrable (fun records => Z n records * inc records) μ := by
    simpa [mul_comm] using hinc_memLp.integrable_mul hZ_memLp
  have hpull :
      μ[(fun records => Z n records * inc records) | M.canonicalRecordFiltration n]
        =ᵐ[μ]
      fun records => Z n records *
        (μ[inc | M.canonicalRecordFiltration n]) records := by
    exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (M.stronglyAdapted_scaledJumpMartingale_canonicalRecordFiltration i n)
      hprod_int hinc_int
  have hcond_inc :
      μ[inc | M.canonicalRecordFiltration n] =ᵐ[μ] 0 := by
    simpa [inc, Z, μ] using
      M.condExp_scaledJumpMartingale_increment_eq_zero_ae_of_noAbsorbing x₀ hNA n i
  have hcond_prod :
      μ[(fun records => Z n records * inc records) | M.canonicalRecordFiltration n]
        =ᵐ[μ] 0 := by
    filter_upwards [hpull, hcond_inc] with records hpull_records hinc_records
    rw [hpull_records, hinc_records]
    simp
  calc
    ∫ records, Z n records * inc records ∂μ
        = ∫ records,
            (μ[(fun records => Z n records * inc records) |
              M.canonicalRecordFiltration n]) records ∂μ := by
            exact (integral_condExp
              (μ := μ)
              (m := M.canonicalRecordFiltration n)
              (f := fun records => Z n records * inc records)
              (M.canonicalRecordFiltration.le n)).symm
    _ = 0 := by
          simpa using integral_congr_ae hcond_prod

/-- L2 recursion for the embedded centered coordinate jump martingale. -/
theorem integral_scaledJumpMartingale_sq_succ_eq_add_increment_sq_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    ∫ records,
        (M.scaledJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2
        ∂M.canonicalRecordMeasure x₀ =
      ∫ records,
        (M.scaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2
        ∂M.canonicalRecordMeasure x₀ +
      ∫ records,
        (M.scaledJumpMartingale (M.canonicalPathMap records) i (n + 1) -
          M.scaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let Z : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.scaledJumpMartingale (M.canonicalPathMap records) i n
  let inc : M.canonicalRecordΩ → ℝ := fun records => Z (n + 1) records - Z n records
  have hZ_memLp : MemLp (Z n) 2 μ := by
    exact (memLp_two_iff_integrable_sq
      (((M.stronglyAdapted_scaledJumpMartingale_canonicalRecordFiltration i n).mono
        (M.canonicalRecordFiltration.le n)).aestronglyMeasurable)).2
      (by
        simpa [Z, μ] using
          M.integrable_scaledJumpMartingale_sq_canonicalRecordMeasure x₀ i n)
  have hZ_succ_memLp : MemLp (Z (n + 1)) 2 μ := by
    exact (memLp_two_iff_integrable_sq
      (((M.stronglyAdapted_scaledJumpMartingale_canonicalRecordFiltration i (n + 1)).mono
        (M.canonicalRecordFiltration.le (n + 1))).aestronglyMeasurable)).2
      (by
        simpa [Z, μ] using
          M.integrable_scaledJumpMartingale_sq_canonicalRecordMeasure x₀ i (n + 1))
  have hinc_memLp : MemLp inc 2 μ := by
    simpa [inc, Pi.sub_apply] using hZ_succ_memLp.sub hZ_memLp
  have hZ_sq_int : Integrable (fun records => (Z n records) ^ 2) μ :=
    hZ_memLp.integrable_sq
  have hinc_sq_int : Integrable (fun records => (inc records) ^ 2) μ :=
    hinc_memLp.integrable_sq
  have hprod_int : Integrable (fun records => Z n records * inc records) μ := by
    simpa [mul_comm] using hinc_memLp.integrable_mul hZ_memLp
  have hcross :
      ∫ records, Z n records * inc records ∂μ = 0 := by
    simpa [Z, inc, μ] using
      M.integral_scaledJumpMartingale_mul_increment_eq_zero_of_noAbsorbing x₀ hNA i n
  let A : M.canonicalRecordΩ → ℝ := fun records => (Z n records) ^ 2
  let B : M.canonicalRecordΩ → ℝ := fun records => 2 * (Z n records * inc records)
  let C : M.canonicalRecordΩ → ℝ := fun records => (inc records) ^ 2
  have hA_int : Integrable A μ := by simpa [A] using hZ_sq_int
  have hB_int : Integrable B μ := by simpa [B] using hprod_int.const_mul 2
  have hC_int : Integrable C μ := by simpa [C] using hinc_sq_int
  have hsum :
      ∫ records, ((A + (B + C)) records) ∂μ =
        ∫ records, A records ∂μ +
          ∫ records, B records ∂μ +
          ∫ records, C records ∂μ := by
    have h1 :
        ∫ records, ((A + (B + C)) records) ∂μ =
          ∫ records, A records ∂μ + ∫ records, ((B + C) records) ∂μ := by
      simpa only [Pi.add_apply] using integral_add hA_int (hB_int.add hC_int)
    have h2 :
        ∫ records, ((B + C) records) ∂μ =
          ∫ records, B records ∂μ + ∫ records, C records ∂μ := by
      simpa only [Pi.add_apply] using integral_add hB_int hC_int
    rw [h1, h2]
    ring
  have hB_zero : ∫ records, B records ∂μ = 0 := by
    calc
      ∫ records, B records ∂μ = 2 * ∫ records, Z n records * inc records ∂μ := by
        simpa [B] using
          (integral_const_mul (μ := μ) (r := (2 : ℝ))
            (f := fun records => Z n records * inc records))
      _ = 0 := by rw [hcross, mul_zero]
  calc
    ∫ records, (Z (n + 1) records) ^ 2 ∂μ
        = ∫ records, A records + B records + C records ∂μ := by
            apply integral_congr_ae
            exact ae_of_all _ fun records => by
              dsimp [A, B, C, inc]
              ring
    _ = ∫ records, ((A + (B + C)) records) ∂μ := by
          apply integral_congr_ae
          exact ae_of_all _ fun records => by
            dsimp [A, B, C]
            ring
    _ = ∫ records, A records ∂μ +
          ∫ records, B records ∂μ +
          ∫ records, C records ∂μ := hsum
    _ = ∫ records, (Z n records) ^ 2 ∂μ +
          ∫ records, (inc records) ^ 2 ∂μ := by
          rw [hB_zero]
          simp [A, C]
    _ = ∫ records,
          (M.scaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2
          ∂M.canonicalRecordMeasure x₀ +
        ∫ records,
          (M.scaledJumpMartingale (M.canonicalPathMap records) i (n + 1) -
            M.scaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2
          ∂M.canonicalRecordMeasure x₀ := by
          rfl

/-- Terminal L2 bound by the expected raw coordinate squared-jump sum. -/
theorem integral_scaledJumpMartingale_sq_le_integral_scaledCoordJumpSqSum_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    ∫ records,
        (M.scaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
    ∫ records,
        M.scaledCoordJumpSqSum (M.canonicalPathMap records) i n
        ∂M.canonicalRecordMeasure x₀ := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let μ := M.canonicalRecordMeasure x₀
      let raw : M.canonicalRecordΩ → ℝ := fun records =>
        M.scaledCoordJumpSqSum (M.canonicalPathMap records) i n
      let nextSq : M.canonicalRecordΩ → ℝ := fun records =>
        ((M.scaledState ((records (n + 1)).2) -
          M.scaledState ((M.canonicalPathMap records).stateSeq n)) i) ^ 2
      have hraw_int : Integrable raw μ := by
        simpa [raw, μ] using
          M.integrable_scaledCoordJumpSqSum_canonicalRecordMeasure x₀ i n
      have hnext_int : Integrable nextSq μ := by
        simpa [nextSq, μ] using
          M.integrable_next_scaledState_sub_apply_sq x₀ n i
      have hmart_rec :=
        M.integral_scaledJumpMartingale_sq_succ_eq_add_increment_sq_of_noAbsorbing
          x₀ hNA i n
      have hinc_le :=
        M.integral_scaledJumpMartingale_increment_sq_le_integral_next_sq_of_noAbsorbing
          x₀ hNA i n
      have hraw_succ :
          ∫ records,
              M.scaledCoordJumpSqSum (M.canonicalPathMap records) i (n + 1)
              ∂M.canonicalRecordMeasure x₀ =
            ∫ records, raw records ∂μ + ∫ records, nextSq records ∂μ := by
        calc
          ∫ records,
              M.scaledCoordJumpSqSum (M.canonicalPathMap records) i (n + 1)
              ∂M.canonicalRecordMeasure x₀
              = ∫ records, raw records + nextSq records ∂μ := by
                  apply integral_congr_ae
                  exact ae_of_all _ fun records => by
                    simp [raw, nextSq, M.scaledCoordJumpSqSum_succ,
                      canonicalPathMap, QMatrix.recordTrajectoryToPath_stateSeq]
          _ = ∫ records, raw records ∂μ + ∫ records, nextSq records ∂μ :=
              integral_add hraw_int hnext_int
      calc
        ∫ records,
            (M.scaledJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2
            ∂M.canonicalRecordMeasure x₀
            = ∫ records,
                (M.scaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2
                ∂M.canonicalRecordMeasure x₀ +
              ∫ records,
                (M.scaledJumpMartingale (M.canonicalPathMap records) i (n + 1) -
                  M.scaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2
                ∂M.canonicalRecordMeasure x₀ := hmart_rec
        _ ≤ ∫ records, raw records ∂μ + ∫ records, nextSq records ∂μ := by
              gcongr
        _ = ∫ records,
              M.scaledCoordJumpSqSum (M.canonicalPathMap records) i (n + 1)
              ∂M.canonicalRecordMeasure x₀ := hraw_succ.symm

/-- Terminal L2 bound by the expected coordinate QV compensator. -/
theorem integral_scaledJumpMartingale_sq_le_integral_scaledCoordQVCompensator_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    ∫ records,
        (M.scaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
    ∫ records,
        M.scaledCoordQVCompensator (M.canonicalPathMap records) i n
        ∂M.canonicalRecordMeasure x₀ := by
  calc
    ∫ records,
        (M.scaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2
        ∂M.canonicalRecordMeasure x₀
        ≤ ∫ records,
            M.scaledCoordJumpSqSum (M.canonicalPathMap records) i n
            ∂M.canonicalRecordMeasure x₀ :=
          M.integral_scaledJumpMartingale_sq_le_integral_scaledCoordJumpSqSum_of_noAbsorbing
            x₀ hNA i n
    _ = ∫ records,
          M.scaledCoordQVCompensator (M.canonicalPathMap records) i n
          ∂M.canonicalRecordMeasure x₀ :=
        M.integral_scaledCoordJumpSqSum_eq_integral_scaledCoordQVCompensator_of_noAbsorbing
          x₀ hNA i n

/-- Once the coordinate Doob L2 maximal estimate is available, it composes
directly with the terminal coordinate QV-compensator bound.  This is the
landing theorem for the jump-index coordinate route. -/
theorem integral_scaledJumpMartingale_sup_sq_le_four_integral_scaledCoordQV_of_noAbsorbing
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ)
    (hDoobL2 :
      ∫ records,
          ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2
          ∂M.canonicalRecordMeasure x₀ ≤
        4 * ∫ records,
          (M.scaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2
          ∂M.canonicalRecordMeasure x₀) :
    ∫ records,
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      4 * ∫ records,
        M.scaledCoordQVCompensator (M.canonicalPathMap records) i n
        ∂M.canonicalRecordMeasure x₀ := by
  calc
    ∫ records,
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2
        ∂M.canonicalRecordMeasure x₀
        ≤ 4 * ∫ records,
          (M.scaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2
          ∂M.canonicalRecordMeasure x₀ := hDoobL2
    _ ≤ 4 * ∫ records,
        M.scaledCoordQVCompensator (M.canonicalPathMap records) i n
        ∂M.canonicalRecordMeasure x₀ := by
      exact mul_le_mul_of_nonneg_left
        (M.integral_scaledJumpMartingale_sq_le_integral_scaledCoordQVCompensator_of_noAbsorbing
          x₀ hNA i n)
        (by norm_num : 0 ≤ (4 : ℝ))

/-- Direct coordinate-QV landing from the remaining layer-cake/maximal
inequality step.  Once `E X^2 ≤ 2 E(XY)` is proved for the finite jump-index
coordinate martingale, this theorem composes Cauchy, the algebraic Doob L2
landing, and the terminal coordinate QV-compensator bound. -/
theorem integral_scaledJumpMartingale_sup_sq_le_four_integral_scaledCoordQV_of_layercake
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ)
    (hLayer :
      ∫ records,
          ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2
          ∂M.canonicalRecordMeasure x₀ ≤
        2 * ∫ records,
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖) *
          ‖M.scaledJumpMartingale (M.canonicalPathMap records) i n‖
          ∂M.canonicalRecordMeasure x₀) :
    ∫ records,
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      4 * ∫ records,
        M.scaledCoordQVCompensator (M.canonicalPathMap records) i n
        ∂M.canonicalRecordMeasure x₀ := by
  have hDoobNorm :=
    M.integral_scaledJumpMartingale_sup_sq_le_four_terminal_norm_sq_of_layercake
      x₀ i n hLayer
  have hterminal_eq :
      ∫ records,
          ‖M.scaledJumpMartingale (M.canonicalPathMap records) i n‖ ^ 2
          ∂M.canonicalRecordMeasure x₀ =
        ∫ records,
          (M.scaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2
          ∂M.canonicalRecordMeasure x₀ := by
    apply integral_congr_ae
    exact ae_of_all _ fun records => by
      change ‖M.scaledJumpMartingale (M.canonicalPathMap records) i n‖ ^ 2 =
        (M.scaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2
      rw [Real.norm_eq_abs]
      exact sq_abs (M.scaledJumpMartingale (M.canonicalPathMap records) i n)
  calc
    ∫ records,
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2
        ∂M.canonicalRecordMeasure x₀
        ≤ 4 * ∫ records,
          ‖M.scaledJumpMartingale (M.canonicalPathMap records) i n‖ ^ 2
          ∂M.canonicalRecordMeasure x₀ := hDoobNorm
    _ = 4 * ∫ records,
          (M.scaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2
          ∂M.canonicalRecordMeasure x₀ := by rw [hterminal_eq]
    _ ≤ 4 * ∫ records,
        M.scaledCoordQVCompensator (M.canonicalPathMap records) i n
        ∂M.canonicalRecordMeasure x₀ := by
      exact mul_le_mul_of_nonneg_left
        (M.integral_scaledJumpMartingale_sq_le_integral_scaledCoordQVCompensator_of_noAbsorbing
          x₀ hNA i n)
        (by norm_num : 0 ≤ (4 : ℝ))

/-- Direct finite jump-index coordinate Doob/QV estimate under the
non-absorbing canonical law. -/
theorem integral_scaledJumpMartingale_sup_sq_le_scaledCoordQV_of_noAbsorbing_maximal
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (i : Fin d) (n : ℕ) :
    ∫ records,
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      4 * ∫ records,
        M.scaledCoordQVCompensator (M.canonicalPathMap records) i n
        ∂M.canonicalRecordMeasure x₀ := by
  exact M.integral_scaledJumpMartingale_sup_sq_le_four_integral_scaledCoordQV_of_layercake
    x₀ hNA i n
    (M.integral_sup_scaledJumpMartingale_norm_sq_le_two_mul_sup_mul_norm_of_noAbsorbing
      x₀ hNA i n)

/-- Summed coordinate version of the finite jump-index Doob/QV estimate,
bounded by the embedded vector QV compensator. -/
theorem integral_sum_scaledJumpMartingale_sup_sq_le_scaledQV_of_noAbsorbing_maximal
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (n : ℕ) :
    ∫ records,
        ∑ i : Fin d,
          ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      (4 * (Fintype.card (Fin d) : ℝ)) *
        ∫ records,
          M.scaledQVCompensator (M.canonicalPathMap records) n
          ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let F : Fin d → M.canonicalRecordΩ → ℝ := fun i records =>
    ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2
  let G : Fin d → M.canonicalRecordΩ → ℝ := fun i records =>
    M.scaledCoordQVCompensator (M.canonicalPathMap records) i n
  let H : M.canonicalRecordΩ → ℝ := fun records =>
    M.scaledQVCompensator (M.canonicalPathMap records) n
  have hF_int : ∀ i : Fin d, Integrable (F i) μ := by
    intro i
    simpa [F, μ] using
      M.integrable_scaledJumpMartingale_sup_sq_canonicalRecordMeasure x₀ i n
  have hG_int : ∀ i : Fin d, Integrable (G i) μ := by
    intro i
    simpa [G, μ] using
      M.integrable_scaledCoordQVCompensator_canonicalRecordMeasure x₀ i n
  have hsumG_int : Integrable (fun records => ∑ i : Fin d, G i records) μ := by
    exact integrable_finset_sum Finset.univ fun i _ => hG_int i
  have hH_int : Integrable H μ := by
    simpa [H, μ] using
      M.integrable_scaledQVCompensator_canonicalRecordMeasure x₀ n
  have hcardH_int :
      Integrable (fun records : M.canonicalRecordΩ =>
        (Fintype.card (Fin d) : ℝ) * H records) μ := by
    exact hH_int.const_mul _
  have hsum_le :
      (fun records : M.canonicalRecordΩ => ∑ i : Fin d, G i records)
        ≤ᵐ[μ]
      (fun records : M.canonicalRecordΩ =>
        (Fintype.card (Fin d) : ℝ) * H records) := by
    filter_upwards with records
    simpa [G, H] using
      M.sum_scaledCoordQVCompensator_le_card_mul_scaledQVCompensator_of_noAbsorbing
        hNA (M.canonicalPathMap records) n
  have hmono := integral_mono_ae hsumG_int hcardH_int hsum_le
  calc
    ∫ records, ∑ i : Fin d, F i records ∂μ
        = ∑ i : Fin d, ∫ records, F i records ∂μ := by
            rw [integral_finset_sum Finset.univ]
            intro i _
            exact hF_int i
    _ ≤ ∑ i : Fin d, 4 * ∫ records, G i records ∂μ := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact
            M.integral_scaledJumpMartingale_sup_sq_le_scaledCoordQV_of_noAbsorbing_maximal
              x₀ hNA i n
    _ = 4 * ∑ i : Fin d, ∫ records, G i records ∂μ := by
          rw [Finset.mul_sum]
    _ = 4 * ∫ records, ∑ i : Fin d, G i records ∂μ := by
          rw [integral_finset_sum Finset.univ]
          intro i _
          exact hG_int i
    _ ≤ 4 * ∫ records, (Fintype.card (Fin d) : ℝ) * H records ∂μ := by
          exact mul_le_mul_of_nonneg_left hmono (by norm_num : 0 ≤ (4 : ℝ))
    _ = (4 * (Fintype.card (Fin d) : ℝ)) * ∫ records, H records ∂μ := by
          rw [integral_const_mul]
          ring
    _ = (4 * (Fintype.card (Fin d) : ℝ)) *
        ∫ records,
          M.scaledQVCompensator (M.canonicalPathMap records) n
          ∂M.canonicalRecordMeasure x₀ := by
          simp [H, μ]

/-- Under boundary compatibility, the actual finite-lattice generator drift is
the abstract mean-field drift evaluated at the scaled state. -/
theorem generatorDrift_eq_rateSpec_drift_of_boundaryCompatible
    (hBC : M.BoundaryCompatible) (x : Fin d → Fin (M.N + 1)) :
    M.generatorDrift x = M.rateSpec.drift (M.scaledState x) := by
  ext i
  calc
    M.generatorDrift x i
        = ∑ y : Fin d → Fin (M.N + 1),
            ∑ ℓ ∈ M.rateSpec.jumps.filter
              (fun ℓ : Fin d → ℤ => ∀ j, (y j : ℤ) - (x j : ℤ) = ℓ j),
              (ℓ i : ℝ) * M.rateSpec.rate ℓ (M.scaledState x) := by
          simp only [generatorDrift]
          apply Finset.sum_congr rfl
          intro y _
          exact M.offDiagRate_mul_scaledState_sub_apply_eq_sum_jumps x y i
    _ = ∑ y : Fin d → Fin (M.N + 1),
            ∑ ℓ ∈ M.rateSpec.jumps,
              if (∀ j, (y j : ℤ) - (x j : ℤ) = ℓ j) then
                (ℓ i : ℝ) * M.rateSpec.rate ℓ (M.scaledState x) else 0 := by
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.sum_filter]
    _ = ∑ ℓ ∈ M.rateSpec.jumps,
            ∑ y : Fin d → Fin (M.N + 1),
              if (∀ j, (y j : ℤ) - (x j : ℤ) = ℓ j) then
                (ℓ i : ℝ) * M.rateSpec.rate ℓ (M.scaledState x) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ ℓ ∈ M.rateSpec.jumps,
            (if ∃ y : Fin d → Fin (M.N + 1),
                ∀ j, (y j : ℤ) - (x j : ℤ) = ℓ j then
                (ℓ i : ℝ) * M.rateSpec.rate ℓ (M.scaledState x) else 0) := by
          apply Finset.sum_congr rfl
          intro ℓ _
          rw [← Finset.sum_filter]
          exact M.sum_matchingStates_const_eq_ite_exists x ℓ
            ((ℓ i : ℝ) * M.rateSpec.rate ℓ (M.scaledState x))
    _ = ∑ ℓ ∈ M.rateSpec.jumps,
          (ℓ i : ℝ) * M.rateSpec.rate ℓ (M.scaledState x) := by
          apply Finset.sum_congr rfl
          intro ℓ hℓ
          by_cases hex : ∃ y : Fin d → Fin (M.N + 1),
              ∀ j, (y j : ℤ) - (x j : ℤ) = ℓ j
          · rw [if_pos hex]
          · rw [if_neg hex]
            have hrate0 := hBC x ℓ hℓ hex
            simp [hrate0]
    _ = (M.rateSpec.drift (M.scaledState x)) i := by
          rfl

/-- On simplex states, simplex-local boundary compatibility is sufficient to
align the actual finite-lattice generator drift with the abstract mean-field
drift. -/
theorem generatorDrift_eq_rateSpec_drift_of_boundaryCompatibleOnSimplex
    (hBC : M.BoundaryCompatibleOnSimplex) {x : Fin d → Fin (M.N + 1)}
    (hx : M.InSimplex x) :
    M.generatorDrift x = M.rateSpec.drift (M.scaledState x) := by
  ext i
  calc
    M.generatorDrift x i
        = ∑ y : Fin d → Fin (M.N + 1),
            ∑ ℓ ∈ M.rateSpec.jumps.filter
              (fun ℓ : Fin d → ℤ => ∀ j, (y j : ℤ) - (x j : ℤ) = ℓ j),
              (ℓ i : ℝ) * M.rateSpec.rate ℓ (M.scaledState x) := by
          simp only [generatorDrift]
          apply Finset.sum_congr rfl
          intro y _
          exact M.offDiagRate_mul_scaledState_sub_apply_eq_sum_jumps x y i
    _ = ∑ y : Fin d → Fin (M.N + 1),
            ∑ ℓ ∈ M.rateSpec.jumps,
              if (∀ j, (y j : ℤ) - (x j : ℤ) = ℓ j) then
                (ℓ i : ℝ) * M.rateSpec.rate ℓ (M.scaledState x) else 0 := by
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.sum_filter]
    _ = ∑ ℓ ∈ M.rateSpec.jumps,
            ∑ y : Fin d → Fin (M.N + 1),
              if (∀ j, (y j : ℤ) - (x j : ℤ) = ℓ j) then
                (ℓ i : ℝ) * M.rateSpec.rate ℓ (M.scaledState x) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ ℓ ∈ M.rateSpec.jumps,
            (if ∃ y : Fin d → Fin (M.N + 1),
                ∀ j, (y j : ℤ) - (x j : ℤ) = ℓ j then
                (ℓ i : ℝ) * M.rateSpec.rate ℓ (M.scaledState x) else 0) := by
          apply Finset.sum_congr rfl
          intro ℓ _
          rw [← Finset.sum_filter]
          exact M.sum_matchingStates_const_eq_ite_exists x ℓ
            ((ℓ i : ℝ) * M.rateSpec.rate ℓ (M.scaledState x))
    _ = ∑ ℓ ∈ M.rateSpec.jumps,
          (ℓ i : ℝ) * M.rateSpec.rate ℓ (M.scaledState x) := by
          apply Finset.sum_congr rfl
          intro ℓ hℓ
          by_cases hex : ∃ y : Fin d → Fin (M.N + 1),
              ∀ j, (y j : ℤ) - (x j : ℤ) = ℓ j
          · rw [if_pos hex]
          · rw [if_neg hex]
            have hrate0 := hBC x hx ℓ hℓ hex
            simp [hrate0]
    _ = (M.rateSpec.drift (M.scaledState x)) i := by
          rfl

/-- One-step embedded-chain second moment per unit exit rate equals the
generator-side instantaneous QV rate.  This is the local bracket identity
behind the remaining martingale QV estimate. -/
theorem exitRateAt_mul_integral_embeddedStepMeasure_scaledState_sub_sq
    (x : Fin d → Fin (M.N + 1)) (h : ¬M.toQMatrix.IsAbsorbing x) :
    M.exitRateAt x *
      (∫ y, ‖M.scaledState y - M.scaledState x‖ ^ 2
        ∂M.toQMatrix.embeddedStepMeasure x) =
    M.instantQVRate x := by
  let f : (Fin d → Fin (M.N + 1)) → ℝ :=
    fun y => ‖M.scaledState y - M.scaledState x‖ ^ 2
  have hsum := M.toQMatrix.exitRate_mul_integral_embeddedStepMeasure_eq_sum_rate h f
  rw [exitRateAt]
  rw [hsum]
  simp only [instantQVRate]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _hy
  by_cases hyx : y ≠ x
  · have hxy : x ≠ y := Ne.symm hyx
    rw [if_pos hyx]
    simp only [toQMatrix, qMatrixRate, if_neg hxy]
    rfl
  · rw [if_neg hyx]
    have hxy : x = y := (not_ne_iff.mp hyx).symm
    subst y
    simp [offDiagRate]

/-- Deterministic generator-side instantaneous quadratic variation bound.
This is the finite-state rate estimate that the stochastic bracket theorem
will integrate along CTMC paths. -/
theorem exists_instantQV_bound :
    ∃ C > 0, ∀ x : Fin d → Fin (M.N + 1),
      (∑ y : Fin d → Fin (M.N + 1),
        M.offDiagRate x y * ‖M.scaledState y - M.scaledState x‖ ^ 2) ≤
        C / (M.N : ℝ) := by
  obtain ⟨B, hBpos, hB⟩ := M.rateSpec.exists_rate_bound_on_ball 1 zero_lt_one
  refine ⟨B * (M.rateSpec.jumps.card : ℝ) * M.rateSpec.jumpNormBound ^ 2 + 1,
    by positivity, ?_⟩
  intro x
  let b := (M.rateSpec.jumpNormBound / (M.N : ℝ)) ^ 2
  let a : (Fin d → ℤ) → ℝ :=
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
  calc
    ∑ y : Fin d → Fin (M.N + 1),
        M.offDiagRate x y * ‖M.scaledState y - M.scaledState x‖ ^ 2
        ≤ ∑ y : Fin d → Fin (M.N + 1),
            ∑ ℓ ∈ M.rateSpec.jumps.filter
              (fun ℓ : Fin d → ℤ => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i), a ℓ * b := by
          exact Finset.sum_le_sum fun y _ =>
            (M.offDiagRate_mul_scaledState_sub_sq_le x y).trans_eq (by simp [a, b])
    _ = ∑ y : Fin d → Fin (M.N + 1),
            ∑ ℓ ∈ M.rateSpec.jumps,
              if (∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i) then a ℓ * b else 0 := by
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.sum_filter]
    _ = ∑ ℓ ∈ M.rateSpec.jumps,
            ∑ y : Fin d → Fin (M.N + 1),
              if (∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i) then a ℓ * b else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ ℓ ∈ M.rateSpec.jumps,
            ∑ y ∈ (Finset.univ : Finset (Fin d → Fin (M.N + 1))).filter
              (fun y : Fin d → Fin (M.N + 1) => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i), a ℓ * b := by
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
    _ ≤ (B * (M.rateSpec.jumps.card : ℝ) * M.rateSpec.jumpNormBound ^ 2 + 1) /
          (M.N : ℝ) := by
          gcongr
          linarith

/-- Named version of `exists_instantQV_bound` using `instantQVRate`. -/
theorem exists_instantQVRate_bound :
    ∃ C > 0, ∀ x : Fin d → Fin (M.N + 1),
      M.instantQVRate x ≤ C / (M.N : ℝ) := by
  simpa [instantQVRate] using M.exists_instantQV_bound

/-- Coordinate instantaneous QV rates inherit the deterministic `O(1/N)` bound
from the vector instantaneous QV rate. -/
theorem exists_instantCoordQVRate_bound (i : Fin d) :
    ∃ C > 0, ∀ x : Fin d → Fin (M.N + 1),
      M.instantCoordQVRate x i ≤ C / (M.N : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := M.exists_instantQVRate_bound
  refine ⟨C, hC, ?_⟩
  intro x
  exact (M.instantCoordQVRate_le_instantQVRate x i).trans (hbound x)

/-! ## Martingale Decomposition and Density Process Bridge

This file separates two layers:

1. A deterministic bridge from any realized CTMC path map to the abstract
   `Kurtz.DensityProcess` interface.
2. The still-to-be-built canonical CTMC law, which should supply such a path map
   and prove the QV estimate from the density-dependent rates.

We deliberately do not manufacture a fake `Ω → CTMCPath` here: the real
construction belongs to the finite-state CTMC law/Ionescu-Tulcea layer. -/

variable {Ω : Type*}

/-- The deterministic instantaneous-QV bound holds along any realized path
map, uniformly over time and samples. -/
theorem exists_instantQVRate_path_bound (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) :
    ∃ C > 0, ∀ (t : ℝ) (ω : Ω),
      M.instantQVRate ((pathMap ω).stateAt t) ≤ C / (M.N : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := M.exists_instantQVRate_bound
  exact ⟨C, hC, fun t ω => hbound ((pathMap ω).stateAt t)⟩

/-- Finite-horizon deterministic integral bound for the instantaneous-QV
integrand along any realized path map.  This is the analytic shape needed for
the predictable bracket estimate; the remaining stochastic work is identifying
the martingale bracket with this time integral. -/
theorem exists_instantQVRate_path_setIntegral_bound (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C > 0, ∀ ω : Ω,
      ∫ s in Set.Icc (0 : ℝ) T, M.instantQVRate ((pathMap ω).stateAt s) ≤
        C * T / (M.N : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := M.exists_instantQVRate_path_bound pathMap
  refine ⟨C, hC, ?_⟩
  intro ω
  let f : ℝ → ℝ := fun s => M.instantQVRate ((pathMap ω).stateAt s)
  have hCdiv_nonneg : 0 ≤ C / (M.N : ℝ) := by positivity
  have hnorm_bound : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖f s‖ ≤ C / (M.N : ℝ) := by
    intro s _hs
    rw [Real.norm_eq_abs]
    refine abs_le.mpr ⟨?_, ?_⟩
    · have hnonneg : 0 ≤ f s := M.instantQVRate_nonneg ((pathMap ω).stateAt s)
      linarith
    · exact hbound s ω
  have hnorm :
      ‖∫ s in Set.Icc (0 : ℝ) T, f s‖ ≤
        (C / (M.N : ℝ)) * volume.real (Set.Icc (0 : ℝ) T) :=
    norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (0 : ℝ) T)
      (f := f) measure_Icc_lt_top hnorm_bound
  calc
    ∫ s in Set.Icc (0 : ℝ) T, M.instantQVRate ((pathMap ω).stateAt s)
        = ∫ s in Set.Icc (0 : ℝ) T, f s := rfl
    _ ≤ ‖∫ s in Set.Icc (0 : ℝ) T, f s‖ := le_abs_self _
    _ ≤ (C / (M.N : ℝ)) * volume.real (Set.Icc (0 : ℝ) T) := hnorm
    _ = (C / (M.N : ℝ)) * T := by
      rw [Real.volume_real_Icc_of_le hT]
      ring
    _ = C * T / (M.N : ℝ) := by ring

/-- Coordinate instantaneous-QV bounds hold along any realized path map,
uniformly over time and samples. -/
theorem exists_instantCoordQVRate_path_bound (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) :
    ∃ C > 0, ∀ (t : ℝ) (ω : Ω),
      M.instantCoordQVRate ((pathMap ω).stateAt t) i ≤ C / (M.N : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := M.exists_instantCoordQVRate_bound i
  exact ⟨C, hC, fun t ω => hbound ((pathMap ω).stateAt t)⟩

/-- Finite-horizon deterministic integral bound for a coordinate
instantaneous-QV integrand along any realized path map. -/
theorem exists_instantCoordQVRate_path_setIntegral_bound (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ C > 0, ∀ ω : Ω,
      ∫ s in Set.Icc (0 : ℝ) T,
        M.instantCoordQVRate ((pathMap ω).stateAt s) i ≤
        C * T / (M.N : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := M.exists_instantCoordQVRate_path_bound pathMap i
  refine ⟨C, hC, ?_⟩
  intro ω
  let f : ℝ → ℝ := fun s => M.instantCoordQVRate ((pathMap ω).stateAt s) i
  have hCdiv_nonneg : 0 ≤ C / (M.N : ℝ) := by positivity
  have hnorm_bound : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖f s‖ ≤ C / (M.N : ℝ) := by
    intro s _hs
    rw [Real.norm_eq_abs]
    refine abs_le.mpr ⟨?_, ?_⟩
    · have hnonneg : 0 ≤ f s :=
        M.instantCoordQVRate_nonneg ((pathMap ω).stateAt s) i
      linarith
    · exact hbound s ω
  have hnorm :
      ‖∫ s in Set.Icc (0 : ℝ) T, f s‖ ≤
        (C / (M.N : ℝ)) * volume.real (Set.Icc (0 : ℝ) T) :=
    norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (0 : ℝ) T)
      (f := f) measure_Icc_lt_top hnorm_bound
  calc
    ∫ s in Set.Icc (0 : ℝ) T,
        M.instantCoordQVRate ((pathMap ω).stateAt s) i
        = ∫ s in Set.Icc (0 : ℝ) T, f s := rfl
    _ ≤ ‖∫ s in Set.Icc (0 : ℝ) T, f s‖ := le_abs_self _
    _ ≤ (C / (M.N : ℝ)) * volume.real (Set.Icc (0 : ℝ) T) := hnorm
    _ = (C / (M.N : ℝ)) * T := by
      rw [Real.volume_real_Icc_of_le hT]
      ring
    _ = C * T / (M.N : ℝ) := by ring

/-- The density process X̄^N(t) = X^N(t)/N.
Each component is the CTMC state at time t divided by population size N. -/
noncomputable def densityProcess (M : DensityDepCTMC d) :
    (Ω → CTMCPath (Fin d → Fin (M.N + 1))) →
    ℝ → Ω → Fin d → ℝ :=
  fun pathMap t ω => M.scaledState ((pathMap ω).stateAt t)

/-- Pathwise version of `generatorDrift_eq_rateSpec_drift_of_boundaryCompatible`
for any realized CTMC path map. -/
theorem generatorDrift_stateAt_eq_rateSpec_drift_densityProcess_of_boundaryCompatible
    (M : DensityDepCTMC d) (hBC : M.BoundaryCompatible)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (t : ℝ) (ω : Ω) :
    M.generatorDrift ((pathMap ω).stateAt t) =
      M.rateSpec.drift (M.densityProcess pathMap t ω) := by
  simpa [densityProcess] using
    M.generatorDrift_eq_rateSpec_drift_of_boundaryCompatible hBC ((pathMap ω).stateAt t)

/-- Pathwise simplex-local drift alignment.  This is the usable wrapper when
the process is known to stay in the total-population simplex rather than when
the rate specification is globally boundary compatible on the ambient cube. -/
theorem generatorDrift_stateAt_eq_rateSpec_drift_densityProcess_of_boundaryCompatibleOnSimplex
    (M : DensityDepCTMC d) (hBC : M.BoundaryCompatibleOnSimplex)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (t : ℝ) (ω : Ω)
    (hx : M.InSimplex ((pathMap ω).stateAt t)) :
    M.generatorDrift ((pathMap ω).stateAt t) =
      M.rateSpec.drift (M.densityProcess pathMap t ω) := by
  simpa [densityProcess] using
    M.generatorDrift_eq_rateSpec_drift_of_boundaryCompatibleOnSimplex hBC hx

/-- Canonical a.s. simplex-local drift alignment.  Under `NoAbsorbing`,
conservative jumps, simplex initial state, and simplex-local boundary
compatibility, the finite-lattice generator drift agrees with the mean-field
drift along the canonical path at every time almost surely. -/
theorem canonical_generatorDrift_eq_rateSpec_drift_ae_of_boundaryCompatibleOnSimplex
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (hNA : M.NoAbsorbing) (hcons : M.ConservativeJumps)
    (hinit : M.InSimplex x₀) (hBC : M.BoundaryCompatibleOnSimplex) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ t : ℝ,
      M.generatorDrift ((M.canonicalPathMap records).stateAt t) =
        M.rateSpec.drift (M.densityProcess M.canonicalPathMap t records) := by
  filter_upwards
    [M.canonicalPathMap_forall_inSimplex_stateAt_ae_of_noAbsorbing
      x₀ hNA hcons hinit]
    with records hsimp t
  exact M.generatorDrift_stateAt_eq_rateSpec_drift_densityProcess_of_boundaryCompatibleOnSimplex
    hBC M.canonicalPathMap t records (hsimp t)

/-- For the canonical record-law realization, the fixed-time state readout is
measurable. -/
theorem measurable_canonicalPathMap_stateAt (M : DensityDepCTMC d) (t : ℝ) :
    Measurable (fun records : M.canonicalRecordΩ => (M.canonicalPathMap records).stateAt t) := by
  simpa [canonicalPathMap] using
    (QMatrix.measurable_recordTrajectoryToPath_stateAt
      (S := Fin d → Fin (M.N + 1)) t)

/-- For the canonical record-law realization, fixed clock-time jump-count
level sets are measurable. -/
theorem measurableSet_canonicalPathMap_jumpCount_eq
    (M : DensityDepCTMC d) (t : ℝ) (n : ℕ) :
    MeasurableSet
      {records : M.canonicalRecordΩ |
        (M.canonicalPathMap records).jumpCount t = n} := by
  simpa [canonicalPathMap] using
    (QMatrix.measurableSet_recordTrajectoryToPath_jumpCount_eq
      (S := Fin d → Fin (M.N + 1)) t n)

/-- For the canonical record-law realization, fixed clock-time jump-count
sublevel sets are measurable. -/
theorem measurableSet_canonicalPathMap_jumpCount_le
    (M : DensityDepCTMC d) (t : ℝ) (n : ℕ) :
    MeasurableSet
      {records : M.canonicalRecordΩ |
        (M.canonicalPathMap records).jumpCount t ≤ n} := by
  rw [show {records : M.canonicalRecordΩ |
        (M.canonicalPathMap records).jumpCount t ≤ n} =
      ⋃ k ∈ Finset.range (n + 1),
        {records : M.canonicalRecordΩ |
          (M.canonicalPathMap records).jumpCount t = k} by
    ext records
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop,
      Finset.mem_range]
    constructor
    · intro hle
      exact ⟨(M.canonicalPathMap records).jumpCount t,
        Nat.lt_succ_of_le hle, rfl⟩
    · rintro ⟨k, hk, hk_eq⟩
      rw [hk_eq]
      exact Nat.le_of_lt_succ hk]
  exact Finset.measurableSet_biUnion (Finset.range (n + 1)) fun k _ =>
    M.measurableSet_canonicalPathMap_jumpCount_eq t k

/-- The coordinate QV compensator sampled at a fixed clock-time jump count is
a.e. strongly measurable. -/
theorem aestronglyMeasurable_scaledCoordQVCompensator_jumpCount
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (T : ℝ) :
    AEStronglyMeasurable
      (fun records : M.canonicalRecordΩ =>
        M.scaledCoordQVCompensator (M.canonicalPathMap records) i
          ((M.canonicalPathMap records).jumpCount T))
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let A : ℕ → Set M.canonicalRecordΩ := fun n =>
    {records | (M.canonicalPathMap records).jumpCount T = n}
  let F : M.canonicalRecordΩ → ℝ := fun records =>
    M.scaledCoordQVCompensator (M.canonicalPathMap records) i
      ((M.canonicalPathMap records).jumpCount T)
  let G : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.scaledCoordQVCompensator (M.canonicalPathMap records) i n
  have hA_meas : ∀ n, MeasurableSet (A n) := by
    intro n
    simpa [A] using M.measurableSet_canonicalPathMap_jumpCount_eq T n
  have hcover : (Set.univ : Set M.canonicalRecordΩ) = ⋃ n, A n := by
    ext records
    simp [A]
  have hpieces : ∀ n, AEStronglyMeasurable F (μ.restrict (A n)) := by
    intro n
    have hG : AEStronglyMeasurable (G n) (μ.restrict (A n)) := by
      exact (((M.measurable_scaledCoordQVCompensator_canonicalRecordFiltration i n).mono
        (M.canonicalRecordFiltration.le n) le_rfl).aestronglyMeasurable).mono_measure
        Measure.restrict_le_self
    have hFG : F =ᵐ[μ.restrict (A n)] G n := by
      filter_upwards [ae_restrict_mem (hA_meas n)] with records hrecords
      change (M.canonicalPathMap records).jumpCount T = n at hrecords
      change
        M.scaledCoordQVCompensator (M.canonicalPathMap records) i
            ((M.canonicalPathMap records).jumpCount T) =
          M.scaledCoordQVCompensator (M.canonicalPathMap records) i n
      rw [hrecords]
    exact hG.congr hFG.symm
  have hUnion : AEStronglyMeasurable F (μ.restrict (⋃ n, A n)) :=
    AEStronglyMeasurable.iUnion hpieces
  simpa [F, μ, ← hcover] using hUnion

/-- The finite embedded-martingale supremum sampled at a fixed clock-time
jump count is a.e. strongly measurable. -/
theorem aestronglyMeasurable_scaledJumpMartingale_finSup_sq_jumpCount
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (T : ℝ) :
    AEStronglyMeasurable
      (fun records : M.canonicalRecordΩ =>
        ((Finset.range ((M.canonicalPathMap records).jumpCount T + 1)).sup'
          Finset.nonempty_range_add_one
          (fun k =>
            ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2)
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let A : ℕ → Set M.canonicalRecordΩ := fun n =>
    {records | (M.canonicalPathMap records).jumpCount T = n}
  let F : M.canonicalRecordΩ → ℝ := fun records =>
    ((Finset.range ((M.canonicalPathMap records).jumpCount T + 1)).sup'
      Finset.nonempty_range_add_one
      (fun k =>
        ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2
  let G : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k =>
        ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2
  have hA_meas : ∀ n, MeasurableSet (A n) := by
    intro n
    simpa [A] using M.measurableSet_canonicalPathMap_jumpCount_eq T n
  have hcover : (Set.univ : Set M.canonicalRecordΩ) = ⋃ n, A n := by
    ext records
    simp [A]
  have hpieces : ∀ n, AEStronglyMeasurable F (μ.restrict (A n)) := by
    intro n
    have hG_meas : Measurable (G n) := by
      exact (Finset.measurable_range_sup'' (fun k _hk =>
        (((M.stronglyAdapted_scaledJumpMartingale_canonicalRecordFiltration i k).mono
          (M.canonicalRecordFiltration.le k)).measurable.norm))).pow_const 2
    have hFG : F =ᵐ[μ.restrict (A n)] G n := by
      filter_upwards [ae_restrict_mem (hA_meas n)] with records hrecords
      change (M.canonicalPathMap records).jumpCount T = n at hrecords
      change
        ((Finset.range ((M.canonicalPathMap records).jumpCount T + 1)).sup'
          Finset.nonempty_range_add_one
          (fun k =>
            ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2 =
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k =>
            ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2
      rw [hrecords]
    exact hG_meas.aestronglyMeasurable.mono_measure Measure.restrict_le_self
      |>.congr hFG.symm
  have hUnion : AEStronglyMeasurable F (μ.restrict (⋃ n, A n)) :=
    AEStronglyMeasurable.iUnion hpieces
  simpa [F, μ, ← hcover] using hUnion

/-- The finite completed-residual supremum sampled at a fixed clock-time jump
count is a.e. strongly measurable. -/
theorem aestronglyMeasurable_residual_finSup_sq_jumpCount
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (T : ℝ) :
    AEStronglyMeasurable
      (fun records : M.canonicalRecordΩ =>
        ((Finset.range ((M.canonicalPathMap records).jumpCount T + 1)).sup'
          Finset.nonempty_range_add_one
          (fun k =>
            ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖)) ^ 2)
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let A : ℕ → Set M.canonicalRecordΩ := fun n =>
    {records | (M.canonicalPathMap records).jumpCount T = n}
  let F : M.canonicalRecordΩ → ℝ := fun records =>
    ((Finset.range ((M.canonicalPathMap records).jumpCount T + 1)).sup'
      Finset.nonempty_range_add_one
      (fun k =>
        ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖)) ^ 2
  let G : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k =>
        ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖)) ^ 2
  have hA_meas : ∀ n, MeasurableSet (A n) := by
    intro n
    simpa [A] using M.measurableSet_canonicalPathMap_jumpCount_eq T n
  have hcover : (Set.univ : Set M.canonicalRecordΩ) = ⋃ n, A n := by
    ext records
    simp [A]
  have hpieces : ∀ n, AEStronglyMeasurable F (μ.restrict (A n)) := by
    intro n
    have hG_meas : Measurable (G n) := by
      exact (Finset.measurable_range_sup'' (fun k _hk =>
        (((M.stronglyAdapted_scaledHoldingTimeDriftResidual_canonicalRecordFiltration
          i k).mono (M.canonicalRecordFiltration.le k)).measurable.norm))).pow_const 2
    have hFG : F =ᵐ[μ.restrict (A n)] G n := by
      filter_upwards [ae_restrict_mem (hA_meas n)] with records hrecords
      change (M.canonicalPathMap records).jumpCount T = n at hrecords
      change
        ((Finset.range ((M.canonicalPathMap records).jumpCount T + 1)).sup'
          Finset.nonempty_range_add_one
          (fun k =>
            ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖)) ^ 2 =
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k =>
            ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖)) ^ 2
      rw [hrecords]
    exact hG_meas.aestronglyMeasurable.mono_measure Measure.restrict_le_self
      |>.congr hFG.symm
  have hUnion : AEStronglyMeasurable F (μ.restrict (⋃ n, A n)) :=
    AEStronglyMeasurable.iUnion hpieces
  simpa [F, μ, ← hcover] using hUnion

/-- Fixed-index completed-sojourn coordinate-QV sums are measurable as
functions of the canonical record trajectory. -/
theorem measurable_sum_instantCoordQVRate_mul_sojournTime
    (M : DensityDepCTMC d) (i : Fin d) (n : ℕ) :
    Measurable
      (fun records : M.canonicalRecordΩ =>
        ∑ k ∈ Finset.range n,
          M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
            (M.canonicalPathMap records).sojournTime k) := by
  refine Finset.measurable_sum _ ?_
  intro k _hk
  have hstate :
      Measurable
        (fun records : M.canonicalRecordΩ =>
          M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i) :=
    ((Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) =>
        M.instantCoordQVRate x i)).comp
          ((M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration k).mono
            (M.canonicalRecordFiltration.le k) le_rfl))
  have hsoj :
      Measurable
        (fun records : M.canonicalRecordΩ =>
          (M.canonicalPathMap records).sojournTime k) := by
    simpa [canonicalPathMap, QMatrix.recordTrajectoryToPath_sojournTime] using
      (measurable_fst.comp (measurable_pi_apply (k + 1) :
        Measurable (fun records : M.canonicalRecordΩ => records (k + 1))))
  exact hstate.mul hsoj

/-- The completed-sojourn coordinate-QV sum sampled at a fixed clock-time
jump count is a.e. strongly measurable. -/
theorem aestronglyMeasurable_sum_instantCoordQVRate_mul_sojournTime_jumpCount
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (T : ℝ) :
    AEStronglyMeasurable
      (fun records : M.canonicalRecordΩ =>
        ∑ k ∈ Finset.range ((M.canonicalPathMap records).jumpCount T),
          M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
            (M.canonicalPathMap records).sojournTime k)
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let A : ℕ → Set M.canonicalRecordΩ := fun n =>
    {records | (M.canonicalPathMap records).jumpCount T = n}
  let F : M.canonicalRecordΩ → ℝ := fun records =>
    ∑ k ∈ Finset.range ((M.canonicalPathMap records).jumpCount T),
      M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
        (M.canonicalPathMap records).sojournTime k
  let G : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    ∑ k ∈ Finset.range n,
      M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
        (M.canonicalPathMap records).sojournTime k
  have hA_meas : ∀ n, MeasurableSet (A n) := by
    intro n
    simpa [A] using M.measurableSet_canonicalPathMap_jumpCount_eq T n
  have hcover : (Set.univ : Set M.canonicalRecordΩ) = ⋃ n, A n := by
    ext records
    simp [A]
  have hpieces : ∀ n, AEStronglyMeasurable F (μ.restrict (A n)) := by
    intro n
    have hG : AEStronglyMeasurable (G n) (μ.restrict (A n)) :=
      (M.measurable_sum_instantCoordQVRate_mul_sojournTime i n).aestronglyMeasurable
        |>.mono_measure Measure.restrict_le_self
    have hFG : F =ᵐ[μ.restrict (A n)] G n := by
      filter_upwards [ae_restrict_mem (hA_meas n)] with records hrecords
      change (M.canonicalPathMap records).jumpCount T = n at hrecords
      change
        (∑ k ∈ Finset.range ((M.canonicalPathMap records).jumpCount T),
          M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
            (M.canonicalPathMap records).sojournTime k) =
        (∑ k ∈ Finset.range n,
          M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
            (M.canonicalPathMap records).sojournTime k)
      rw [hrecords]
    exact hG.congr hFG.symm
  have hUnion : AEStronglyMeasurable F (μ.restrict (⋃ n, A n)) :=
    AEStronglyMeasurable.iUnion hpieces
  simpa [F, μ, ← hcover] using hUnion

/-- The canonical sojourn start at a fixed index is measurable. -/
theorem measurable_canonicalPathMap_sojournStart
    (M : DensityDepCTMC d) (n : ℕ) :
    Measurable
      (fun records : M.canonicalRecordΩ =>
        (M.canonicalPathMap records).sojournStart n) := by
  cases n with
  | zero =>
      simp [CTMCPath.sojournStart]
  | succ n =>
      simpa [canonicalPathMap, CTMCPath.sojournStart] using
        (QMatrix.measurable_recordTrajectoryToPath_times
          (S := Fin d → Fin (M.N + 1)) n)

/-- The event that the `n`-th canonical jump time is after a fixed clock time
is measurable with respect to the record history through `n+1`. -/
theorem measurableSet_canonicalPathMap_time_gt_canonicalRecordFiltration
    (M : DensityDepCTMC d) (T : ℝ) (n : ℕ) :
    MeasurableSet[M.canonicalRecordFiltration (n + 1)]
      {records : M.canonicalRecordΩ |
        T < (M.canonicalPathMap records).times n} := by
  simpa [canonicalPathMap] using
    (QMatrix.measurableSet_recordTrajectoryToPath_time_gt_canonicalRecordFiltration
      (S := Fin d → Fin (M.N + 1)) T n)

/-- Shifted-stopping finite-level events for the WithTop clock-horizon jump
index are measurable in the canonical density-dependent record filtration. -/
theorem measurableSet_canonicalPathMap_jumpCountTop_le_canonicalRecordFiltration
    (M : DensityDepCTMC d) (T : ℝ) (n : ℕ) :
    MeasurableSet[M.canonicalRecordFiltration (n + 1)]
      {records : M.canonicalRecordΩ |
        (M.canonicalPathMap records).jumpCountTop T ≤ (n : WithTop ℕ)} := by
  simpa [canonicalPathMap] using
    (QMatrix.measurableSet_recordTrajectoryToPath_jumpCountTop_le_canonicalRecordFiltration
      (S := Fin d → Fin (M.N + 1)) T n)

/-- The WithTop clock-horizon jump index is a stopping time for the shifted
density-dependent canonical record filtration. -/
theorem isStoppingTime_canonicalPathMap_jumpCountTop_shifted
    (M : DensityDepCTMC d) (T : ℝ) :
    MeasureTheory.IsStoppingTime M.shiftedCanonicalRecordFiltration
      (fun records : M.canonicalRecordΩ =>
        (M.canonicalPathMap records).jumpCountTop T) := by
  simpa [shiftedCanonicalRecordFiltration, canonicalPathMap] using
    (QMatrix.isStoppingTime_recordTrajectoryToPath_jumpCountTop_shifted
      (S := Fin d → Fin (M.N + 1)) T)

/-- Under the canonical non-explosive law, `jumpCountTop` agrees a.s. with the
finite `jumpCount` embedded in `WithTop`. -/
theorem canonicalPathMap_jumpCountTop_eq_jumpCount_ae_of_noAbsorbing
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (hNA : M.NoAbsorbing) (T : ℝ) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      (M.canonicalPathMap records).jumpCountTop T =
        ((M.canonicalPathMap records).jumpCount T : WithTop ℕ) := by
  filter_upwards [M.canonicalPathMap_nonExplosive_ae_of_noAbsorbing x₀ hNA]
    with records hne
  exact (M.canonicalPathMap records).jumpCountTop_eq_jumpCount_of_exists
    ((M.canonicalPathMap records).exists_bound_of_nonExplosive hne T)

/-- Under the canonical non-explosive law, the WithTop clock-horizon jump index
is finite a.s. -/
theorem canonicalPathMap_jumpCountTop_ne_top_ae_of_noAbsorbing
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (hNA : M.NoAbsorbing) (T : ℝ) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      (M.canonicalPathMap records).jumpCountTop T ≠ ⊤ := by
  filter_upwards
    [M.canonicalPathMap_jumpCountTop_eq_jumpCount_ae_of_noAbsorbing x₀ hNA T]
    with records heq
  simp [heq]

/-- Truncated stopping of the coordinate QV compensator at
`jumpCountTop T ∧ N` is integrable. -/
theorem integrable_scaledCoordQVCompensator_jumpCountTop_min
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (T : ℝ) (N : ℕ) :
    Integrable
      (MeasureTheory.stoppedValue
        (fun n records =>
          M.scaledCoordQVCompensator (M.canonicalPathMap records) i n)
        (fun records : M.canonicalRecordΩ =>
          min ((M.canonicalPathMap records).jumpCountTop T) (N : WithTop ℕ)))
      (M.canonicalRecordMeasure x₀) := by
  have hτ :
      MeasureTheory.IsStoppingTime M.shiftedCanonicalRecordFiltration
        (fun records : M.canonicalRecordΩ =>
          min ((M.canonicalPathMap records).jumpCountTop T) (N : WithTop ℕ)) :=
    (M.isStoppingTime_canonicalPathMap_jumpCountTop_shifted T).min_const N
  have hu : ∀ n : ℕ,
      Integrable
        (fun records : M.canonicalRecordΩ =>
          M.scaledCoordQVCompensator (M.canonicalPathMap records) i n)
        (M.canonicalRecordMeasure x₀) :=
    fun n => M.integrable_scaledCoordQVCompensator_canonicalRecordMeasure x₀ i n
  exact MeasureTheory.integrable_stoppedValue ℕ hτ hu (N := N) (by
    intro records
    exact min_le_right _ _)

/-- Truncated stopping of the squared embedded coordinate martingale at
`jumpCountTop T ∧ N` is integrable. -/
theorem integrable_scaledJumpMartingale_sq_jumpCountTop_min
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (T : ℝ) (N : ℕ) :
    Integrable
      (MeasureTheory.stoppedValue
        (fun n records =>
          (M.scaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2)
        (fun records : M.canonicalRecordΩ =>
          min ((M.canonicalPathMap records).jumpCountTop T) (N : WithTop ℕ)))
      (M.canonicalRecordMeasure x₀) := by
  have hτ :
      MeasureTheory.IsStoppingTime M.shiftedCanonicalRecordFiltration
        (fun records : M.canonicalRecordΩ =>
          min ((M.canonicalPathMap records).jumpCountTop T) (N : WithTop ℕ)) :=
    (M.isStoppingTime_canonicalPathMap_jumpCountTop_shifted T).min_const N
  have hu : ∀ n : ℕ,
      Integrable
        (fun records : M.canonicalRecordΩ =>
          (M.scaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2)
        (M.canonicalRecordMeasure x₀) :=
    fun n => M.integrable_scaledJumpMartingale_sq_canonicalRecordMeasure x₀ i n
  exact MeasureTheory.integrable_stoppedValue ℕ hτ hu (N := N) (by
    intro records
    exact min_le_right _ _)

/-- The current partial-sojourn coordinate-QV term sampled at `jumpCount T` is
a.e. strongly measurable. -/
theorem aestronglyMeasurable_currentSojourn_instantCoordQVRate_mul_elapsed_jumpCount
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (T : ℝ) :
    AEStronglyMeasurable
      (fun records : M.canonicalRecordΩ =>
        M.instantCoordQVRate
            ((M.canonicalPathMap records).stateSeq
              ((M.canonicalPathMap records).jumpCount T)) i *
          (M.canonicalPathMap records).currentSojournElapsed T)
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let A : ℕ → Set M.canonicalRecordΩ := fun n =>
    {records | (M.canonicalPathMap records).jumpCount T = n}
  let F : M.canonicalRecordΩ → ℝ := fun records =>
    M.instantCoordQVRate
        ((M.canonicalPathMap records).stateSeq
          ((M.canonicalPathMap records).jumpCount T)) i *
      (M.canonicalPathMap records).currentSojournElapsed T
  let G : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq n) i *
      (T - (M.canonicalPathMap records).sojournStart n)
  have hA_meas : ∀ n, MeasurableSet (A n) := by
    intro n
    simpa [A] using M.measurableSet_canonicalPathMap_jumpCount_eq T n
  have hcover : (Set.univ : Set M.canonicalRecordΩ) = ⋃ n, A n := by
    ext records
    simp [A]
  have hpieces : ∀ n, AEStronglyMeasurable F (μ.restrict (A n)) := by
    intro n
    have hstate :
        Measurable
          (fun records : M.canonicalRecordΩ =>
            M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq n) i) :=
      ((Measurable.of_discrete
        (f := fun x : Fin d → Fin (M.N + 1) =>
          M.instantCoordQVRate x i)).comp
            ((M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration n).mono
              (M.canonicalRecordFiltration.le n) le_rfl))
    have hstart : Measurable
        (fun records : M.canonicalRecordΩ =>
          (M.canonicalPathMap records).sojournStart n) :=
      M.measurable_canonicalPathMap_sojournStart n
    have hG : AEStronglyMeasurable (G n) (μ.restrict (A n)) :=
      (hstate.mul (measurable_const.sub hstart)).aestronglyMeasurable
        |>.mono_measure Measure.restrict_le_self
    have hFG : F =ᵐ[μ.restrict (A n)] G n := by
      filter_upwards [ae_restrict_mem (hA_meas n)] with records hrecords
      change (M.canonicalPathMap records).jumpCount T = n at hrecords
      change
        M.instantCoordQVRate
            ((M.canonicalPathMap records).stateSeq
              ((M.canonicalPathMap records).jumpCount T)) i *
          (M.canonicalPathMap records).currentSojournElapsed T =
        M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq n) i *
          (T - (M.canonicalPathMap records).sojournStart n)
      rw [CTMCPath.currentSojournElapsed, hrecords]
    exact hG.congr hFG.symm
  have hUnion : AEStronglyMeasurable F (μ.restrict (⋃ n, A n)) :=
    AEStronglyMeasurable.iUnion hpieces
  simpa [F, μ, ← hcover] using hUnion

/-- The current partial-sojourn coordinate-QV contribution is integrable on a
finite horizon. -/
theorem integrable_currentSojourn_instantCoordQVRate_mul_elapsed_jumpCount
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (hNA : M.NoAbsorbing) (i : Fin d) (T : ℝ) (hT : 0 ≤ T) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.instantCoordQVRate
            ((M.canonicalPathMap records).stateSeq
              ((M.canonicalPathMap records).jumpCount T)) i *
          (M.canonicalPathMap records).currentSojournElapsed T)
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let F : M.canonicalRecordΩ → ℝ := fun records =>
    M.instantCoordQVRate
        ((M.canonicalPathMap records).stateSeq
          ((M.canonicalPathMap records).jumpCount T)) i *
      (M.canonicalPathMap records).currentSojournElapsed T
  obtain ⟨C, hC_nonneg, hC⟩ := M.exists_instantCoordQVRate_abs_bound i
  have hF_sm : AEStronglyMeasurable F μ := by
    simpa [F, μ] using
      M.aestronglyMeasurable_currentSojourn_instantCoordQVRate_mul_elapsed_jumpCount
        x₀ i T
  have hbound :
      ∀ᵐ records ∂μ, ‖F records‖ ≤ C * T := by
    filter_upwards
      [M.canonicalPathMap_isCompatible_ae_of_noAbsorbing x₀ hNA,
        M.canonicalPathMap_nonExplosive_ae_of_noAbsorbing x₀ hNA]
      with records hcompat hne
    have hel0 :
        0 ≤ (M.canonicalPathMap records).currentSojournElapsed T :=
      (M.canonicalPathMap records).currentSojournElapsed_nonneg hT
        ((M.canonicalPathMap records).exists_bound_of_nonExplosive hne T)
    have helT :
        (M.canonicalPathMap records).currentSojournElapsed T ≤ T :=
      (M.canonicalPathMap records).currentSojournElapsed_le hcompat.2.1 hcompat.1
    have hnorm_el :
        ‖(M.canonicalPathMap records).currentSojournElapsed T‖ ≤ T := by
      rw [Real.norm_eq_abs, abs_of_nonneg hel0]
      exact helT
    change
      ‖M.instantCoordQVRate
          ((M.canonicalPathMap records).stateSeq
            ((M.canonicalPathMap records).jumpCount T)) i *
        (M.canonicalPathMap records).currentSojournElapsed T‖ ≤ C * T
    rw [norm_mul]
    exact mul_le_mul
      (hC ((M.canonicalPathMap records).stateSeq
        ((M.canonicalPathMap records).jumpCount T)))
      hnorm_el
      (norm_nonneg _)
      hC_nonneg
  exact (integrable_const (C * T)).mono' hF_sm hbound

/-- For the canonical record-law realization, the density process at a fixed
time is measurable. -/
theorem measurable_canonicalDensityProcess (M : DensityDepCTMC d) (t : ℝ) :
    Measurable (fun records : M.canonicalRecordΩ =>
      M.densityProcess M.canonicalPathMap t records) := by
  rw [measurable_pi_iff]
  intro i
  unfold densityProcess scaledState
  have hstate_i : Measurable (fun records : M.canonicalRecordΩ =>
      ((M.canonicalPathMap records).stateAt t) i) :=
    (measurable_pi_apply i).comp (M.measurable_canonicalPathMap_stateAt t)
  exact (Measurable.of_discrete
    (f := fun x : Fin (M.N + 1) => (x : ℝ) / (M.N : ℝ))).comp hstate_i

/-- For the canonical record-law realization, the instantaneous QV-rate
integrand at a fixed time is measurable. -/
theorem measurable_canonicalInstantQVRate (M : DensityDepCTMC d) (t : ℝ) :
    Measurable (fun records : M.canonicalRecordΩ =>
      M.instantQVRate ((M.canonicalPathMap records).stateAt t)) := by
  exact (Measurable.of_discrete
    (f := fun x : Fin d → Fin (M.N + 1) => M.instantQVRate x)).comp
      (M.measurable_canonicalPathMap_stateAt t)

/-- For the canonical record-law realization, the state readout is jointly
measurable in clock time and record trajectory. -/
theorem measurable_prod_canonicalPathMap_stateAt (M : DensityDepCTMC d) :
    Measurable (fun p : ℝ × M.canonicalRecordΩ =>
      (M.canonicalPathMap p.2).stateAt p.1) := by
  simpa [canonicalPathMap] using
    (QMatrix.measurable_prod_recordTrajectoryToPath_stateAt
      (S := Fin d → Fin (M.N + 1)))

/-- For the canonical record-law realization, the density process is jointly
measurable in clock time and record trajectory. -/
theorem measurable_prod_canonicalDensityProcess (M : DensityDepCTMC d) :
    Measurable (fun p : ℝ × M.canonicalRecordΩ =>
      M.densityProcess M.canonicalPathMap p.1 p.2) := by
  rw [measurable_pi_iff]
  intro i
  unfold densityProcess scaledState
  have hstate_i : Measurable (fun p : ℝ × M.canonicalRecordΩ =>
      ((M.canonicalPathMap p.2).stateAt p.1) i) :=
    (measurable_pi_apply i).comp M.measurable_prod_canonicalPathMap_stateAt
  exact (Measurable.of_discrete
    (f := fun x : Fin (M.N + 1) => (x : ℝ) / (M.N : ℝ))).comp hstate_i

/-- For the canonical record-law realization, the instantaneous QV-rate
integrand is jointly measurable in clock time and record trajectory. -/
theorem measurable_prod_canonicalInstantQVRate (M : DensityDepCTMC d) :
    Measurable (fun p : ℝ × M.canonicalRecordΩ =>
      M.instantQVRate ((M.canonicalPathMap p.2).stateAt p.1)) := by
  exact (Measurable.of_discrete
    (f := fun x : Fin d → Fin (M.N + 1) => M.instantQVRate x)).comp
      M.measurable_prod_canonicalPathMap_stateAt

/-- For the canonical record-law realization, a coordinate instantaneous
QV-rate integrand is jointly measurable in clock time and record trajectory. -/
theorem measurable_prod_canonicalInstantCoordQVRate
    (M : DensityDepCTMC d) (i : Fin d) :
    Measurable (fun p : ℝ × M.canonicalRecordΩ =>
      M.instantCoordQVRate ((M.canonicalPathMap p.2).stateAt p.1) i) := by
  exact (Measurable.of_discrete
    (f := fun x : Fin d → Fin (M.N + 1) => M.instantCoordQVRate x i)).comp
      M.measurable_prod_canonicalPathMap_stateAt

/-- For the canonical record-law realization, a coordinate generator-drift
integrand is jointly measurable in clock time and record trajectory. -/
theorem measurable_prod_canonicalGeneratorDrift_component
    (M : DensityDepCTMC d) (i : Fin d) :
    Measurable (fun p : ℝ × M.canonicalRecordΩ =>
      M.generatorDrift ((M.canonicalPathMap p.2).stateAt p.1) i) := by
  exact (Measurable.of_discrete
    (f := fun x : Fin d → Fin (M.N + 1) => M.generatorDrift x i)).comp
      M.measurable_prod_canonicalPathMap_stateAt

/-- The finite-horizon time integral of the canonical instantaneous QV-rate is
measurable as a function of the record trajectory. -/
theorem measurable_canonicalInstantQVRate_setIntegral
    (M : DensityDepCTMC d) (T : ℝ) :
    Measurable (fun records : M.canonicalRecordΩ =>
      ∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).stateAt s)) := by
  have hjoint : StronglyMeasurable
      (fun p : M.canonicalRecordΩ × ℝ =>
        M.instantQVRate ((M.canonicalPathMap p.1).stateAt p.2)) :=
    (M.measurable_prod_canonicalInstantQVRate.comp measurable_swap).stronglyMeasurable
  exact (hjoint.integral_prod_right'
    (ν := MeasureTheory.Measure.restrict volume (Set.Icc 0 T))).measurable

/-- The finite-horizon time integral of a canonical coordinate instantaneous
QV-rate is measurable as a function of the record trajectory. -/
theorem measurable_canonicalInstantCoordQVRate_setIntegral
    (M : DensityDepCTMC d) (i : Fin d) (T : ℝ) :
    Measurable (fun records : M.canonicalRecordΩ =>
      ∫ s in Set.Icc (0 : ℝ) T,
        M.instantCoordQVRate ((M.canonicalPathMap records).stateAt s) i) := by
  have hjoint : StronglyMeasurable
      (fun p : M.canonicalRecordΩ × ℝ =>
        M.instantCoordQVRate ((M.canonicalPathMap p.1).stateAt p.2) i) :=
    (M.measurable_prod_canonicalInstantCoordQVRate i |>.comp measurable_swap).stronglyMeasurable
  exact (hjoint.integral_prod_right'
    (ν := MeasureTheory.Measure.restrict volume (Set.Icc 0 T))).measurable

/-- The canonical instantaneous-QV time integral is nonnegative pathwise. -/
theorem canonical_instantQVRate_setIntegral_nonneg
    (M : DensityDepCTMC d) (T : ℝ) (records : M.canonicalRecordΩ) :
    0 ≤ ∫ s in Set.Icc (0 : ℝ) T,
      M.instantQVRate ((M.canonicalPathMap records).stateAt s) := by
  exact setIntegral_nonneg measurableSet_Icc fun s _ =>
    M.instantQVRate_nonneg ((M.canonicalPathMap records).stateAt s)

/-- The canonical coordinate instantaneous-QV time integral is nonnegative
pathwise. -/
theorem canonical_instantCoordQVRate_setIntegral_nonneg
    (M : DensityDepCTMC d) (i : Fin d) (T : ℝ)
    (records : M.canonicalRecordΩ) :
    0 ≤ ∫ s in Set.Icc (0 : ℝ) T,
      M.instantCoordQVRate ((M.canonicalPathMap records).stateAt s) i := by
  exact setIntegral_nonneg measurableSet_Icc fun s _ =>
    M.instantCoordQVRate_nonneg ((M.canonicalPathMap records).stateAt s) i

set_option maxHeartbeats 800000 in
-- Section measurability through the canonical path readout is expensive here.
/-- Along a fixed canonical record trajectory, the instantaneous-QV rate is
integrable on a finite clock-time interval. -/
theorem integrableOn_canonicalInstantQVRate_Icc
    (M : DensityDepCTMC d) (records : M.canonicalRecordΩ)
    (T : ℝ) :
    IntegrableOn
      (fun s : ℝ => M.instantQVRate ((M.canonicalPathMap records).stateAt s))
      (Set.Icc (0 : ℝ) T) volume := by
  obtain ⟨C, hC, hbound⟩ :=
    M.exists_instantQVRate_path_bound M.canonicalPathMap
  have hmeas : Measurable
      (fun s : ℝ => M.instantQVRate ((M.canonicalPathMap records).stateAt s)) := by
    let sec : ℝ → ℝ × M.canonicalRecordΩ := fun s => (s, records)
    have hsec : Measurable sec :=
      (Measurable.prodMk measurable_id measurable_const :
        Measurable (fun s : ℝ => (s, records)))
    exact M.measurable_prod_canonicalInstantQVRate.comp hsec
  refine IntegrableOn.of_bound measure_Icc_lt_top
    hmeas.aestronglyMeasurable (C / (M.N : ℝ)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s _hs
  rw [Real.norm_eq_abs]
  refine abs_le.mpr ⟨?_, hbound s records⟩
  have hnonneg : 0 ≤ M.instantQVRate ((M.canonicalPathMap records).stateAt s) :=
    M.instantQVRate_nonneg ((M.canonicalPathMap records).stateAt s)
  have hCdiv_nonneg : 0 ≤ C / (M.N : ℝ) := by positivity
  linarith

set_option maxHeartbeats 800000 in
-- Section measurability through the canonical path readout is expensive here.
/-- Along a fixed canonical record trajectory, a coordinate instantaneous-QV rate
is integrable on a finite clock-time interval. -/
theorem integrableOn_canonicalInstantCoordQVRate_Icc
    (M : DensityDepCTMC d) (records : M.canonicalRecordΩ)
    (i : Fin d) (T : ℝ) :
    IntegrableOn
      (fun s : ℝ =>
        M.instantCoordQVRate ((M.canonicalPathMap records).stateAt s) i)
      (Set.Icc (0 : ℝ) T) volume := by
  obtain ⟨C, hC, hbound⟩ :=
    M.exists_instantCoordQVRate_path_bound M.canonicalPathMap i
  have hmeas : Measurable
      (fun s : ℝ =>
        M.instantCoordQVRate ((M.canonicalPathMap records).stateAt s) i) := by
    let sec : ℝ → ℝ × M.canonicalRecordΩ := fun s => (s, records)
    have hsec : Measurable sec :=
      (Measurable.prodMk measurable_id measurable_const :
        Measurable (fun s : ℝ => (s, records)))
    exact (M.measurable_prod_canonicalInstantCoordQVRate i).comp hsec
  refine IntegrableOn.of_bound measure_Icc_lt_top
    hmeas.aestronglyMeasurable (C / (M.N : ℝ)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s _hs
  rw [Real.norm_eq_abs]
  refine abs_le.mpr ⟨?_, hbound s records⟩
  have hnonneg :
      0 ≤ M.instantCoordQVRate ((M.canonicalPathMap records).stateAt s) i :=
    M.instantCoordQVRate_nonneg ((M.canonicalPathMap records).stateAt s) i
  have hCdiv_nonneg : 0 ≤ C / (M.N : ℝ) := by positivity
  linarith

set_option maxHeartbeats 800000 in
-- Section measurability through the canonical path readout is expensive here.
/-- Along a fixed canonical record trajectory, a coordinate generator-drift
integrand is integrable on a finite clock-time interval. -/
theorem integrableOn_canonicalGeneratorDrift_component_Icc
    (M : DensityDepCTMC d) (records : M.canonicalRecordΩ)
    (i : Fin d) (T : ℝ) :
    IntegrableOn
      (fun s : ℝ => M.generatorDrift ((M.canonicalPathMap records).stateAt s) i)
      (Set.Icc (0 : ℝ) T) volume := by
  obtain ⟨C, _hC_nonneg, hC⟩ := M.exists_generatorDrift_abs_bound i
  have hmeas : Measurable
      (fun s : ℝ =>
        M.generatorDrift ((M.canonicalPathMap records).stateAt s) i) := by
    let sec : ℝ → ℝ × M.canonicalRecordΩ := fun s => (s, records)
    have hsec : Measurable sec :=
      (Measurable.prodMk measurable_id measurable_const :
        Measurable (fun s : ℝ => (s, records)))
    exact (M.measurable_prod_canonicalGeneratorDrift_component i).comp hsec
  refine IntegrableOn.of_bound measure_Icc_lt_top hmeas.aestronglyMeasurable C ?_
  filter_upwards with s
  exact hC ((M.canonicalPathMap records).stateAt s)

/-- The canonical instantaneous-QV time integral is integrable on finite
horizons. -/
theorem integrable_canonicalInstantQVRate_setIntegral
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (hT : 0 ≤ T) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        ∫ s in Set.Icc (0 : ℝ) T,
          M.instantQVRate ((M.canonicalPathMap records).stateAt s))
      (M.canonicalRecordMeasure x₀) := by
  obtain ⟨C, _hC, hbound⟩ :=
    M.exists_instantQVRate_path_setIntegral_bound M.canonicalPathMap T hT
  refine MeasureTheory.Integrable.of_bound
    (M.measurable_canonicalInstantQVRate_setIntegral T).aestronglyMeasurable
    (C * T / (M.N : ℝ)) ?_
  filter_upwards with records
  rw [Real.norm_eq_abs,
    abs_of_nonneg (M.canonical_instantQVRate_setIntegral_nonneg T records)]
  exact hbound records

/-- A canonical coordinate instantaneous-QV time integral is integrable on
finite horizons. -/
theorem integrable_canonicalInstantCoordQVRate_setIntegral
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (T : ℝ) (hT : 0 ≤ T) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        ∫ s in Set.Icc (0 : ℝ) T,
          M.instantCoordQVRate ((M.canonicalPathMap records).stateAt s) i)
      (M.canonicalRecordMeasure x₀) := by
  obtain ⟨C, _hC, hbound⟩ :=
    M.exists_instantCoordQVRate_path_setIntegral_bound M.canonicalPathMap i T hT
  refine MeasureTheory.Integrable.of_bound
    (M.measurable_canonicalInstantCoordQVRate_setIntegral i T).aestronglyMeasurable
    (C * T / (M.N : ℝ)) ?_
  filter_upwards with records
  rw [Real.norm_eq_abs,
    abs_of_nonneg (M.canonical_instantCoordQVRate_setIntegral_nonneg i T records)]
  exact hbound records

/-- On canonical non-explosive paths, the completed-sojourn contribution of a
coordinate instantaneous-QV rate is bounded by its clock-time integral over the
horizon.  This is the deterministic half of the compensator bridge. -/
theorem canonical_sum_instantCoordQVRate_mul_sojournTime_le_setIntegral_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (hNA : M.NoAbsorbing) (i : Fin d) (T : ℝ) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      (∑ k ∈ Finset.range ((M.canonicalPathMap records).jumpCount T),
        M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
          (M.canonicalPathMap records).sojournTime k) ≤
        ∫ s in Set.Icc (0 : ℝ) T,
          M.instantCoordQVRate ((M.canonicalPathMap records).stateAt s) i := by
  filter_upwards
    [M.canonicalPathMap_isCompatible_ae_of_noAbsorbing x₀ hNA,
      M.canonicalPathMap_nonExplosive_ae_of_noAbsorbing x₀ hNA]
    with records hcompat hne
  exact (M.canonicalPathMap records).sum_sojournTime_mul_le_setIntegral_Icc
    hcompat.2.1 hcompat.1
    (fun x => M.instantCoordQVRate x i)
    ((M.canonicalPathMap records).exists_bound_of_nonExplosive hne T)
    (fun x => M.instantCoordQVRate_nonneg x i)
    (M.integrableOn_canonicalInstantCoordQVRate_Icc records i T)

/-- The completed-sojourn coordinate-QV contribution up to the random jump
count at `T` is integrable. -/
theorem integrable_sum_instantCoordQVRate_mul_sojournTime_jumpCount
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (hNA : M.NoAbsorbing) (i : Fin d) (T : ℝ) (hT : 0 ≤ T) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        ∑ k ∈ Finset.range ((M.canonicalPathMap records).jumpCount T),
          M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
            (M.canonicalPathMap records).sojournTime k)
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let L : M.canonicalRecordΩ → ℝ := fun records =>
    ∑ k ∈ Finset.range ((M.canonicalPathMap records).jumpCount T),
      M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
        (M.canonicalPathMap records).sojournTime k
  let R : M.canonicalRecordΩ → ℝ := fun records =>
    ∫ s in Set.Icc (0 : ℝ) T,
      M.instantCoordQVRate ((M.canonicalPathMap records).stateAt s) i
  have hL_sm : AEStronglyMeasurable L μ := by
    simpa [L, μ] using
      M.aestronglyMeasurable_sum_instantCoordQVRate_mul_sojournTime_jumpCount
        x₀ i T
  have hR_int : Integrable R μ := by
    simpa [R, μ] using
      M.integrable_canonicalInstantCoordQVRate_setIntegral x₀ i T hT
  have hL_nonneg : 0 ≤ᵐ[μ] L := by
    filter_upwards [M.canonicalPathMap_isCompatible_ae_of_noAbsorbing x₀ hNA]
      with records hcompat
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg
        (M.instantCoordQVRate_nonneg ((M.canonicalPathMap records).stateSeq k) i)
        ((M.canonicalPathMap records).sojournTime_nonneg hcompat.2.1 hcompat.1 k)
  have hle : L ≤ᵐ[μ] R := by
    simpa [L, R, μ] using
      M.canonical_sum_instantCoordQVRate_mul_sojournTime_le_setIntegral_ae
        x₀ hNA i T
  have hnorm : ∀ᵐ records ∂μ, ‖L records‖ ≤ R records := by
    filter_upwards [hL_nonneg, hle] with records hL0 hLR
    rwa [Real.norm_eq_abs, abs_of_nonneg hL0]
  exact hR_int.mono' hL_sm hnorm

/-- Expectation form of the deterministic completed-sojourn lower bound. -/
theorem integral_sum_instantCoordQVRate_mul_sojournTime_le_integral_setIntegral
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (hNA : M.NoAbsorbing) (i : Fin d) (T : ℝ) (hT : 0 ≤ T) :
    ∫ records,
        (∑ k ∈ Finset.range ((M.canonicalPathMap records).jumpCount T),
          M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
            (M.canonicalPathMap records).sojournTime k)
        ∂M.canonicalRecordMeasure x₀ ≤
      ∫ records,
        (∫ s in Set.Icc (0 : ℝ) T,
          M.instantCoordQVRate ((M.canonicalPathMap records).stateAt s) i)
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let L : M.canonicalRecordΩ → ℝ := fun records =>
    ∑ k ∈ Finset.range ((M.canonicalPathMap records).jumpCount T),
      M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
        (M.canonicalPathMap records).sojournTime k
  let R : M.canonicalRecordΩ → ℝ := fun records =>
    ∫ s in Set.Icc (0 : ℝ) T,
      M.instantCoordQVRate ((M.canonicalPathMap records).stateAt s) i
  have hL_int : Integrable L μ := by
    simpa [L, μ] using
      M.integrable_sum_instantCoordQVRate_mul_sojournTime_jumpCount
        x₀ hNA i T hT
  have hR_int : Integrable R μ := by
    simpa [R, μ] using
      M.integrable_canonicalInstantCoordQVRate_setIntegral x₀ i T hT
  have hle : L ≤ᵐ[μ] R := by
    simpa [L, R, μ] using
      M.canonical_sum_instantCoordQVRate_mul_sojournTime_le_setIntegral_ae
        x₀ hNA i T
  exact integral_mono_ae hL_int hR_int hle

/-- On canonical paths, the coordinate-QV contribution over the current
partial sojourn interval has the expected constant-state form. -/
theorem canonical_currentSojourn_instantCoordQVRate_setIntegral_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (hNA : M.NoAbsorbing) (i : Fin d) (T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      (∫ s in Set.Icc
          ((M.canonicalPathMap records).sojournStart
            ((M.canonicalPathMap records).jumpCount T)) T,
        M.instantCoordQVRate ((M.canonicalPathMap records).stateAt s) i) =
        M.instantCoordQVRate
            ((M.canonicalPathMap records).stateSeq
              ((M.canonicalPathMap records).jumpCount T)) i *
          (M.canonicalPathMap records).currentSojournElapsed T := by
  filter_upwards
    [M.canonicalPathMap_isCompatible_ae_of_noAbsorbing x₀ hNA,
      M.canonicalPathMap_nonExplosive_ae_of_noAbsorbing x₀ hNA]
    with records hcompat hne
  exact (M.canonicalPathMap records).setIntegral_currentSojourn_stateAt
    hcompat.2.1
    (fun x => M.instantCoordQVRate x i)
    hT
    ((M.canonicalPathMap records).exists_bound_of_nonExplosive hne T)

/-- On canonical paths, the elapsed current-sojourn time is bounded in square
by the full current sojourn time. -/
theorem canonical_currentSojournElapsed_sq_le_sojournTime_sq_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (hNA : M.NoAbsorbing) (T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      (M.canonicalPathMap records).currentSojournElapsed T ^ 2 ≤
        (M.canonicalPathMap records).sojournTime
          ((M.canonicalPathMap records).jumpCount T) ^ 2 := by
  filter_upwards
    [M.canonicalPathMap_isCompatible_ae_of_noAbsorbing x₀ hNA,
      M.canonicalPathMap_nonExplosive_ae_of_noAbsorbing x₀ hNA]
    with records hcompat hne
  exact (M.canonicalPathMap records).currentSojournElapsed_sq_le_sojournTime_sq
    hcompat.2.1 hcompat.1 hT
    ((M.canonicalPathMap records).exists_bound_of_nonExplosive hne T)

/-- Canonical pathwise lower bound using both completed sojourns and the
current partial sojourn contribution. -/
theorem canonical_sum_instantCoordQVRate_mul_sojournTime_add_currentSojourn_le_setIntegral_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (hNA : M.NoAbsorbing) (i : Fin d) (T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      (∑ k ∈ Finset.range ((M.canonicalPathMap records).jumpCount T),
        M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
          (M.canonicalPathMap records).sojournTime k) +
        M.instantCoordQVRate
            ((M.canonicalPathMap records).stateSeq
              ((M.canonicalPathMap records).jumpCount T)) i *
          (M.canonicalPathMap records).currentSojournElapsed T ≤
        ∫ s in Set.Icc (0 : ℝ) T,
          M.instantCoordQVRate ((M.canonicalPathMap records).stateAt s) i := by
  filter_upwards
    [M.canonicalPathMap_isCompatible_ae_of_noAbsorbing x₀ hNA,
      M.canonicalPathMap_nonExplosive_ae_of_noAbsorbing x₀ hNA]
    with records hcompat hne
  exact (M.canonicalPathMap records).sum_sojournTime_mul_add_currentSojourn_le_setIntegral_Icc
    hcompat.2.1 hcompat.1
    (fun x => M.instantCoordQVRate x i)
    hT
    ((M.canonicalPathMap records).exists_bound_of_nonExplosive hne T)
    (fun x => M.instantCoordQVRate_nonneg x i)
    (M.integrableOn_canonicalInstantCoordQVRate_Icc records i T)

/-- The completed-plus-current coordinate-QV contribution is integrable. -/
theorem integrable_sum_instantCoordQVRate_mul_sojournTime_add_currentSojourn
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (hNA : M.NoAbsorbing) (i : Fin d) (T : ℝ) (hT : 0 ≤ T) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        (∑ k ∈ Finset.range ((M.canonicalPathMap records).jumpCount T),
          M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
            (M.canonicalPathMap records).sojournTime k) +
          M.instantCoordQVRate
              ((M.canonicalPathMap records).stateSeq
                ((M.canonicalPathMap records).jumpCount T)) i *
            (M.canonicalPathMap records).currentSojournElapsed T)
      (M.canonicalRecordMeasure x₀) :=
  (M.integrable_sum_instantCoordQVRate_mul_sojournTime_jumpCount x₀ hNA i T hT).add
    (M.integrable_currentSojourn_instantCoordQVRate_mul_elapsed_jumpCount
      x₀ hNA i T hT)

/-- Expectation lower bound using completed sojourns plus the current partial
sojourn contribution. -/
theorem integral_sum_instantCoordQVRate_mul_sojournTime_add_currentSojourn_le_integral_setIntegral
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (hNA : M.NoAbsorbing) (i : Fin d) (T : ℝ) (hT : 0 ≤ T) :
    ∫ records,
        ((∑ k ∈ Finset.range ((M.canonicalPathMap records).jumpCount T),
          M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
            (M.canonicalPathMap records).sojournTime k) +
          M.instantCoordQVRate
              ((M.canonicalPathMap records).stateSeq
                ((M.canonicalPathMap records).jumpCount T)) i *
            (M.canonicalPathMap records).currentSojournElapsed T)
        ∂M.canonicalRecordMeasure x₀ ≤
      ∫ records,
        (∫ s in Set.Icc (0 : ℝ) T,
          M.instantCoordQVRate ((M.canonicalPathMap records).stateAt s) i)
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let L : M.canonicalRecordΩ → ℝ := fun records =>
    (∑ k ∈ Finset.range ((M.canonicalPathMap records).jumpCount T),
      M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
        (M.canonicalPathMap records).sojournTime k) +
      M.instantCoordQVRate
          ((M.canonicalPathMap records).stateSeq
            ((M.canonicalPathMap records).jumpCount T)) i *
        (M.canonicalPathMap records).currentSojournElapsed T
  let R : M.canonicalRecordΩ → ℝ := fun records =>
    ∫ s in Set.Icc (0 : ℝ) T,
      M.instantCoordQVRate ((M.canonicalPathMap records).stateAt s) i
  have hL_int : Integrable L μ := by
    simpa [L, μ] using
      M.integrable_sum_instantCoordQVRate_mul_sojournTime_add_currentSojourn
        x₀ hNA i T hT
  have hR_int : Integrable R μ := by
    simpa [R, μ] using
      M.integrable_canonicalInstantCoordQVRate_setIntegral x₀ i T hT
  have hle : L ≤ᵐ[μ] R := by
    simpa [L, R, μ] using
      M.canonical_sum_instantCoordQVRate_mul_sojournTime_add_currentSojourn_le_setIntegral_ae
        x₀ hNA i T hT
  exact integral_mono_ae hL_int hR_int hle

/-- The sum of expected coordinate instantaneous-QV time integrals is controlled
by the expected vector instantaneous-QV time integral, with the same dimension
factor as the pointwise coordinate-to-vector QV comparison. -/
theorem canonical_sum_instantCoordQVRate_setIntegral_le_card_mul_instantQVRate
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (hT : 0 ≤ T) :
    (∑ i : Fin d,
      ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantCoordQVRate ((M.canonicalPathMap records).stateAt s) i)
        ∂M.canonicalRecordMeasure x₀) ≤
    (Fintype.card (Fin d) : ℝ) *
      ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).stateAt s))
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let Qc : Fin d → M.canonicalRecordΩ → ℝ := fun i records =>
    ∫ s in Set.Icc (0 : ℝ) T,
      M.instantCoordQVRate ((M.canonicalPathMap records).stateAt s) i
  let Q : M.canonicalRecordΩ → ℝ := fun records =>
    ∫ s in Set.Icc (0 : ℝ) T,
      M.instantQVRate ((M.canonicalPathMap records).stateAt s)
  have hQc_int : ∀ i : Fin d, Integrable (Qc i) μ := by
    intro i
    simpa [Qc, μ] using
      M.integrable_canonicalInstantCoordQVRate_setIntegral x₀ i T hT
  have hQ_int : Integrable Q μ := by
    simpa [Q, μ] using M.integrable_canonicalInstantQVRate_setIntegral x₀ T hT
  have hsumQc_int : Integrable (fun records => ∑ i : Fin d, Qc i records) μ := by
    exact integrable_finset_sum Finset.univ fun i _ => hQc_int i
  have hcardQ_int :
      Integrable (fun records : M.canonicalRecordΩ =>
        (Fintype.card (Fin d) : ℝ) * Q records) μ :=
    hQ_int.const_mul _
  have hcoord_le : ∀ records : M.canonicalRecordΩ, ∀ i : Fin d,
      Qc i records ≤ Q records := by
    intro records i
    exact setIntegral_mono_on
      (M.integrableOn_canonicalInstantCoordQVRate_Icc records i T)
      (M.integrableOn_canonicalInstantQVRate_Icc records T)
      measurableSet_Icc
      (fun s _hs =>
        M.instantCoordQVRate_le_instantQVRate
          ((M.canonicalPathMap records).stateAt s) i)
  have hsum_le :
      (fun records : M.canonicalRecordΩ => ∑ i : Fin d, Qc i records)
        ≤ᵐ[μ]
      (fun records : M.canonicalRecordΩ =>
        (Fintype.card (Fin d) : ℝ) * Q records) := by
    filter_upwards with records
    calc
      (∑ i : Fin d, Qc i records) ≤ ∑ _i : Fin d, Q records := by
          exact Finset.sum_le_sum fun i _ => hcoord_le records i
      _ = (Fintype.card (Fin d) : ℝ) * Q records := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hmono := integral_mono_ae hsumQc_int hcardQ_int hsum_le
  calc
    (∑ i : Fin d, ∫ records, Qc i records ∂μ)
        = ∫ records, ∑ i : Fin d, Qc i records ∂μ := by
            rw [integral_finset_sum Finset.univ]
            intro i _
            exact hQc_int i
    _ ≤ ∫ records, (Fintype.card (Fin d) : ℝ) * Q records ∂μ := hmono
    _ = (Fintype.card (Fin d) : ℝ) * ∫ records, Q records ∂μ := by
          rw [integral_const_mul]
    _ = (Fintype.card (Fin d) : ℝ) *
        ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
          M.instantQVRate ((M.canonicalPathMap records).stateAt s))
          ∂M.canonicalRecordMeasure x₀ := by
          simp [Q, μ]

/-- Expected canonical instantaneous-QV time integral bound.  This is the
expectation-side deterministic estimate used before the remaining stochastic
step identifying the martingale bracket and applying Doob's inequality. -/
theorem canonical_instantQVRate_setIntegral_expectation_bound
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ C > 0,
      ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).stateAt s))
        ∂M.canonicalRecordMeasure x₀ ≤ C * T / (M.N : ℝ) := by
  obtain ⟨C, hC, hbound⟩ :=
    M.exists_instantQVRate_path_setIntegral_bound M.canonicalPathMap T hT
  let G : M.canonicalRecordΩ → ℝ := fun records =>
    ∫ s in Set.Icc (0 : ℝ) T,
      M.instantQVRate ((M.canonicalPathMap records).stateAt s)
  have hG_nonneg : ∀ records, 0 ≤ G records := by
    intro records
    exact M.canonical_instantQVRate_setIntegral_nonneg T records
  have hG_int : Integrable G (M.canonicalRecordMeasure x₀) := by
    simpa [G] using M.integrable_canonicalInstantQVRate_setIntegral x₀ T hT
  refine ⟨C, hC, ?_⟩
  have hconst_int :
      Integrable (fun _records : M.canonicalRecordΩ => C * T / (M.N : ℝ))
        (M.canonicalRecordMeasure x₀) :=
    integrable_const _
  have hle_ae :
      G ≤ᶠ[ae (M.canonicalRecordMeasure x₀)]
        fun _records : M.canonicalRecordΩ => C * T / (M.N : ℝ) := by
    filter_upwards with records
    exact hbound records
  have hmono := integral_mono_ae hG_int hconst_int hle_ae
  calc
    ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).stateAt s))
        ∂M.canonicalRecordMeasure x₀ = ∫ records, G records ∂M.canonicalRecordMeasure x₀ := rfl
    _ ≤ ∫ _records : M.canonicalRecordΩ, C * T / (M.N : ℝ)
        ∂M.canonicalRecordMeasure x₀ := hmono
    _ = C * T / (M.N : ℝ) := by
      rw [integral_const]
      simp [measureReal_def]

/-- Each component of the density process is in [0, 1]. -/
theorem densityProcess_mem_Icc (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1)))
    (t : ℝ) (ω : Ω) (i : Fin d) :
    M.densityProcess pathMap t ω i ∈ Set.Icc 0 1 := by
  simp only [densityProcess, scaledState]
  constructor
  · apply div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · rw [div_le_one (Nat.cast_pos.mpr M.hN)]
    exact Nat.cast_le.mpr (Fin.is_le _)

/-- The density process is uniformly bounded by 1 in each component. -/
theorem densityProcess_nonneg (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1)))
    (t : ℝ) (ω : Ω) (i : Fin d) :
    0 ≤ M.densityProcess pathMap t ω i :=
  (M.densityProcess_mem_Icc pathMap t ω i).1

theorem densityProcess_le_one (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1)))
    (t : ℝ) (ω : Ω) (i : Fin d) :
    M.densityProcess pathMap t ω i ≤ 1 :=
  (M.densityProcess_mem_Icc pathMap t ω i).2

/-- The density process sup-norm is bounded by 1. -/
theorem densityProcess_norm_le (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1)))
    (t : ℝ) (ω : Ω) : ‖M.densityProcess pathMap t ω‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (M.densityProcess_nonneg pathMap t ω i)]
  exact M.densityProcess_le_one pathMap t ω i

/-- Along a single jump-and-hold trajectory, the density process is eventually
constant immediately to the right of any time. -/
theorem densityProcess_eventually_eq_nhdsWithin_Ici (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (ω : Ω)
    (hstrict : ∀ n, (pathMap ω).times n < (pathMap ω).times (n + 1))
    (hpos : 0 < (pathMap ω).times 0)
    (t : ℝ) :
    ∀ᶠ s in nhdsWithin t (Set.Ici t),
      M.densityProcess pathMap s ω = M.densityProcess pathMap t ω := by
  simpa [densityProcess] using
    (pathMap ω).eventually_observable_stateAt_eq_nhdsWithin_Ici
      M.scaledState hstrict hpos t

/-- Right-continuity of the density readout along a compatible
jump-and-hold trajectory. -/
theorem densityProcess_continuousWithinAt_Ici (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (ω : Ω)
    (hstrict : ∀ n, (pathMap ω).times n < (pathMap ω).times (n + 1))
    (hpos : 0 < (pathMap ω).times 0)
    (t : ℝ) :
    ContinuousWithinAt (fun s => M.densityProcess pathMap s ω) (Set.Ici t) t :=
  tendsto_nhds_of_eventually_eq
    (M.densityProcess_eventually_eq_nhdsWithin_Ici pathMap ω hstrict hpos t)

/-- The drift evaluated along the density process is also eventually constant
immediately to the right of any time. -/
theorem drift_densityProcess_eventually_eq_nhdsWithin_Ici (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (ω : Ω)
    (hstrict : ∀ n, (pathMap ω).times n < (pathMap ω).times (n + 1))
    (hpos : 0 < (pathMap ω).times 0)
    (t : ℝ) :
    ∀ᶠ s in nhdsWithin t (Set.Ici t),
      M.rateSpec.drift (M.densityProcess pathMap s ω) =
        M.rateSpec.drift (M.densityProcess pathMap t ω) := by
  exact (M.densityProcess_eventually_eq_nhdsWithin_Ici
    pathMap ω hstrict hpos t).mono fun _ hs => by rw [hs]

/-- Right-continuity of the drift readout along a compatible trajectory. -/
theorem drift_densityProcess_continuousWithinAt_Ici (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (ω : Ω)
    (hstrict : ∀ n, (pathMap ω).times n < (pathMap ω).times (n + 1))
    (hpos : 0 < (pathMap ω).times 0)
    (t : ℝ) :
    ContinuousWithinAt
      (fun s => M.rateSpec.drift (M.densityProcess pathMap s ω))
      (Set.Ici t) t :=
  tendsto_nhds_of_eventually_eq
    (M.drift_densityProcess_eventually_eq_nhdsWithin_Ici
      pathMap ω hstrict hpos t)

/-- The instantaneous QV rate readout is eventually constant immediately to
the right of any time along a compatible trajectory. -/
theorem instantQVRate_eventually_eq_nhdsWithin_Ici (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (ω : Ω)
    (hstrict : ∀ n, (pathMap ω).times n < (pathMap ω).times (n + 1))
    (hpos : 0 < (pathMap ω).times 0)
    (t : ℝ) :
    ∀ᶠ s in nhdsWithin t (Set.Ici t),
      M.instantQVRate ((pathMap ω).stateAt s) =
        M.instantQVRate ((pathMap ω).stateAt t) :=
  (pathMap ω).eventually_observable_stateAt_eq_nhdsWithin_Ici
    M.instantQVRate hstrict hpos t

/-- Right-continuity of the instantaneous QV rate readout along a compatible
trajectory. -/
theorem instantQVRate_continuousWithinAt_Ici (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (ω : Ω)
    (hstrict : ∀ n, (pathMap ω).times n < (pathMap ω).times (n + 1))
    (hpos : 0 < (pathMap ω).times 0)
    (t : ℝ) :
    ContinuousWithinAt
      (fun s => M.instantQVRate ((pathMap ω).stateAt s))
      (Set.Ici t) t :=
  tendsto_nhds_of_eventually_eq
    (M.instantQVRate_eventually_eq_nhdsWithin_Ici pathMap ω hstrict hpos t)

/-- Under `NoAbsorbing`, the canonical density process is right-continuous at
each fixed time almost surely. -/
theorem canonical_densityProcess_continuousWithinAt_Ici_ae_of_noAbsorbing
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (t : ℝ) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      ContinuousWithinAt
        (fun s => M.densityProcess M.canonicalPathMap s records)
        (Set.Ici t) t := by
  filter_upwards [M.canonicalPathMap_isCompatible_ae_of_noAbsorbing x₀ hNA]
    with records hcomp
  exact M.densityProcess_continuousWithinAt_Ici M.canonicalPathMap records
    hcomp.2.1 hcomp.1 t

/-- Under `NoAbsorbing`, the canonical drift readout is right-continuous at
each fixed time almost surely. -/
theorem canonical_drift_densityProcess_continuousWithinAt_Ici_ae_of_noAbsorbing
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (t : ℝ) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      ContinuousWithinAt
        (fun s => M.rateSpec.drift (M.densityProcess M.canonicalPathMap s records))
        (Set.Ici t) t := by
  filter_upwards [M.canonicalPathMap_isCompatible_ae_of_noAbsorbing x₀ hNA]
    with records hcomp
  exact M.drift_densityProcess_continuousWithinAt_Ici M.canonicalPathMap records
    hcomp.2.1 hcomp.1 t

/-- Under `NoAbsorbing`, the canonical instantaneous-QV-rate readout is
right-continuous at each fixed time almost surely. -/
theorem canonical_instantQVRate_continuousWithinAt_Ici_ae_of_noAbsorbing
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (t : ℝ) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      ContinuousWithinAt
        (fun s => M.instantQVRate ((M.canonicalPathMap records).stateAt s))
        (Set.Ici t) t := by
  filter_upwards [M.canonicalPathMap_isCompatible_ae_of_noAbsorbing x₀ hNA]
    with records hcomp
  exact M.instantQVRate_continuousWithinAt_Ici M.canonicalPathMap records
    hcomp.2.1 hcomp.1 t

/-- Stronger form: under `NoAbsorbing`, on one almost-sure event the canonical
density process is right-continuous at every time. -/
theorem canonical_densityProcess_forall_continuousWithinAt_Ici_ae_of_noAbsorbing
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      ∀ t : ℝ,
        ContinuousWithinAt
          (fun s => M.densityProcess M.canonicalPathMap s records)
          (Set.Ici t) t := by
  filter_upwards [M.canonicalPathMap_isCompatible_ae_of_noAbsorbing x₀ hNA]
    with records hcomp t
  exact M.densityProcess_continuousWithinAt_Ici M.canonicalPathMap records
    hcomp.2.1 hcomp.1 t

/-- Stronger form: under `NoAbsorbing`, on one almost-sure event the canonical
drift readout is right-continuous at every time. -/
theorem canonical_drift_densityProcess_forall_continuousWithinAt_Ici_ae_of_noAbsorbing
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      ∀ t : ℝ,
        ContinuousWithinAt
          (fun s => M.rateSpec.drift (M.densityProcess M.canonicalPathMap s records))
          (Set.Ici t) t := by
  filter_upwards [M.canonicalPathMap_isCompatible_ae_of_noAbsorbing x₀ hNA]
    with records hcomp t
  exact M.drift_densityProcess_continuousWithinAt_Ici M.canonicalPathMap records
    hcomp.2.1 hcomp.1 t

/-- Stronger form: under `NoAbsorbing`, on one almost-sure event the canonical
instantaneous-QV-rate readout is right-continuous at every time. -/
theorem canonical_instantQVRate_forall_continuousWithinAt_Ici_ae_of_noAbsorbing
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      ∀ t : ℝ,
        ContinuousWithinAt
          (fun s => M.instantQVRate ((M.canonicalPathMap records).stateAt s))
          (Set.Ici t) t := by
  filter_upwards [M.canonicalPathMap_isCompatible_ae_of_noAbsorbing x₀ hNA]
    with records hcomp t
  exact M.instantQVRate_continuousWithinAt_Ici M.canonicalPathMap records
    hcomp.2.1 hcomp.1 t

/-- Consolidated canonical path regularity event under `NoAbsorbing`.
This packages compatibility, non-explosion, and the right-continuity readouts
needed by the martingale supremum and QV arguments on a single a.s. event. -/
theorem canonicalPathMap_regular_ae_of_noAbsorbing
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      (M.canonicalPathMap records).IsCompatible M.toQMatrix ∧
      (M.canonicalPathMap records).NonExplosive ∧
      (∀ t : ℝ,
        ContinuousWithinAt
          (fun s => M.densityProcess M.canonicalPathMap s records)
          (Set.Ici t) t) ∧
      (∀ t : ℝ,
        ContinuousWithinAt
          (fun s => M.rateSpec.drift (M.densityProcess M.canonicalPathMap s records))
          (Set.Ici t) t) ∧
      (∀ t : ℝ,
        ContinuousWithinAt
          (fun s => M.instantQVRate ((M.canonicalPathMap records).stateAt s))
          (Set.Ici t) t) := by
  filter_upwards
    [M.canonicalPathMap_isCompatible_ae_of_noAbsorbing x₀ hNA,
     M.canonicalPathMap_nonExplosive_ae_of_noAbsorbing x₀ hNA]
    with records hcomp hne
  refine ⟨hcomp, hne, ?_, ?_, ?_⟩
  · intro t
    exact M.densityProcess_continuousWithinAt_Ici M.canonicalPathMap records
      hcomp.2.1 hcomp.1 t
  · intro t
    exact M.drift_densityProcess_continuousWithinAt_Ici M.canonicalPathMap records
      hcomp.2.1 hcomp.1 t
  · intro t
    exact M.instantQVRate_continuousWithinAt_Ici M.canonicalPathMap records
      hcomp.2.1 hcomp.1 t

/-- The drift integral along any realized density path is bounded on finite
time horizons, using the deterministic drift bound on the unit ball. -/
theorem exists_drift_setIntegral_norm_bound (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (T : ℝ) :
    ∃ C > 0, ∀ (t : ℝ) (ω : Ω), 0 ≤ t → t ≤ T →
      ‖(fun i => ∫ s in Set.Icc (0 : ℝ) t,
          (M.rateSpec.drift (M.densityProcess pathMap s ω)) i)‖ ≤ C * T := by
  obtain ⟨C, hC, hbound⟩ := M.rateSpec.exists_drift_bound_on_ball 1 zero_lt_one
  refine ⟨C, hC, ?_⟩
  intro t ω ht0 htT
  have hCT_nonneg : 0 ≤ C * T := by
    exact mul_nonneg (le_of_lt hC) (le_trans ht0 htT)
  rw [pi_norm_le_iff_of_nonneg hCT_nonneg]
  intro i
  rw [Real.norm_eq_abs]
  let f : ℝ → ℝ := fun s => (M.rateSpec.drift (M.densityProcess pathMap s ω)) i
  have hnorm_bound : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖f s‖ ≤ C := by
    intro s _hs
    exact (norm_le_pi_norm (M.rateSpec.drift (M.densityProcess pathMap s ω)) i).trans
      (hbound (M.densityProcess pathMap s ω) (M.densityProcess_norm_le pathMap s ω))
  have hnorm :
      ‖∫ s in Set.Icc (0 : ℝ) t, f s‖ ≤ C * volume.real (Set.Icc (0 : ℝ) t) :=
    norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (0 : ℝ) t)
      (f := f) measure_Icc_lt_top hnorm_bound
  calc
    |∫ s in Set.Icc (0 : ℝ) t,
        (M.rateSpec.drift (M.densityProcess pathMap s ω)) i|
        = ‖∫ s in Set.Icc (0 : ℝ) t, f s‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ C * volume.real (Set.Icc (0 : ℝ) t) := hnorm
    _ = C * t := by
      rw [Real.volume_real_Icc_of_le ht0]
      ring
    _ ≤ C * T := mul_le_mul_of_nonneg_left htT (le_of_lt hC)

/-- Initial condition X̄^N(0). -/
noncomputable def initialCondition (M : DensityDepCTMC d) :
    (Ω → CTMCPath (Fin d → Fin (M.N + 1))) →
    Ω → Fin d → ℝ :=
  fun pathMap ω => M.densityProcess pathMap 0 ω

/-- Deterministic jump-sum decomposition of the density readout.  On a
non-explosive path with strictly increasing jump times and positive first jump
time, the density at time `t` is the initial density plus the finite sum of
scaled state increments up to `jumpCount t`. -/
theorem densityProcess_eq_initialCondition_add_scaledJumpSum
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (t : ℝ) (ω : Ω)
    (hne : (pathMap ω).NonExplosive)
    (hstrict : ∀ n, (pathMap ω).times n < (pathMap ω).times (n + 1))
    (hpos : 0 < (pathMap ω).times 0) :
    M.densityProcess pathMap t ω =
      M.initialCondition pathMap ω +
        M.scaledJumpSum (pathMap ω) ((pathMap ω).jumpCount t) := by
  rw [densityProcess, initialCondition, densityProcess]
  rw [(pathMap ω).stateAt_eq_stateSeq_jumpCount_of_nonExplosive hne hstrict t]
  rw [(pathMap ω).stateAt_zero hpos]
  exact M.scaledState_stateSeq_eq_init_add_scaledJumpSum
    (pathMap ω) ((pathMap ω).jumpCount t)

/-- For the canonical record-law realization, the initial density is
measurable. -/
theorem measurable_canonicalInitialCondition (M : DensityDepCTMC d) :
    Measurable (fun records : M.canonicalRecordΩ =>
      M.initialCondition M.canonicalPathMap records) := by
  simpa [initialCondition] using M.measurable_canonicalDensityProcess 0

/-- The martingale part M^N(t), defined as the residual:
M^N(t) = X̄^N(t) - X̄^N(0) - ∫₀ᵗ F(X̄^N(s)) ds. -/
noncomputable def martingalePart (M : DensityDepCTMC d) :
    (Ω → CTMCPath (Fin d → Fin (M.N + 1))) →
    ℝ → Ω → Fin d → ℝ :=
  fun pathMap t ω => M.densityProcess pathMap t ω - M.initialCondition pathMap ω -
    (fun i => ∫ s in Set.Icc (0:ℝ) t,
      (M.rateSpec.drift (M.densityProcess pathMap s ω)) i)

/-- The same residual written with the actual finite-lattice generator drift.
This is the natural object for the pure-jump bracket calculation.  It agrees
with `martingalePart` once generator drift is aligned with `rateSpec.drift`
along the path. -/
noncomputable def generatorMartingalePart (M : DensityDepCTMC d) :
    (Ω → CTMCPath (Fin d → Fin (M.N + 1))) →
    ℝ → Ω → Fin d → ℝ :=
  fun pathMap t ω => M.densityProcess pathMap t ω - M.initialCondition pathMap ω -
    (fun i => ∫ s in Set.Icc (0:ℝ) t,
      (M.generatorDrift ((pathMap ω).stateAt s)) i)

/-- The generator-drift residual starts from zero. -/
theorem generatorMartingalePart_zero (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (ω : Ω) :
    M.generatorMartingalePart pathMap 0 ω = 0 := by
  ext i
  simp [generatorMartingalePart, initialCondition]

/-- The actual finite-lattice generator drift is uniformly bounded on the
finite density lattice. -/
theorem exists_generatorDrift_norm_bound (M : DensityDepCTMC d) :
    ∃ C > 0, ∀ x : Fin d → Fin (M.N + 1), ‖M.generatorDrift x‖ ≤ C := by
  refine ⟨(∑ x : Fin d → Fin (M.N + 1), ‖M.generatorDrift x‖) + 1,
    by positivity, ?_⟩
  intro x
  calc
    ‖M.generatorDrift x‖
        ≤ ∑ y : Fin d → Fin (M.N + 1), ‖M.generatorDrift y‖ :=
          Finset.single_le_sum (fun y _ => norm_nonneg _) (Finset.mem_univ x)
    _ ≤ (∑ y : Fin d → Fin (M.N + 1), ‖M.generatorDrift y‖) + 1 := by linarith

/-- The actual generator-drift time integral is bounded on finite horizons. -/
theorem exists_generatorDrift_setIntegral_norm_bound (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (T : ℝ) :
    ∃ C > 0, ∀ (t : ℝ) (ω : Ω), 0 ≤ t → t ≤ T →
      ‖(fun i => ∫ s in Set.Icc (0 : ℝ) t,
          (M.generatorDrift ((pathMap ω).stateAt s)) i)‖ ≤ C * T := by
  obtain ⟨C, hC, hbound⟩ := M.exists_generatorDrift_norm_bound
  refine ⟨C, hC, ?_⟩
  intro t ω ht0 htT
  have hCT_nonneg : 0 ≤ C * T := by
    exact mul_nonneg (le_of_lt hC) (le_trans ht0 htT)
  rw [pi_norm_le_iff_of_nonneg hCT_nonneg]
  intro i
  rw [Real.norm_eq_abs]
  let f : ℝ → ℝ := fun s => (M.generatorDrift ((pathMap ω).stateAt s)) i
  have hnorm_bound : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖f s‖ ≤ C := by
    intro s _hs
    exact (norm_le_pi_norm (M.generatorDrift ((pathMap ω).stateAt s)) i).trans
      (hbound ((pathMap ω).stateAt s))
  have hnorm :
      ‖∫ s in Set.Icc (0 : ℝ) t, f s‖ ≤ C * volume.real (Set.Icc (0 : ℝ) t) :=
    norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (0 : ℝ) t)
      (f := f) measure_Icc_lt_top hnorm_bound
  calc
    |∫ s in Set.Icc (0 : ℝ) t,
        (M.generatorDrift ((pathMap ω).stateAt s)) i|
        = ‖∫ s in Set.Icc (0 : ℝ) t, f s‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ C * volume.real (Set.Icc (0 : ℝ) t) := hnorm
    _ = C * t := by
      rw [Real.volume_real_Icc_of_le ht0]
      ring
    _ ≤ C * T := mul_le_mul_of_nonneg_left htT (le_of_lt hC)

/-- The generator residual is deterministically bounded on finite time
horizons. -/
theorem exists_generatorMartingalePart_norm_bound (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C > 0, ∀ (t : ℝ) (ω : Ω), 0 ≤ t → t ≤ T →
      ‖M.generatorMartingalePart pathMap t ω‖ ≤ C := by
  obtain ⟨D, hD, hD_bound⟩ := M.exists_generatorDrift_setIntegral_norm_bound pathMap T
  refine ⟨D * T + 3, by positivity, ?_⟩
  intro t ω ht0 htT
  let integralTerm : Fin d → ℝ := fun i =>
    ∫ s in Set.Icc (0 : ℝ) t,
      (M.generatorDrift ((pathMap ω).stateAt s)) i
  have hproc : ‖M.densityProcess pathMap t ω‖ ≤ 1 :=
    M.densityProcess_norm_le pathMap t ω
  have hinit : ‖M.initialCondition pathMap ω‖ ≤ 1 := by
    exact M.densityProcess_norm_le pathMap 0 ω
  have hint : ‖integralTerm‖ ≤ D * T := by
    simpa [integralTerm] using hD_bound t ω ht0 htT
  calc
    ‖M.generatorMartingalePart pathMap t ω‖
        = ‖M.densityProcess pathMap t ω - M.initialCondition pathMap ω -
            integralTerm‖ := rfl
    _ ≤ ‖M.densityProcess pathMap t ω - M.initialCondition pathMap ω‖ +
          ‖integralTerm‖ := norm_sub_le _ _
    _ ≤ (‖M.densityProcess pathMap t ω‖ + ‖M.initialCondition pathMap ω‖) +
          ‖integralTerm‖ := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ (1 + 1) + D * T := by gcongr
    _ ≤ D * T + 3 := by linarith

/-- If the actual generator drift and the abstract mean-field drift agree
along a path, then the generator-drift residual is the existing
`martingalePart`. -/
theorem generatorMartingalePart_eq_martingalePart_of_generatorDrift_eq
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (t : ℝ) (ω : Ω)
    (h : ∀ s : ℝ,
      M.generatorDrift ((pathMap ω).stateAt s) =
        M.rateSpec.drift (M.densityProcess pathMap s ω)) :
    M.generatorMartingalePart pathMap t ω =
      M.martingalePart pathMap t ω := by
  ext i
  simp [generatorMartingalePart, martingalePart, h]

/-- Pointwise coordinate-square domination for the Kurtz-facing martingale
residual.  This is the deterministic bridge from coordinatewise estimates to
the vector-valued norm square. -/
theorem martingalePart_norm_sq_le_sum_coord_sq
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (t : ℝ) (ω : Ω) :
    ‖M.martingalePart pathMap t ω‖ ^ 2 ≤
      ∑ i, (M.martingalePart pathMap t ω i) ^ 2 :=
  Ripple.Kurtz.vector_norm_sq_le_sum_sq (M.martingalePart pathMap t ω)

/-- Pointwise coordinate-square domination for the generator-drift residual.
This is the version needed for the generator-side Doob/bracket route. -/
theorem generatorMartingalePart_norm_sq_le_sum_coord_sq
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (t : ℝ) (ω : Ω) :
    ‖M.generatorMartingalePart pathMap t ω‖ ^ 2 ≤
      ∑ i, (M.generatorMartingalePart pathMap t ω i) ^ 2 :=
  Ripple.Kurtz.vector_norm_sq_le_sum_sq (M.generatorMartingalePart pathMap t ω)

/-- Finite-horizon vector supremum of the generator residual is bounded by
coordinate finite-horizon suprema, once a deterministic generator-residual norm
bound is supplied. -/
theorem generatorMartingalePart_timeSup_norm_sq_le_sum_coord_timeSup_sq_of_bound
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1)))
    (T : ℝ) (hT : 0 ≤ T) (ω : Ω)
    (hbound : ∃ C : ℝ, ∀ s : ℝ, 0 ≤ s → s ≤ T →
      ‖M.generatorMartingalePart pathMap s ω‖ ≤ C) :
    (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.generatorMartingalePart pathMap s ω‖ ^ 2) ≤
      ∑ i, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        (M.generatorMartingalePart pathMap s ω i) ^ 2 := by
  exact Ripple.Kurtz.vector_timeSup_norm_sq_le_sum_coord_timeSup_sq
    (fun s => M.generatorMartingalePart pathMap s ω) hT hbound

/-- Finite-horizon vector supremum of the generator residual is bounded by
coordinate finite-horizon suprema. -/
theorem generatorMartingalePart_timeSup_norm_sq_le_sum_coord_timeSup_sq
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1)))
    (T : ℝ) (hT : 0 ≤ T) (ω : Ω) :
    (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.generatorMartingalePart pathMap s ω‖ ^ 2) ≤
      ∑ i, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        (M.generatorMartingalePart pathMap s ω i) ^ 2 := by
  exact M.generatorMartingalePart_timeSup_norm_sq_le_sum_coord_timeSup_sq_of_bound
    pathMap T hT ω
    (by
      obtain ⟨C, _hC, hbound⟩ :=
        M.exists_generatorMartingalePart_norm_bound pathMap T hT
      exact ⟨C, fun s hs0 hsT => hbound s ω hs0 hsT⟩)

/-- Deterministic finite-jump representation of the generator-drift residual:
on a regular non-explosive path it is the finite sum of scaled jump increments
up to `jumpCount t`, minus the time integral of the actual generator drift. -/
theorem generatorMartingalePart_eq_scaledJumpSum_sub_integral
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (t : ℝ) (ω : Ω)
    (hne : (pathMap ω).NonExplosive)
    (hstrict : ∀ n, (pathMap ω).times n < (pathMap ω).times (n + 1))
    (hpos : 0 < (pathMap ω).times 0) :
    M.generatorMartingalePart pathMap t ω =
      M.scaledJumpSum (pathMap ω) ((pathMap ω).jumpCount t) -
        (fun i => ∫ s in Set.Icc (0:ℝ) t,
          (M.generatorDrift ((pathMap ω).stateAt s)) i) := by
  have hdensity :=
    M.densityProcess_eq_initialCondition_add_scaledJumpSum
      pathMap t ω hne hstrict hpos
  ext i
  simp only [generatorMartingalePart, Pi.sub_apply]
  have hdensity_i := congr_fun hdensity i
  simp only [Pi.add_apply] at hdensity_i
  rw [hdensity_i]
  ring

/-- Coordinate form of the finite-jump representation for the
generator-drift residual. -/
theorem generatorMartingalePart_apply_eq_scaledJumpSum_sub_integral
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (t : ℝ) (ω : Ω)
    (hne : (pathMap ω).NonExplosive)
    (hstrict : ∀ n, (pathMap ω).times n < (pathMap ω).times (n + 1))
    (hpos : 0 < (pathMap ω).times 0) (i : Fin d) :
    M.generatorMartingalePart pathMap t ω i =
      M.scaledJumpSum (pathMap ω) ((pathMap ω).jumpCount t) i -
        ∫ s in Set.Icc (0:ℝ) t,
          (M.generatorDrift ((pathMap ω).stateAt s)) i := by
  have hvec :=
    M.generatorMartingalePart_eq_scaledJumpSum_sub_integral
      pathMap t ω hne hstrict hpos
  simpa using congr_fun hvec i

/-- Coordinate generator residual split into the embedded jump-index martingale
sampled at `jumpCount t` plus the holding-time compensator residual.  This is
the deterministic algebraic split for the final clock-time bridge. -/
theorem generatorMartingalePart_apply_eq_scaledJumpMartingale_add_driftCompensator_sub_integral
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (t : ℝ) (ω : Ω)
    (hne : (pathMap ω).NonExplosive)
    (hstrict : ∀ n, (pathMap ω).times n < (pathMap ω).times (n + 1))
    (hpos : 0 < (pathMap ω).times 0) (i : Fin d) :
    M.generatorMartingalePart pathMap t ω i =
      M.scaledJumpMartingale (pathMap ω) i ((pathMap ω).jumpCount t) +
        (M.scaledJumpDriftCompensator (pathMap ω) i ((pathMap ω).jumpCount t) -
          ∫ s in Set.Icc (0:ℝ) t,
            (M.generatorDrift ((pathMap ω).stateAt s)) i) := by
  rw [M.generatorMartingalePart_apply_eq_scaledJumpSum_sub_integral
    pathMap t ω hne hstrict hpos i]
  simp only [scaledJumpMartingale]
  ring

/-- Canonical a.s. finite-jump representation of the generator-drift
residual, under `NoAbsorbing`. -/
theorem canonical_generatorMartingalePart_eq_scaledJumpSum_sub_integral_ae_of_noAbsorbing
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ t : ℝ,
      M.generatorMartingalePart M.canonicalPathMap t records =
        M.scaledJumpSum (M.canonicalPathMap records)
            ((M.canonicalPathMap records).jumpCount t) -
          (fun i => ∫ s in Set.Icc (0:ℝ) t,
            (M.generatorDrift ((M.canonicalPathMap records).stateAt s)) i) := by
  filter_upwards [M.canonicalPathMap_regular_ae_of_noAbsorbing x₀ hNA]
    with records hreg t
  exact M.generatorMartingalePart_eq_scaledJumpSum_sub_integral
    M.canonicalPathMap t records hreg.2.1 hreg.1.2.1 hreg.1.1

/-- Canonical a.s. coordinate form of the finite-jump representation for the
generator-drift residual. -/
theorem canonical_generatorMartingalePart_apply_eq_scaledJumpSum_sub_integral_ae_of_noAbsorbing
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ t : ℝ, ∀ i : Fin d,
      M.generatorMartingalePart M.canonicalPathMap t records i =
        M.scaledJumpSum (M.canonicalPathMap records)
            ((M.canonicalPathMap records).jumpCount t) i -
          ∫ s in Set.Icc (0:ℝ) t,
            (M.generatorDrift ((M.canonicalPathMap records).stateAt s)) i := by
  filter_upwards
    [M.canonical_generatorMartingalePart_eq_scaledJumpSum_sub_integral_ae_of_noAbsorbing
      x₀ hNA]
    with records hvec t i
  simpa using congr_fun (hvec t) i

/-- Canonical a.s. coordinate split of the generator residual into the embedded
jump martingale sampled at `jumpCount` plus the holding-time compensator
residual. -/
theorem canonical_generatorMartingalePart_apply_split_ae_of_noAbsorbing
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ t : ℝ, ∀ i : Fin d,
      M.generatorMartingalePart M.canonicalPathMap t records i =
        M.scaledJumpMartingale (M.canonicalPathMap records) i
            ((M.canonicalPathMap records).jumpCount t) +
          (M.scaledJumpDriftCompensator (M.canonicalPathMap records) i
              ((M.canonicalPathMap records).jumpCount t) -
            ∫ s in Set.Icc (0:ℝ) t,
              (M.generatorDrift ((M.canonicalPathMap records).stateAt s)) i) := by
  filter_upwards [M.canonicalPathMap_regular_ae_of_noAbsorbing x₀ hNA]
    with records hreg t i
  exact M.generatorMartingalePart_apply_eq_scaledJumpMartingale_add_driftCompensator_sub_integral
    M.canonicalPathMap t records hreg.2.1 hreg.1.2.1 hreg.1.1 i

/-- Canonical a.s. bridge from the sampled embedded drift compensator to the
completed holding-time residual plus the current partial-sojourn correction. -/
theorem canonical_driftComp_sub_integral_eq_holdingResidual_sub_current_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin d,
      M.scaledJumpDriftCompensator (M.canonicalPathMap records) i
          ((M.canonicalPathMap records).jumpCount t) -
        ∫ s in Set.Icc (0:ℝ) t,
          M.generatorDrift ((M.canonicalPathMap records).stateAt s) i =
        M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i
            ((M.canonicalPathMap records).jumpCount t) -
          M.generatorDrift
              ((M.canonicalPathMap records).stateSeq
                ((M.canonicalPathMap records).jumpCount t)) i *
            (M.canonicalPathMap records).currentSojournElapsed t := by
  filter_upwards [M.canonicalPathMap_regular_ae_of_noAbsorbing x₀ hNA]
    with records hreg t ht i
  exact M.scaledJumpDriftCompensator_sub_integral_eq_scaledHoldingTimeDriftResidual_sub_current
    (M.canonicalPathMap records) hreg.1.2.1 hreg.1.1 i ht
    ((M.canonicalPathMap records).exists_bound_of_nonExplosive hreg.2.1 t)
    (M.integrableOn_canonicalGeneratorDrift_component_Icc records i t)

/-- Canonical a.s. coordinate split of the generator residual into the embedded
jump martingale sampled at `jumpCount`, the completed holding-time residual,
and the current partial-sojourn correction. -/
theorem canonical_generatorMartingalePart_apply_split_holdingTimeResidual_ae_of_noAbsorbing
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin d,
      M.generatorMartingalePart M.canonicalPathMap t records i =
        M.scaledJumpMartingale (M.canonicalPathMap records) i
            ((M.canonicalPathMap records).jumpCount t) +
          (M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i
              ((M.canonicalPathMap records).jumpCount t) -
            M.generatorDrift
                ((M.canonicalPathMap records).stateSeq
                  ((M.canonicalPathMap records).jumpCount t)) i *
              (M.canonicalPathMap records).currentSojournElapsed t) := by
  filter_upwards
    [M.canonical_generatorMartingalePart_apply_split_ae_of_noAbsorbing x₀ hNA,
      M.canonical_driftComp_sub_integral_eq_holdingResidual_sub_current_ae
        x₀ hNA]
    with records hsplit hbridge t ht i
  rw [hsplit t i]
  rw [hbridge t ht i]

/-- Pointwise square bound from the clock-time split: the generator residual
coordinate is controlled by the embedded jump martingale square plus the
holding-time compensator residual square. -/
theorem generatorMartingalePart_apply_sq_le_two_scaledJumpMartingale_sq_add_two_driftResidual_sq
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (t : ℝ) (ω : Ω)
    (hne : (pathMap ω).NonExplosive)
    (hstrict : ∀ n, (pathMap ω).times n < (pathMap ω).times (n + 1))
    (hpos : 0 < (pathMap ω).times 0) (i : Fin d) :
    (M.generatorMartingalePart pathMap t ω i) ^ 2 ≤
      2 * (M.scaledJumpMartingale (pathMap ω) i ((pathMap ω).jumpCount t)) ^ 2 +
        2 *
          (M.scaledJumpDriftCompensator (pathMap ω) i ((pathMap ω).jumpCount t) -
            ∫ s in Set.Icc (0:ℝ) t,
              (M.generatorDrift ((pathMap ω).stateAt s)) i) ^ 2 := by
  rw [M.generatorMartingalePart_apply_eq_scaledJumpMartingale_add_driftCompensator_sub_integral
    pathMap t ω hne hstrict hpos i]
  let a := M.scaledJumpMartingale (pathMap ω) i ((pathMap ω).jumpCount t)
  let b :=
    M.scaledJumpDriftCompensator (pathMap ω) i ((pathMap ω).jumpCount t) -
      ∫ s in Set.Icc (0:ℝ) t, (M.generatorDrift ((pathMap ω).stateAt s)) i
  change (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2
  nlinarith [sq_nonneg (a - b)]

/-- Canonical a.s. pointwise square bound from the split into embedded jump
martingale and holding-time compensator residual. -/
theorem canonical_generatorMartingalePart_apply_sq_split_bound_ae_of_noAbsorbing
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ t : ℝ, ∀ i : Fin d,
      (M.generatorMartingalePart M.canonicalPathMap t records i) ^ 2 ≤
        2 *
          (M.scaledJumpMartingale (M.canonicalPathMap records) i
            ((M.canonicalPathMap records).jumpCount t)) ^ 2 +
          2 *
            (M.scaledJumpDriftCompensator (M.canonicalPathMap records) i
                ((M.canonicalPathMap records).jumpCount t) -
              ∫ s in Set.Icc (0:ℝ) t,
                (M.generatorDrift ((M.canonicalPathMap records).stateAt s)) i) ^ 2 := by
  filter_upwards [M.canonicalPathMap_regular_ae_of_noAbsorbing x₀ hNA]
    with records hreg t i
  exact M.generatorMartingalePart_apply_sq_le_two_scaledJumpMartingale_sq_add_two_driftResidual_sq
    M.canonicalPathMap t records hreg.2.1 hreg.1.2.1 hreg.1.1 i

/-- Supremum lift for a scalar two-term square bound on a finite horizon. -/
theorem scalar_timeSup_sq_le_two_timeSup_sq_add_two_timeSup_sq
    (f g h : ℝ → ℝ) {T : ℝ}
    (hg_bound : ∃ C ≥ 0, ∀ t : ℝ, 0 ≤ t → t ≤ T → |g t| ≤ C)
    (hh_bound : ∃ C ≥ 0, ∀ t : ℝ, 0 ≤ t → t ≤ T → |h t| ≤ C)
    (hpoint : ∀ t : ℝ, 0 ≤ t → t ≤ T →
      f t ^ 2 ≤ 2 * g t ^ 2 + 2 * h t ^ 2) :
    (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), f t ^ 2) ≤
      2 * (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), g t ^ 2) +
        2 * (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), h t ^ 2) := by
  obtain ⟨Cg, hCg_nonneg, hg⟩ := hg_bound
  obtain ⟨Ch, hCh_nonneg, hh⟩ := hh_bound
  have hg_inner_bdd (t : ℝ) :
      BddAbove (Set.range fun _ : 0 ≤ t ∧ t ≤ T => g t ^ 2) := by
    refine ⟨Cg ^ 2, ?_⟩
    rintro y ⟨ht, rfl⟩
    rw [← sq_abs]
    exact sq_le_sq.mpr (by
      simpa [abs_of_nonneg hCg_nonneg] using hg t ht.1 ht.2)
  have hg_outer_bdd :
      BddAbove (Set.range fun t : ℝ =>
        ⨆ (_ : 0 ≤ t ∧ t ≤ T), g t ^ 2) := by
    refine ⟨Cg ^ 2, ?_⟩
    rintro y ⟨t, rfl⟩
    exact Real.iSup_le (fun ht => by
      rw [← sq_abs]
      exact sq_le_sq.mpr (by
        simpa [abs_of_nonneg hCg_nonneg] using hg t ht.1 ht.2))
      (sq_nonneg Cg)
  have hh_inner_bdd (t : ℝ) :
      BddAbove (Set.range fun _ : 0 ≤ t ∧ t ≤ T => h t ^ 2) := by
    refine ⟨Ch ^ 2, ?_⟩
    rintro y ⟨ht, rfl⟩
    rw [← sq_abs]
    exact sq_le_sq.mpr (by
      simpa [abs_of_nonneg hCh_nonneg] using hh t ht.1 ht.2)
  have hh_outer_bdd :
      BddAbove (Set.range fun t : ℝ =>
        ⨆ (_ : 0 ≤ t ∧ t ≤ T), h t ^ 2) := by
    refine ⟨Ch ^ 2, ?_⟩
    rintro y ⟨t, rfl⟩
    exact Real.iSup_le (fun ht => by
      rw [← sq_abs]
      exact sq_le_sq.mpr (by
        simpa [abs_of_nonneg hCh_nonneg] using hh t ht.1 ht.2))
      (sq_nonneg Ch)
  have hg_le (t : ℝ) (ht : 0 ≤ t ∧ t ≤ T) :
      g t ^ 2 ≤ ⨆ (u : ℝ) (_ : 0 ≤ u ∧ u ≤ T), g u ^ 2 := by
    exact le_trans (le_ciSup (hg_inner_bdd t) ht)
      (le_ciSup hg_outer_bdd t)
  have hh_le (t : ℝ) (ht : 0 ≤ t ∧ t ≤ T) :
      h t ^ 2 ≤ ⨆ (u : ℝ) (_ : 0 ≤ u ∧ u ≤ T), h u ^ 2 := by
    exact le_trans (le_ciSup (hh_inner_bdd t) ht)
      (le_ciSup hh_outer_bdd t)
  refine Real.iSup_le ?_ (by
    exact add_nonneg
      (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ))
        (Real.iSup_nonneg fun t => Real.iSup_nonneg fun _ => sq_nonneg (g t)))
      (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ))
        (Real.iSup_nonneg fun t => Real.iSup_nonneg fun _ => sq_nonneg (h t))))
  intro t
  refine Real.iSup_le ?_ (by
    exact add_nonneg
      (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ))
        (Real.iSup_nonneg fun u => Real.iSup_nonneg fun _ => sq_nonneg (g u)))
      (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ))
        (Real.iSup_nonneg fun u => Real.iSup_nonneg fun _ => sq_nonneg (h u))))
  intro ht
  calc
    f t ^ 2 ≤ 2 * g t ^ 2 + 2 * h t ^ 2 := hpoint t ht.1 ht.2
    _ ≤ 2 * (⨆ (u : ℝ) (_ : 0 ≤ u ∧ u ≤ T), g u ^ 2) +
        2 * (⨆ (u : ℝ) (_ : 0 ≤ u ∧ u ≤ T), h u ^ 2) := by
          gcongr
          · exact hg_le t ht
          · exact hh_le t ht

/-- Clock-time supremum version of the coordinate split bound, with boundedness
of the embedded and holding-time residual components supplied explicitly. -/
theorem generatorMartingalePart_coord_timeSup_sq_le_split_timeSup_sq_of_bounds
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1)))
    (T : ℝ) (ω : Ω)
    (hne : (pathMap ω).NonExplosive)
    (hstrict : ∀ n, (pathMap ω).times n < (pathMap ω).times (n + 1))
    (hpos : 0 < (pathMap ω).times 0) (i : Fin d)
    (hJ_bound : ∃ C ≥ 0, ∀ t : ℝ, 0 ≤ t → t ≤ T →
      |M.scaledJumpMartingale (pathMap ω) i ((pathMap ω).jumpCount t)| ≤ C)
    (hR_bound : ∃ C ≥ 0, ∀ t : ℝ, 0 ≤ t → t ≤ T →
      |M.scaledJumpDriftCompensator (pathMap ω) i ((pathMap ω).jumpCount t) -
        ∫ s in Set.Icc (0:ℝ) t,
          (M.generatorDrift ((pathMap ω).stateAt s)) i| ≤ C) :
    (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        (M.generatorMartingalePart pathMap t ω i) ^ 2) ≤
      2 * (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        (M.scaledJumpMartingale (pathMap ω) i ((pathMap ω).jumpCount t)) ^ 2) +
      2 * (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        (M.scaledJumpDriftCompensator (pathMap ω) i ((pathMap ω).jumpCount t) -
          ∫ s in Set.Icc (0:ℝ) t,
            (M.generatorDrift ((pathMap ω).stateAt s)) i) ^ 2) := by
  exact scalar_timeSup_sq_le_two_timeSup_sq_add_two_timeSup_sq
    (fun t => M.generatorMartingalePart pathMap t ω i)
    (fun t => M.scaledJumpMartingale (pathMap ω) i ((pathMap ω).jumpCount t))
    (fun t =>
      M.scaledJumpDriftCompensator (pathMap ω) i ((pathMap ω).jumpCount t) -
        ∫ s in Set.Icc (0:ℝ) t,
          (M.generatorDrift ((pathMap ω).stateAt s)) i)
    hJ_bound hR_bound
    (fun t ht0 htT =>
      M.generatorMartingalePart_apply_sq_le_two_scaledJumpMartingale_sq_add_two_driftResidual_sq
        pathMap t ω hne hstrict hpos i)

/-- Sampling an embedded jump-index martingale at `jumpCount t` and taking a
clock-time supremum up to `T` is bounded by the finite jump-index supremum up to
`jumpCount T`. -/
theorem scaledJumpMartingale_jumpCount_timeSup_sq_le_finSup_of_nonExplosive
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d)
    (hne : path.NonExplosive)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (T : ℝ) :
    (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        (M.scaledJumpMartingale path i (path.jumpCount t)) ^ 2) ≤
      ((Finset.range (path.jumpCount T + 1)).sup' Finset.nonempty_range_add_one
        (fun k => ‖M.scaledJumpMartingale path i k‖)) ^ 2 := by
  let S : ℝ :=
    (Finset.range (path.jumpCount T + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ‖M.scaledJumpMartingale path i k‖)
  have hS_nonneg : 0 ≤ S := by
    have hmem0 : 0 ∈ Finset.range (path.jumpCount T + 1) :=
      Finset.mem_range.mpr (Nat.succ_pos _)
    exact (norm_nonneg (M.scaledJumpMartingale path i 0)).trans
      (Finset.le_sup'
        (s := Finset.range (path.jumpCount T + 1))
        (f := fun k => ‖M.scaledJumpMartingale path i k‖) hmem0)
  refine Real.iSup_le ?_ (sq_nonneg S)
  intro t
  refine Real.iSup_le ?_ (sq_nonneg S)
  intro ht
  have ht_future : ∃ n, t < path.times n := path.exists_bound_of_nonExplosive hne t
  have hT_future : ∃ n, T < path.times n := path.exists_bound_of_nonExplosive hne T
  have hjump_le : path.jumpCount t ≤ path.jumpCount T :=
    path.jumpCount_mono hstrict ht.2 ht_future hT_future
  have hmem : path.jumpCount t ∈ Finset.range (path.jumpCount T + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hjump_le)
  have hnorm_le :
      ‖M.scaledJumpMartingale path i (path.jumpCount t)‖ ≤ S :=
    Finset.le_sup'
      (s := Finset.range (path.jumpCount T + 1))
      (f := fun k => ‖M.scaledJumpMartingale path i k‖) hmem
  rw [← sq_abs]
  exact sq_le_sq' (by
      nlinarith [hS_nonneg,
        abs_nonneg (M.scaledJumpMartingale path i (path.jumpCount t))])
    hnorm_le

/-- Sampling the completed holding-time residual at `jumpCount t` and taking a
clock-time supremum up to `T` is bounded by the finite jump-index supremum up
to `jumpCount T`. -/
theorem scaledHoldingTimeResidual_jumpCount_timeSup_sq_le_finSup_of_nonExplosive
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d)
    (hne : path.NonExplosive)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (T : ℝ) :
    (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        (M.scaledHoldingTimeDriftResidual path i (path.jumpCount t)) ^ 2) ≤
      ((Finset.range (path.jumpCount T + 1)).sup' Finset.nonempty_range_add_one
        (fun k => ‖M.scaledHoldingTimeDriftResidual path i k‖)) ^ 2 := by
  let S : ℝ :=
    (Finset.range (path.jumpCount T + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ‖M.scaledHoldingTimeDriftResidual path i k‖)
  have hS_nonneg : 0 ≤ S := by
    have hmem0 : 0 ∈ Finset.range (path.jumpCount T + 1) :=
      Finset.mem_range.mpr (Nat.succ_pos _)
    exact (norm_nonneg (M.scaledHoldingTimeDriftResidual path i 0)).trans
      (Finset.le_sup'
        (s := Finset.range (path.jumpCount T + 1))
        (f := fun k => ‖M.scaledHoldingTimeDriftResidual path i k‖) hmem0)
  refine Real.iSup_le ?_ (sq_nonneg S)
  intro t
  refine Real.iSup_le ?_ (sq_nonneg S)
  intro ht
  have ht_future : ∃ n, t < path.times n := path.exists_bound_of_nonExplosive hne t
  have hT_future : ∃ n, T < path.times n := path.exists_bound_of_nonExplosive hne T
  have hjump_le : path.jumpCount t ≤ path.jumpCount T :=
    path.jumpCount_mono hstrict ht.2 ht_future hT_future
  have hmem : path.jumpCount t ∈ Finset.range (path.jumpCount T + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hjump_le)
  have hnorm_le :
      ‖M.scaledHoldingTimeDriftResidual path i (path.jumpCount t)‖ ≤ S :=
    Finset.le_sup'
      (s := Finset.range (path.jumpCount T + 1))
      (f := fun k => ‖M.scaledHoldingTimeDriftResidual path i k‖) hmem
  rw [← sq_abs]
  exact sq_le_sq' (by
      nlinarith [hS_nonneg,
        abs_nonneg (M.scaledHoldingTimeDriftResidual path i (path.jumpCount t))])
    hnorm_le

/-- The clock-time supremum of the compensator-minus-integral residual is
bounded by the completed holding-time residual finite supremum plus the
current partial-sojourn correction. -/
theorem driftCompensatorResidual_timeSup_sq_le_holdingResidual_finSup_add_currentSup
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d)
    (hne : path.NonExplosive)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) (T : ℝ) (hT : 0 ≤ T)
    (hf_int : ∀ t : ℝ, 0 ≤ t → t ≤ T →
      IntegrableOn (fun s => M.generatorDrift (path.stateAt s) i)
        (Set.Icc (0 : ℝ) t) volume) :
    (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        (M.scaledJumpDriftCompensator path i (path.jumpCount t) -
          ∫ s in Set.Icc (0:ℝ) t, M.generatorDrift (path.stateAt s) i) ^ 2) ≤
      2 * ((Finset.range (path.jumpCount T + 1)).sup' Finset.nonempty_range_add_one
        (fun k => ‖M.scaledHoldingTimeDriftResidual path i k‖)) ^ 2 +
      2 * (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        (M.generatorDrift (path.stateSeq (path.jumpCount t)) i *
          path.currentSojournElapsed t) ^ 2) := by
  let R : ℝ → ℝ := fun t =>
    M.scaledJumpDriftCompensator path i (path.jumpCount t) -
      ∫ s in Set.Icc (0:ℝ) t, M.generatorDrift (path.stateAt s) i
  let H : ℝ → ℝ := fun t =>
    M.scaledHoldingTimeDriftResidual path i (path.jumpCount t)
  let E : ℝ → ℝ := fun t =>
    M.generatorDrift (path.stateSeq (path.jumpCount t)) i *
      path.currentSojournElapsed t
  let S : ℝ :=
    (Finset.range (path.jumpCount T + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ‖M.scaledHoldingTimeDriftResidual path i k‖)
  have hS_nonneg : 0 ≤ S := by
    have hmem0 : 0 ∈ Finset.range (path.jumpCount T + 1) :=
      Finset.mem_range.mpr (Nat.succ_pos _)
    exact (norm_nonneg (M.scaledHoldingTimeDriftResidual path i 0)).trans
      (Finset.le_sup'
        (s := Finset.range (path.jumpCount T + 1))
        (f := fun k => ‖M.scaledHoldingTimeDriftResidual path i k‖) hmem0)
  have hH_bound : ∃ C₀ ≥ 0, ∀ t : ℝ, 0 ≤ t → t ≤ T → |H t| ≤ C₀ := by
    refine ⟨S, hS_nonneg, ?_⟩
    intro t _ht0 htT
    have ht_future : ∃ n, t < path.times n := path.exists_bound_of_nonExplosive hne t
    have hT_future : ∃ n, T < path.times n := path.exists_bound_of_nonExplosive hne T
    have hjump_le : path.jumpCount t ≤ path.jumpCount T :=
      path.jumpCount_mono hstrict htT ht_future hT_future
    have hmem : path.jumpCount t ∈ Finset.range (path.jumpCount T + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hjump_le)
    have hnorm_le : ‖M.scaledHoldingTimeDriftResidual path i (path.jumpCount t)‖ ≤ S :=
      Finset.le_sup'
        (s := Finset.range (path.jumpCount T + 1))
        (f := fun k => ‖M.scaledHoldingTimeDriftResidual path i k‖) hmem
    simpa [H, Real.norm_eq_abs] using hnorm_le
  have hC_bound : ∃ C₀ ≥ 0, ∀ t : ℝ, 0 ≤ t → t ≤ T → |E t| ≤ C₀ := by
    obtain ⟨D, hD_nonneg, hD⟩ := M.exists_generatorDrift_abs_bound i
    refine ⟨D * T, mul_nonneg hD_nonneg hT, ?_⟩
    intro t ht0 htT
    have ht_future : ∃ n, t < path.times n := path.exists_bound_of_nonExplosive hne t
    have hel_nonneg : 0 ≤ path.currentSojournElapsed t :=
      path.currentSojournElapsed_nonneg ht0 ht_future
    have hel_le_T : path.currentSojournElapsed t ≤ T :=
      le_trans (path.currentSojournElapsed_le hstrict hpos) htT
    calc
      |E t| =
          |M.generatorDrift (path.stateSeq (path.jumpCount t)) i *
            path.currentSojournElapsed t| := by
              rfl
      _ = |M.generatorDrift (path.stateSeq (path.jumpCount t)) i| *
            path.currentSojournElapsed t := by
          rw [abs_mul, abs_of_nonneg hel_nonneg]
      _ ≤ D * T := by
          exact mul_le_mul
            (by simpa [Real.norm_eq_abs] using
              hD (path.stateSeq (path.jumpCount t)))
            hel_le_T hel_nonneg hD_nonneg
  have hsplit :
      (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), R t ^ 2) ≤
        2 * (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), H t ^ 2) +
        2 * (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), E t ^ 2) := by
    exact scalar_timeSup_sq_le_two_timeSup_sq_add_two_timeSup_sq R H E
      hH_bound hC_bound
      (fun t ht0 htT => by
        have hfuture : ∃ n, t < path.times n := path.exists_bound_of_nonExplosive hne t
        have hbridge :=
          M.scaledJumpDriftCompensator_sub_integral_eq_scaledHoldingTimeDriftResidual_sub_current
            path hstrict hpos i ht0 hfuture (hf_int t ht0 htT)
        have hR_eq : R t = H t - E t := by
          simpa [R, H, E] using hbridge
        rw [hR_eq]
        nlinarith [sq_nonneg (H t + E t)])
  have hH_sup :=
    M.scaledHoldingTimeResidual_jumpCount_timeSup_sq_le_finSup_of_nonExplosive
      path i hne hstrict T
  calc
    (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        (M.scaledJumpDriftCompensator path i (path.jumpCount t) -
          ∫ s in Set.Icc (0:ℝ) t, M.generatorDrift (path.stateAt s) i) ^ 2)
        = (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), R t ^ 2) := by
            simp [R]
    _ ≤ 2 * (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), H t ^ 2) +
        2 * (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), E t ^ 2) := hsplit
    _ ≤ 2 * S ^ 2 +
        2 * (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), E t ^ 2) := by
          gcongr
    _ = 2 * ((Finset.range (path.jumpCount T + 1)).sup'
          Finset.nonempty_range_add_one
          (fun k => ‖M.scaledHoldingTimeDriftResidual path i k‖)) ^ 2 +
        2 * (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
          (M.generatorDrift (path.stateSeq (path.jumpCount t)) i *
            path.currentSojournElapsed t) ^ 2) := by
          simp [S, E]

/-- Canonical a.s. pointwise combined bound: at each time `t ≤ T` the
coordinate generator-martingale square is bounded by twice the finite
jump-index norm supremum squared (up to `jumpCount T`) plus twice the
holding-time compensator residual squared.  This merges the pointwise split
(update 62) with the random-index bridge (update 64). -/
theorem canonical_generatorMartingalePart_sq_le_finSup_sq_add_residual_sq_ae_of_noAbsorbing
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ (t T : ℝ) (i : Fin d),
      0 ≤ t → t ≤ T →
        (M.generatorMartingalePart M.canonicalPathMap t records i) ^ 2 ≤
          2 * ((Finset.range ((M.canonicalPathMap records).jumpCount T + 1)).sup'
                Finset.nonempty_range_add_one
                (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2 +
          2 * (M.scaledJumpDriftCompensator (M.canonicalPathMap records) i
                  ((M.canonicalPathMap records).jumpCount t) -
                ∫ s in Set.Icc (0:ℝ) t,
                  (M.generatorDrift ((M.canonicalPathMap records).stateAt s)) i) ^ 2 := by
  filter_upwards [M.canonicalPathMap_regular_ae_of_noAbsorbing x₀ hNA]
    with records hreg t T i _ht0 htT
  let path := M.canonicalPathMap records
  have hne := hreg.2.1
  have hstrict := hreg.1.2.1
  have hsplit :=
    M.generatorMartingalePart_apply_sq_le_two_scaledJumpMartingale_sq_add_two_driftResidual_sq
      M.canonicalPathMap t records hne hstrict hreg.1.1 i
  have hfuture_t : ∃ n, t < path.times n :=
    path.exists_bound_of_nonExplosive hne t
  have hfuture_T : ∃ n, T < path.times n :=
    path.exists_bound_of_nonExplosive hne T
  have hjc_le : path.jumpCount t ≤ path.jumpCount T :=
    path.jumpCount_mono hstrict htT hfuture_t hfuture_T
  have hjc_mem : path.jumpCount t ∈ Finset.range (path.jumpCount T + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hjc_le)
  have hnorm_le : ‖M.scaledJumpMartingale path i (path.jumpCount t)‖ ≤
      (Finset.range (path.jumpCount T + 1)).sup' Finset.nonempty_range_add_one
        (fun k => ‖M.scaledJumpMartingale path i k‖) :=
    Finset.le_sup'
      (s := Finset.range (path.jumpCount T + 1))
      (f := fun k => ‖M.scaledJumpMartingale path i k‖) hjc_mem
  have hS_nonneg : 0 ≤
      (Finset.range (path.jumpCount T + 1)).sup' Finset.nonempty_range_add_one
        (fun k => ‖M.scaledJumpMartingale path i k‖) :=
    (norm_nonneg _).trans
      (Finset.le_sup'
        (s := Finset.range (path.jumpCount T + 1))
        (f := fun k => ‖M.scaledJumpMartingale path i k‖)
        (Finset.mem_range.mpr (Nat.succ_pos _)))
  have habs_le : |M.scaledJumpMartingale path i (path.jumpCount t)| ≤
      (Finset.range (path.jumpCount T + 1)).sup' Finset.nonempty_range_add_one
        (fun k => ‖M.scaledJumpMartingale path i k‖) := by
    rwa [← Real.norm_eq_abs]
  have hbounds := abs_le.mp habs_le
  have hsq_le :
      (M.scaledJumpMartingale path i (path.jumpCount t)) ^ 2 ≤
        ((Finset.range (path.jumpCount T + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.scaledJumpMartingale path i k‖)) ^ 2 :=
    sq_le_sq' hbounds.1 hbounds.2
  calc
    (M.generatorMartingalePart M.canonicalPathMap t records i) ^ 2
        ≤ 2 * (M.scaledJumpMartingale path i (path.jumpCount t)) ^ 2 +
          2 * (M.scaledJumpDriftCompensator path i (path.jumpCount t) -
            ∫ s in Set.Icc (0:ℝ) t,
              (M.generatorDrift (path.stateAt s)) i) ^ 2 := hsplit
    _ ≤ 2 * ((Finset.range (path.jumpCount T + 1)).sup' Finset.nonempty_range_add_one
              (fun k => ‖M.scaledJumpMartingale path i k‖)) ^ 2 +
          2 * (M.scaledJumpDriftCompensator path i (path.jumpCount t) -
            ∫ s in Set.Icc (0:ℝ) t,
              (M.generatorDrift (path.stateAt s)) i) ^ 2 := by
      gcongr

/-- Canonical a.s. clock-time supremum version of the combined coordinate
bound.  The embedded jump-martingale contribution is reduced to the finite
jump-index supremum up to `jumpCount T`; the remaining term is the clock-time
supremum of the holding-time compensator residual. -/
theorem canonical_generatorMartingalePart_coord_timeSup_sq_le_finSup_add_residualSup_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ (T : ℝ) (i : Fin d),
      (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
          (M.generatorMartingalePart M.canonicalPathMap t records i) ^ 2) ≤
        2 * ((Finset.range ((M.canonicalPathMap records).jumpCount T + 1)).sup'
              Finset.nonempty_range_add_one
              (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2 +
        2 * (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
          (M.scaledJumpDriftCompensator (M.canonicalPathMap records) i
              ((M.canonicalPathMap records).jumpCount t) -
            ∫ s in Set.Icc (0:ℝ) t,
              (M.generatorDrift ((M.canonicalPathMap records).stateAt s)) i) ^ 2) := by
  filter_upwards [M.canonicalPathMap_regular_ae_of_noAbsorbing x₀ hNA]
    with records hreg T i
  let path := M.canonicalPathMap records
  let S : ℝ :=
    (Finset.range (path.jumpCount T + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ‖M.scaledJumpMartingale path i k‖)
  let R : ℝ → ℝ := fun t =>
    M.scaledJumpDriftCompensator path i (path.jumpCount t) -
      ∫ s in Set.Icc (0:ℝ) t, (M.generatorDrift (path.stateAt s)) i
  have hS_nonneg : 0 ≤ S := by
    have hmem0 : 0 ∈ Finset.range (path.jumpCount T + 1) :=
      Finset.mem_range.mpr (Nat.succ_pos _)
    exact (norm_nonneg (M.scaledJumpMartingale path i 0)).trans
      (Finset.le_sup'
        (s := Finset.range (path.jumpCount T + 1))
        (f := fun k => ‖M.scaledJumpMartingale path i k‖) hmem0)
  have hJ_abs_bound : ∀ t : ℝ, 0 ≤ t → t ≤ T →
      |M.scaledJumpMartingale path i (path.jumpCount t)| ≤ S := by
    intro t _ht0 htT
    have ht_future : ∃ n, t < path.times n :=
      path.exists_bound_of_nonExplosive hreg.2.1 t
    have hT_future : ∃ n, T < path.times n :=
      path.exists_bound_of_nonExplosive hreg.2.1 T
    have hjump_le : path.jumpCount t ≤ path.jumpCount T :=
      path.jumpCount_mono hreg.1.2.1 htT ht_future hT_future
    have hmem : path.jumpCount t ∈ Finset.range (path.jumpCount T + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hjump_le)
    have hnorm_le : ‖M.scaledJumpMartingale path i (path.jumpCount t)‖ ≤ S :=
      Finset.le_sup'
        (s := Finset.range (path.jumpCount T + 1))
        (f := fun k => ‖M.scaledJumpMartingale path i k‖) hmem
    rwa [← Real.norm_eq_abs]
  have hJ_bound : ∃ C ≥ 0, ∀ t : ℝ, 0 ≤ t → t ≤ T →
      |M.scaledJumpMartingale path i (path.jumpCount t)| ≤ C :=
    ⟨S, hS_nonneg, hJ_abs_bound⟩
  have hR_bound : ∃ C ≥ 0, ∀ t : ℝ, 0 ≤ t → t ≤ T → |R t| ≤ C := by
    by_cases hT : 0 ≤ T
    · obtain ⟨C, hCpos, hC_bound⟩ :=
        M.exists_generatorMartingalePart_norm_bound M.canonicalPathMap T hT
      refine ⟨C + S, add_nonneg (le_of_lt hCpos) hS_nonneg, ?_⟩
      intro t ht0 htT
      have hsplit :=
        M.generatorMartingalePart_apply_eq_scaledJumpMartingale_add_driftCompensator_sub_integral
          M.canonicalPathMap t records hreg.2.1 hreg.1.2.1 hreg.1.1 i
      have hR_eq :
          R t =
            M.generatorMartingalePart M.canonicalPathMap t records i -
              M.scaledJumpMartingale path i (path.jumpCount t) := by
        dsimp [R, path]
        linarith
      have hgen_abs :
          |M.generatorMartingalePart M.canonicalPathMap t records i| ≤ C := by
        calc
          |M.generatorMartingalePart M.canonicalPathMap t records i|
              = ‖M.generatorMartingalePart M.canonicalPathMap t records i‖ := by
                  rw [Real.norm_eq_abs]
          _ ≤ ‖M.generatorMartingalePart M.canonicalPathMap t records‖ :=
              norm_le_pi_norm _ i
          _ ≤ C := hC_bound t records ht0 htT
      have hjump_abs :
          |M.scaledJumpMartingale path i (path.jumpCount t)| ≤ S :=
        hJ_abs_bound t ht0 htT
      rw [hR_eq]
      calc
        |M.generatorMartingalePart M.canonicalPathMap t records i -
            M.scaledJumpMartingale path i (path.jumpCount t)|
            ≤ |M.generatorMartingalePart M.canonicalPathMap t records i| +
              |M.scaledJumpMartingale path i (path.jumpCount t)| := abs_sub _ _
        _ ≤ C + S := add_le_add hgen_abs hjump_abs
    · refine ⟨0, le_rfl, ?_⟩
      intro t ht0 htT
      exact False.elim (hT (le_trans ht0 htT))
  have hsplit_sup :=
    M.generatorMartingalePart_coord_timeSup_sq_le_split_timeSup_sq_of_bounds
      M.canonicalPathMap T records hreg.2.1 hreg.1.2.1 hreg.1.1 i
      hJ_bound hR_bound
  have hJ_sup :=
    M.scaledJumpMartingale_jumpCount_timeSup_sq_le_finSup_of_nonExplosive
      path i hreg.2.1 hreg.1.2.1 T
  calc
    (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
        (M.generatorMartingalePart M.canonicalPathMap t records i) ^ 2)
        ≤ 2 * (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
          (M.scaledJumpMartingale path i (path.jumpCount t)) ^ 2) +
          2 * (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), R t ^ 2) := by
          simpa [path, R] using hsplit_sup
    _ ≤ 2 * S ^ 2 + 2 * (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), R t ^ 2) := by
          gcongr
    _ = 2 * ((Finset.range ((M.canonicalPathMap records).jumpCount T + 1)).sup'
              Finset.nonempty_range_add_one
              (fun k => ‖M.scaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2 +
        2 * (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
          (M.scaledJumpDriftCompensator (M.canonicalPathMap records) i
              ((M.canonicalPathMap records).jumpCount t) -
            ∫ s in Set.Icc (0:ℝ) t,
              (M.generatorDrift ((M.canonicalPathMap records).stateAt s)) i) ^ 2) := by
          simp [S, R, path]

/-- Canonical a.s. bracket skeleton for the generator-drift residual: on one
full-measure event, the residual has the finite-jump decomposition, the
cumulative squared scaled-jump sum through `jumpCount` has the deterministic
`jumpCount * (jumpNormBound/N)^2` bound, and that cumulative squared-jump
process is monotone in clock time. -/
theorem canonical_generatorBracketSkeleton_ae_of_noAbsorbing
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      (∀ t : ℝ,
        M.generatorMartingalePart M.canonicalPathMap t records =
          M.scaledJumpSum (M.canonicalPathMap records)
              ((M.canonicalPathMap records).jumpCount t) -
            (fun i => ∫ s in Set.Icc (0:ℝ) t,
              (M.generatorDrift ((M.canonicalPathMap records).stateAt s)) i)) ∧
      (∀ T : ℝ,
        M.scaledJumpSqSum (M.canonicalPathMap records)
            ((M.canonicalPathMap records).jumpCount T) ≤
          ((M.canonicalPathMap records).jumpCount T : ℝ) *
            (M.rateSpec.jumpNormBound / (M.N : ℝ)) ^ 2) ∧
      (∀ s t : ℝ, s ≤ t →
        M.scaledJumpSqSum (M.canonicalPathMap records)
            ((M.canonicalPathMap records).jumpCount s) ≤
          M.scaledJumpSqSum (M.canonicalPathMap records)
            ((M.canonicalPathMap records).jumpCount t)) := by
  filter_upwards
    [M.canonical_generatorMartingalePart_eq_scaledJumpSum_sub_integral_ae_of_noAbsorbing
      x₀ hNA,
      M.canonicalPathMap_scaledJumpSqSum_jumpCount_le_ae_of_noAbsorbing x₀ hNA,
      M.canonicalPathMap_scaledJumpSqSum_jumpCount_mono_ae_of_noAbsorbing x₀ hNA]
    with records hrepr hbound hmono
  exact ⟨hrepr, hbound, hmono⟩

/-- Canonical a.s. equality between the generator-drift residual and the
existing `martingalePart`, under simplex-local drift alignment hypotheses. -/
theorem canonical_generatorMartingalePart_eq_martingalePart_ae_of_boundaryCompatibleOnSimplex
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (hNA : M.NoAbsorbing) (hcons : M.ConservativeJumps)
    (hinit : M.InSimplex x₀) (hBC : M.BoundaryCompatibleOnSimplex) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ t : ℝ,
      M.generatorMartingalePart M.canonicalPathMap t records =
        M.martingalePart M.canonicalPathMap t records := by
  filter_upwards
    [M.canonical_generatorDrift_eq_rateSpec_drift_ae_of_boundaryCompatibleOnSimplex
      x₀ hNA hcons hinit hBC]
    with records halign t
  exact M.generatorMartingalePart_eq_martingalePart_of_generatorDrift_eq
    M.canonicalPathMap t records (halign ·)

/-- The martingale residual is right-continuous once the density readout and
the drift-integral term are right-continuous.  This isolates the remaining
analytic work for the real-time supremum theorem to the integral term. -/
theorem martingalePart_continuousWithinAt_Ici_of_driftIntegral
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (ω : Ω) (t : ℝ)
    (hX : ContinuousWithinAt
      (fun s => M.densityProcess pathMap s ω) (Set.Ici t) t)
    (hI : ContinuousWithinAt
      (fun u : ℝ => fun i : Fin d =>
        ∫ s in Set.Icc (0 : ℝ) u,
          (M.rateSpec.drift (M.densityProcess pathMap s ω)) i)
      (Set.Ici t) t) :
    ContinuousWithinAt
      (fun s => M.martingalePart pathMap s ω) (Set.Ici t) t := by
  simpa [martingalePart] using
    (hX.sub continuousWithinAt_const).sub hI

/-- Canonical a.s. wrapper for martingale right-continuity: after the
drift-integral primitive is shown right-continuous on one a.s. event, the
martingale residual is right-continuous at every time on one a.s. event. -/
theorem canonical_martingalePart_forall_continuousWithinAt_Ici_ae_of_driftIntegral
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (hI : ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      ∀ t : ℝ,
        ContinuousWithinAt
          (fun u : ℝ => fun i : Fin d =>
            ∫ s in Set.Icc (0 : ℝ) u,
              (M.rateSpec.drift
                (M.densityProcess M.canonicalPathMap s records)) i)
          (Set.Ici t) t) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      ∀ t : ℝ,
        ContinuousWithinAt
          (fun s => M.martingalePart M.canonicalPathMap s records)
          (Set.Ici t) t := by
  filter_upwards
    [M.canonical_densityProcess_forall_continuousWithinAt_Ici_ae_of_noAbsorbing x₀ hNA,
     hI]
    with records hX hIrecords t
  exact M.martingalePart_continuousWithinAt_Ici_of_driftIntegral
    M.canonicalPathMap records t (hX t) (hIrecords t)

/-- The residual martingale part is deterministically bounded on finite time
horizons, assuming only a realized path map.  This is the pointwise bound used
later for sup-square integrability. -/
theorem exists_martingalePart_norm_bound (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C > 0, ∀ (t : ℝ) (ω : Ω), 0 ≤ t → t ≤ T →
      ‖M.martingalePart pathMap t ω‖ ≤ C := by
  obtain ⟨D, hD, hD_bound⟩ := M.exists_drift_setIntegral_norm_bound pathMap T
  refine ⟨D * T + 3, by positivity, ?_⟩
  intro t ω ht0 htT
  let integralTerm : Fin d → ℝ := fun i =>
    ∫ s in Set.Icc (0 : ℝ) t,
      (M.rateSpec.drift (M.densityProcess pathMap s ω)) i
  have hproc : ‖M.densityProcess pathMap t ω‖ ≤ 1 :=
    M.densityProcess_norm_le pathMap t ω
  have hinit : ‖M.initialCondition pathMap ω‖ ≤ 1 := by
    exact M.densityProcess_norm_le pathMap 0 ω
  have hint : ‖integralTerm‖ ≤ D * T := by
    simpa [integralTerm] using hD_bound t ω ht0 htT
  calc
    ‖M.martingalePart pathMap t ω‖
        = ‖M.densityProcess pathMap t ω - M.initialCondition pathMap ω -
            integralTerm‖ := rfl
    _ ≤ ‖M.densityProcess pathMap t ω - M.initialCondition pathMap ω‖ +
          ‖integralTerm‖ := norm_sub_le _ _
    _ ≤ (‖M.densityProcess pathMap t ω‖ + ‖M.initialCondition pathMap ω‖) +
          ‖integralTerm‖ := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ (1 + 1) + D * T := by gcongr
    _ ≤ D * T + 3 := by linarith

/-- The finite-horizon martingale sup-square is pointwise bounded.  This is
the boundedness half of the remaining integrability proof; measurability of the
continuous-time supremum is still a separate analytic obligation. -/
theorem exists_martingale_sup_sq_bound (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C > 0, ∀ ω : Ω,
      (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.martingalePart pathMap s ω‖ ^ 2) ≤ C := by
  obtain ⟨K, hK, hK_bound⟩ := M.exists_martingalePart_norm_bound pathMap T hT
  refine ⟨K ^ 2 + 1, by positivity, ?_⟩
  intro ω
  refine Real.iSup_le ?_ (by positivity)
  intro s
  refine Real.iSup_le ?_ (by positivity)
  intro hs
  have hnorm := hK_bound s ω hs.1 hs.2
  have hnorm_nonneg : 0 ≤ ‖M.martingalePart pathMap s ω‖ := norm_nonneg _
  calc
    ‖M.martingalePart pathMap s ω‖ ^ 2 ≤ K ^ 2 := by nlinarith
    _ ≤ K ^ 2 + 1 := by linarith

/-- Finite-horizon vector supremum of the Kurtz-facing residual is bounded by
the sum of coordinate finite-horizon suprema. -/
theorem martingalePart_timeSup_norm_sq_le_sum_coord_timeSup_sq
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1)))
    (T : ℝ) (hT : 0 ≤ T) (ω : Ω) :
    (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.martingalePart pathMap s ω‖ ^ 2) ≤
      ∑ i, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        (M.martingalePart pathMap s ω i) ^ 2 := by
  exact Ripple.Kurtz.vector_timeSup_norm_sq_le_sum_coord_timeSup_sq
    (fun s => M.martingalePart pathMap s ω) hT
    (by
      obtain ⟨C, _hC, hbound⟩ := M.exists_martingalePart_norm_bound pathMap T hT
      exact ⟨C, fun s hs0 hsT => hbound s ω hs0 hsT⟩)

/-! ## Measurability of the canonical martingale part and its supremum -/

/-- Joint measurability: `(t, records) ↦ drift(densityProcess(t, records))_i`. -/
theorem measurable_prod_canonicalDrift_component (M : DensityDepCTMC d) (i : Fin d) :
    Measurable (fun p : ℝ × M.canonicalRecordΩ =>
      (M.rateSpec.drift (M.densityProcess M.canonicalPathMap p.1 p.2)) i) := by
  unfold densityProcess
  exact (measurable_pi_apply i).comp
    ((Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) => M.rateSpec.drift (M.scaledState x))).comp
        M.measurable_prod_canonicalPathMap_stateAt)

/-- The drift-integral term in the canonical martingale part is measurable
for each fixed time `t` and component `i`. -/
theorem measurable_canonicalDriftIntegral_component (M : DensityDepCTMC d) (t : ℝ) (i : Fin d) :
    Measurable (fun records : M.canonicalRecordΩ =>
      ∫ s in Set.Icc (0 : ℝ) t,
        (M.rateSpec.drift (M.densityProcess M.canonicalPathMap s records)) i) := by
  have hjoint : StronglyMeasurable
      (fun p : M.canonicalRecordΩ × ℝ =>
        (M.rateSpec.drift (M.densityProcess M.canonicalPathMap p.2 p.1)) i) :=
    ((M.measurable_prod_canonicalDrift_component i).comp measurable_swap).stronglyMeasurable
  exact (hjoint.integral_prod_right'
    (ν := MeasureTheory.Measure.restrict volume (Set.Icc 0 t))).measurable

/-- For a fixed canonical record, the scalar drift readout is measurable in
time.  This avoids unfolding the full product drift expression during section
measurability: section `stateAt` first, then compose with the finite-state
drift observable. -/
theorem measurable_canonicalDrift_component_section
    (M : DensityDepCTMC d) (records : M.canonicalRecordΩ) (i : Fin d) :
    Measurable (fun s : ℝ =>
      (M.rateSpec.drift (M.densityProcess M.canonicalPathMap s records)) i) := by
  have hstate : Measurable (fun s : ℝ =>
      (M.canonicalPathMap records).stateAt s) := by
    have hpair : Measurable (fun s : ℝ => (s, records)) :=
      Measurable.prodMk measurable_id measurable_const
    exact M.measurable_prod_canonicalPathMap_stateAt.comp hpair
  unfold densityProcess
  exact (Measurable.of_discrete
    (f := fun x : Fin d → Fin (M.N + 1) =>
      (M.rateSpec.drift (M.scaledState x)) i)).comp hstate

/-- The scalar canonical drift readout is integrable on every compact
interval. -/
theorem integrableOn_canonicalDrift_component_Icc
    (M : DensityDepCTMC d) (records : M.canonicalRecordΩ) (i : Fin d)
    (a b : ℝ) :
    IntegrableOn
      (fun s : ℝ =>
        (M.rateSpec.drift (M.densityProcess M.canonicalPathMap s records)) i)
      (Set.Icc a b) volume := by
  obtain ⟨C, hC, hbound⟩ :=
    M.rateSpec.exists_drift_bound_on_ball 1 zero_lt_one
  refine MeasureTheory.IntegrableOn.of_bound measure_Icc_lt_top
    ((M.measurable_canonicalDrift_component_section records i).aestronglyMeasurable)
    C ?_
  filter_upwards with s
  exact (norm_le_pi_norm
    (M.rateSpec.drift (M.densityProcess M.canonicalPathMap s records)) i).trans
      (hbound (M.densityProcess M.canonicalPathMap s records)
        (M.densityProcess_norm_le M.canonicalPathMap s records))

/-- For a fixed canonical record and component, the drift-integral primitive
`u ↦ ∫_[0,u] drift_i(X(s)) ds` is right-continuous at every time. -/
theorem canonicalDriftIntegral_component_continuousWithinAt_Ici
    (M : DensityDepCTMC d) (records : M.canonicalRecordΩ) (i : Fin d)
    (t : ℝ) :
    ContinuousWithinAt
      (fun u : ℝ =>
        ∫ s in Set.Icc (0 : ℝ) u,
          (M.rateSpec.drift
            (M.densityProcess M.canonicalPathMap s records)) i)
      (Set.Ici t) t := by
  let f : ℝ → ℝ := fun s =>
    (M.rateSpec.drift (M.densityProcess M.canonicalPathMap s records)) i
  by_cases ht0 : 0 ≤ t
  · let b : ℝ := t + 1
    have hb : t < b := by dsimp [b]; linarith
    have hcontOn :
        ContinuousOn (fun u : ℝ => ∫ s in Set.Icc (0 : ℝ) u, f s)
          (Set.Icc (0 : ℝ) b) :=
      intervalIntegral.continuousOn_primitive_Icc
        (M.integrableOn_canonicalDrift_component_Icc records i 0 b)
    have htmem : t ∈ Set.Icc (0 : ℝ) b := ⟨ht0, le_of_lt hb⟩
    have hwithin :
        ContinuousWithinAt (fun u : ℝ => ∫ s in Set.Icc (0 : ℝ) u, f s)
          (Set.Icc (0 : ℝ) b) t :=
      hcontOn.continuousWithinAt htmem
    have hmem : Set.Icc (0 : ℝ) b ∈ nhdsWithin t (Set.Ici t) := by
      have hIic : Set.Iic b ∈ nhds t := Iic_mem_nhds hb
      refine Filter.mem_of_superset (inter_mem_nhdsWithin (Set.Ici t) hIic) ?_
      intro u hu
      exact ⟨le_trans ht0 hu.1, hu.2⟩
    exact hwithin.mono_of_mem_nhdsWithin hmem
  · have htneg : t < 0 := lt_of_not_ge ht0
    have hevent :
        (fun u : ℝ => ∫ s in Set.Icc (0 : ℝ) u, f s)
          =ᶠ[nhdsWithin t (Set.Ici t)] fun _ => (0 : ℝ) := by
      have hIio : Set.Iio (0 : ℝ) ∈ nhds t := Iio_mem_nhds htneg
      have hmem : Set.Iio (0 : ℝ) ∈ nhdsWithin t (Set.Ici t) :=
        Filter.mem_of_superset (inter_mem_nhdsWithin (Set.Ici t) hIio)
          (fun _ hu => hu.2)
      filter_upwards [hmem] with u hu
      have hempty : Set.Icc (0 : ℝ) u = ∅ :=
        Set.Icc_eq_empty (not_le_of_gt hu)
      rw [hempty, setIntegral_empty]
    have htval :
        (∫ s in Set.Icc (0 : ℝ) t, f s) = (0 : ℝ) := by
      have hempty : Set.Icc (0 : ℝ) t = ∅ :=
        Set.Icc_eq_empty (not_le_of_gt htneg)
      rw [hempty, setIntegral_empty]
    exact (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq
      hevent htval

/-- Vector-valued version of
`canonicalDriftIntegral_component_continuousWithinAt_Ici`. -/
theorem canonicalDriftIntegral_continuousWithinAt_Ici
    (M : DensityDepCTMC d) (records : M.canonicalRecordΩ) (t : ℝ) :
    ContinuousWithinAt
      (fun u : ℝ => fun i : Fin d =>
        ∫ s in Set.Icc (0 : ℝ) u,
          (M.rateSpec.drift
            (M.densityProcess M.canonicalPathMap s records)) i)
      (Set.Ici t) t := by
  rw [continuousWithinAt_pi]
  intro i
  exact M.canonicalDriftIntegral_component_continuousWithinAt_Ici records i t

/-- The drift-integral primitive has the all-time right-continuity needed by
the martingale supremum argument.  This statement is deterministic in the
canonical record, hence holds almost surely under every canonical law. -/
theorem canonical_driftIntegral_forall_continuousWithinAt_Ici_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      ∀ t : ℝ,
        ContinuousWithinAt
          (fun u : ℝ => fun i : Fin d =>
            ∫ s in Set.Icc (0 : ℝ) u,
              (M.rateSpec.drift
                (M.densityProcess M.canonicalPathMap s records)) i)
          (Set.Ici t) t := by
  filter_upwards with records t
  exact M.canonicalDriftIntegral_continuousWithinAt_Ici records t

/-- The canonical martingale part at a fixed time is measurable. -/
theorem measurable_canonicalMartingalePart (M : DensityDepCTMC d) (t : ℝ) :
    Measurable (fun records : M.canonicalRecordΩ =>
      M.martingalePart M.canonicalPathMap t records) := by
  rw [measurable_pi_iff]
  intro i
  simp only [martingalePart, Pi.sub_apply]
  exact (((measurable_pi_apply i).comp (M.measurable_canonicalDensityProcess t)).sub
    ((measurable_pi_apply i).comp (M.measurable_canonicalInitialCondition))).sub
      (M.measurable_canonicalDriftIntegral_component t i)

/-- `‖M^N(t)‖²` at a fixed time is measurable under the canonical law. -/
theorem measurable_canonicalMartingalePart_norm_sq (M : DensityDepCTMC d) (t : ℝ) :
    Measurable (fun records : M.canonicalRecordΩ =>
      ‖M.martingalePart M.canonicalPathMap t records‖ ^ 2) :=
  (measurable_norm.comp (M.measurable_canonicalMartingalePart t)).pow measurable_const

variable [MeasurableSpace Ω] (μ : Measure Ω)

/-- Martingale decomposition: X̄^N(t) = X̄^N(0) + ∫₀ᵗ F(X̄^N(s)) ds + M^N(t).
Immediate from the definition of M^N as the residual. -/
theorem martingale_decomposition (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) :
    ∀ t ≥ 0, ∀ᵐ ω ∂μ,
      M.densityProcess pathMap t ω = M.initialCondition pathMap ω + (fun i =>
        ∫ s in Set.Icc (0:ℝ) t, (M.rateSpec.drift (M.densityProcess pathMap s ω)) i) +
        M.martingalePart pathMap t ω := by
  intro t _ht
  filter_upwards with ω
  simp only [martingalePart]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- M^N(0) = 0 follows from the residual definition and ∫₀⁰ = 0. -/
theorem martingale_init (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) :
    ∀ᵐ ω ∂μ, M.martingalePart pathMap 0 ω = 0 := by
  filter_upwards with ω
  simp only [martingalePart, initialCondition]
  ext i
  simp only [Pi.sub_apply, sub_self, Pi.zero_apply, zero_sub, neg_eq_zero]
  exact setIntegral_measure_zero _ (by simp)

/-- The finite-horizon martingale sup-square random variable is non-negative.
This is pointwise immediate from the square, but packaging it here removes one
regularity proof obligation from the CTMC-to-Kurtz bridge. -/
theorem martingale_sup_sq_nonneg (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (T : ℝ) (_hT : 0 < T) :
    0 ≤ᵐ[μ] fun ω => ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
      ‖M.martingalePart pathMap s ω‖ ^ 2 := by
  filter_upwards with ω
  exact Real.iSup_nonneg fun s =>
    Real.iSup_nonneg fun _hs => sq_nonneg ‖M.martingalePart pathMap s ω‖

/-- The finite-horizon generator-residual sup-square random variable is
non-negative. -/
theorem generatorMartingale_sup_sq_nonneg (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (T : ℝ) (_hT : 0 < T) :
    0 ≤ᵐ[μ] fun ω => ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
      ‖M.generatorMartingalePart pathMap s ω‖ ^ 2 := by
  filter_upwards with ω
  exact Real.iSup_nonneg fun s =>
    Real.iSup_nonneg fun _hs =>
      sq_nonneg ‖M.generatorMartingalePart pathMap s ω‖

/-- Bridge to `Kurtz.DensityProcess` from a realized density-dependent CTMC.

The QV bound is an explicit input here. The canonical CTMC construction still
has to provide this bound from bounded jump sizes and density-dependent rates. -/
noncomputable def toDensityProcess (M : DensityDepCTMC d)
    [IsProbabilityMeasure μ]
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1)))
    (martingale_sup_sq_nonneg : ∀ T > 0,
      0 ≤ᵐ[μ] fun ω => ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.martingalePart pathMap s ω‖ ^ 2)
    (martingale_sup_sq_integrable : ∀ T > 0,
      Integrable (fun ω => ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.martingalePart pathMap s ω‖ ^ 2) μ)
    (martingale_qv_bound : ∀ T > 0, ∃ C > 0,
      ∫ ω, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.martingalePart pathMap s ω‖ ^ 2 ∂μ ≤ C * T / M.N) :
    Ripple.Kurtz.DensityProcess d M.rateSpec M.N μ where
  process := M.densityProcess pathMap
  init := M.initialCondition pathMap
  martingale_part := M.martingalePart pathMap
  decomposition := M.martingale_decomposition μ pathMap
  martingale_init := M.martingale_init μ pathMap
  martingale_sup_sq_nonneg := martingale_sup_sq_nonneg
  martingale_sup_sq_integrable := martingale_sup_sq_integrable
  martingale_qv_bound := martingale_qv_bound

/-- Bridge from the canonical record law of the density-dependent CTMC to
`Kurtz.DensityProcess`.

The remaining stochastic regularity inputs are exactly the sup-square
nonnegativity, integrability, and QV estimate for the canonical martingale
residual. -/
noncomputable def toCanonicalDensityProcess (M : DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1))
    (martingale_sup_sq_nonneg : ∀ T > 0,
      0 ≤ᵐ[M.canonicalRecordMeasure x₀] fun records =>
        ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖M.martingalePart M.canonicalPathMap s records‖ ^ 2)
    (martingale_sup_sq_integrable : ∀ T > 0,
      Integrable (fun records =>
        ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖M.martingalePart M.canonicalPathMap s records‖ ^ 2)
        (M.canonicalRecordMeasure x₀))
    (martingale_qv_bound : ∀ T > 0, ∃ C > 0,
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.martingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤ C * T / M.N) :
    Ripple.Kurtz.DensityProcess d M.rateSpec M.N (M.canonicalRecordMeasure x₀) :=
  M.toDensityProcess (M.canonicalRecordMeasure x₀) M.canonicalPathMap
    martingale_sup_sq_nonneg martingale_sup_sq_integrable martingale_qv_bound

/-- Canonical version of `martingale_sup_sq_nonneg`. -/
theorem canonical_martingale_sup_sq_nonneg (M : DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1)) (T : ℝ) (hT : 0 < T) :
    0 ≤ᵐ[M.canonicalRecordMeasure x₀] fun records =>
      ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.martingalePart M.canonicalPathMap s records‖ ^ 2 :=
  M.martingale_sup_sq_nonneg (M.canonicalRecordMeasure x₀) M.canonicalPathMap T hT

/-- Canonical version of `generatorMartingale_sup_sq_nonneg`. -/
theorem canonical_generatorMartingale_sup_sq_nonneg (M : DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1)) (T : ℝ) (hT : 0 < T) :
    0 ≤ᵐ[M.canonicalRecordMeasure x₀] fun records =>
      ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.generatorMartingalePart M.canonicalPathMap s records‖ ^ 2 :=
  M.generatorMartingale_sup_sq_nonneg
    (M.canonicalRecordMeasure x₀) M.canonicalPathMap T hT

/-- The rational-time sup of `‖M^N(q)‖²` is measurable under the canonical law.
This is the countable-index version used to establish `AEStronglyMeasurable`
of the uncountable-time sup. -/
theorem measurable_canonicalMartingalePart_ratSup (M : DensityDepCTMC d) (T : ℝ) :
    Measurable (fun records : M.canonicalRecordΩ =>
      ⨆ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T),
        ‖M.martingalePart M.canonicalPathMap (q : ℝ) records‖ ^ 2) := by
  apply Measurable.iSup
  intro q
  exact (M.measurable_canonicalMartingalePart_norm_sq (q : ℝ)).iSup_Prop _

/-- Canonical record-law bridge requiring only the two genuinely analytic
finite-horizon inputs that remain after the pointwise non-negativity proof:
integrability of the sup-square and the QV estimate. -/
noncomputable def toCanonicalDensityProcessOfIntegrableQV (M : DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1))
    (martingale_sup_sq_integrable : ∀ T > 0,
      Integrable (fun records =>
        ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖M.martingalePart M.canonicalPathMap s records‖ ^ 2)
        (M.canonicalRecordMeasure x₀))
    (martingale_qv_bound : ∀ T > 0, ∃ C > 0,
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.martingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤ C * T / M.N) :
    Ripple.Kurtz.DensityProcess d M.rateSpec M.N (M.canonicalRecordMeasure x₀) :=
  M.toCanonicalDensityProcess x₀
    (M.canonical_martingale_sup_sq_nonneg x₀)
    martingale_sup_sq_integrable martingale_qv_bound

/-- The rational-time sup of `‖M^N(q)‖²` is integrable under the canonical law.
This is the measurable proxy for the uncountable-time sup. -/
theorem canonical_martingale_ratSup_integrable (M : DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1)) (T : ℝ) (hT : 0 < T) :
    Integrable (fun records : M.canonicalRecordΩ =>
      ⨆ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T),
        ‖M.martingalePart M.canonicalPathMap (q : ℝ) records‖ ^ 2)
      (M.canonicalRecordMeasure x₀) := by
  obtain ⟨K, hK, hK_bound⟩ := M.exists_martingalePart_norm_bound
    M.canonicalPathMap T (le_of_lt hT)
  let C := K ^ 2 + 1
  refine ⟨(M.measurable_canonicalMartingalePart_ratSup T).aestronglyMeasurable, ?_⟩
  apply MeasureTheory.HasFiniteIntegral.of_bounded (C := C)
  filter_upwards with records
  rw [Real.norm_eq_abs, abs_of_nonneg
    (Real.iSup_nonneg fun q => Real.iSup_nonneg fun _ => sq_nonneg _)]
  apply Real.iSup_le (fun q => ?_) (by positivity)
  apply Real.iSup_le (fun hq => ?_) (by positivity)
  have hnorm := hK_bound (q : ℝ) records hq.1 hq.2
  calc ‖M.martingalePart M.canonicalPathMap (q : ℝ) records‖ ^ 2
      ≤ K ^ 2 := by nlinarith [norm_nonneg (M.martingalePart M.canonicalPathMap (q : ℝ) records)]
    _ ≤ C := by linarith

omit [MeasurableSpace Ω] in
/-- The rational-time supremum is bounded by the real-time supremum, pointwise.
This is the easy set-inclusion direction of the eventual real/rational
supremum comparison. -/
theorem ratSup_le_realSup (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (T : ℝ) (hT : 0 ≤ T)
    (ω : Ω) :
    (⨆ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T),
      ‖M.martingalePart pathMap (q : ℝ) ω‖ ^ 2) ≤
    (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
      ‖M.martingalePart pathMap s ω‖ ^ 2) := by
  obtain ⟨K, hK, hK_bound⟩ :=
    M.exists_martingalePart_norm_bound pathMap T hT
  let B : ℝ := K ^ 2
  have hinner_bdd : ∀ s : ℝ,
      BddAbove (Set.range fun _ : 0 ≤ s ∧ s ≤ T =>
        ‖M.martingalePart pathMap s ω‖ ^ 2) := by
    intro s
    refine ⟨B, ?_⟩
    rintro y ⟨hs, rfl⟩
    have hnorm := hK_bound s ω hs.1 hs.2
    nlinarith [norm_nonneg (M.martingalePart pathMap s ω)]
  have houter_bdd : BddAbove (Set.range fun s : ℝ =>
      ⨆ (_ : 0 ≤ s ∧ s ≤ T), ‖M.martingalePart pathMap s ω‖ ^ 2) := by
    refine ⟨B, ?_⟩
    rintro y ⟨s, rfl⟩
    exact Real.iSup_le (fun hs => by
      have hnorm := hK_bound s ω hs.1 hs.2
      nlinarith [norm_nonneg (M.martingalePart pathMap s ω)])
      (by positivity)
  refine Real.iSup_le (fun q => ?_) (Real.iSup_nonneg fun s =>
    Real.iSup_nonneg fun _ => sq_nonneg ‖M.martingalePart pathMap s ω‖)
  refine Real.iSup_le (fun hq => ?_) (Real.iSup_nonneg fun s =>
    Real.iSup_nonneg fun _ => sq_nonneg ‖M.martingalePart pathMap s ω‖)
  exact le_trans
    (le_ciSup (hinner_bdd (q : ℝ)) hq)
    (le_ciSup houter_bdd (q : ℝ))

omit M [MeasurableSpace Ω] μ in
/-- If a real-valued path is right-continuous at every time, then its
finite-horizon real-time supremum is bounded by the maximum of the rational-time
supremum and the endpoint value.  The endpoint term is necessary: a merely
right-continuous path can jump at an irrational terminal time `T`, and rationals
from the left need not see that value. -/
theorem realSup_le_ratSup_max_endpoint_of_right_continuous
    (f : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hcont : ∀ t : ℝ, ContinuousWithinAt f (Set.Ici t) t)
    (hbound : ∃ B : ℝ, ∀ s : ℝ, 0 ≤ s → s ≤ T → f s ≤ B)
    (hnonneg : ∀ s : ℝ, 0 ≤ s → s ≤ T → 0 ≤ f s) :
    (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T), f s) ≤
      max
        (⨆ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T), f (q : ℝ))
        (f T) := by
  obtain ⟨B₀, hB₀⟩ := hbound
  let B : ℝ := max B₀ 0
  have hB_nonneg : 0 ≤ B := by
    exact le_max_right B₀ 0
  have hB : ∀ s : ℝ, 0 ≤ s → s ≤ T → f s ≤ B := by
    intro s hs0 hsT
    exact le_trans (hB₀ s hs0 hsT) (le_max_left B₀ 0)
  let ratSup : ℝ :=
    ⨆ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T), f (q : ℝ)
  have hrat_inner_bdd : ∀ q : ℚ,
      BddAbove (Set.range fun _ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T =>
        f (q : ℝ)) := by
    intro q
    refine ⟨B, ?_⟩
    rintro y ⟨hq, rfl⟩
    exact hB (q : ℝ) hq.1 hq.2
  have hrat_outer_bdd : BddAbove (Set.range fun q : ℚ =>
      ⨆ (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T), f (q : ℝ)) := by
    refine ⟨B, ?_⟩
    rintro y ⟨q, rfl⟩
    exact Real.iSup_le (fun hq => hB (q : ℝ) hq.1 hq.2) hB_nonneg
  have hrat_ge {q : ℚ} (hq : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T) :
      f (q : ℝ) ≤ ratSup := by
    exact le_trans
      (le_ciSup (hrat_inner_bdd q) hq)
      (le_ciSup hrat_outer_bdd q)
  have htarget_nonneg :
      0 ≤ max ratSup (f T) := by
    exact le_trans (hnonneg T hT le_rfl) (le_max_right ratSup (f T))
  refine Real.iSup_le (fun s => ?_) htarget_nonneg
  refine Real.iSup_le (fun hs => ?_) htarget_nonneg
  by_cases hst : s = T
  · simp [hst]
  · have hslt : s < T := lt_of_le_of_ne hs.2 hst
    have hs_le_rat : f s ≤ ratSup := by
      refine le_of_forall_pos_lt_add ?_
      intro ε hε
      obtain ⟨δ, hδpos, hδ⟩ :=
        (Metric.tendsto_nhdsWithin_nhds.mp (hcont s).tendsto) ε hε
      have hs_upper : s < min (s + δ) T := by
        exact lt_min (by linarith) hslt
      obtain ⟨q, hsq, hq_upper⟩ := exists_rat_btwn hs_upper
      have hq0 : 0 ≤ (q : ℝ) := le_trans hs.1 (le_of_lt hsq)
      have hqT : (q : ℝ) ≤ T := by
        exact le_of_lt (lt_of_lt_of_le hq_upper (min_le_right _ _))
      have hq_mem : (q : ℝ) ∈ Set.Ici s := le_of_lt hsq
      have hq_delta : dist (q : ℝ) s < δ := by
        have hq_s_delta : (q : ℝ) < s + δ :=
          lt_of_lt_of_le hq_upper (min_le_left _ _)
        rw [Real.dist_eq]
        rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt hsq))]
        linarith
      have hf_close : dist (f (q : ℝ)) (f s) < ε := hδ hq_mem hq_delta
      have hf_lt : f s < f (q : ℝ) + ε := by
        rw [Real.dist_eq] at hf_close
        have hneg : -ε < f (q : ℝ) - f s := (abs_lt.mp hf_close).1
        linarith
      have hq_le : f (q : ℝ) ≤ ratSup := hrat_ge ⟨hq0, hqT⟩
      exact lt_of_lt_of_le hf_lt (by
        simpa [add_comm] using add_le_add_right hq_le ε)
    exact le_trans hs_le_rat (le_max_left ratSup (f T))

omit [MeasurableSpace Ω] μ in
/-- Pointwise comparison for the martingale finite-horizon supremum.  Under
right-continuity of the martingale path, the continuous-time supremum is the
maximum of the rational-time supremum and the endpoint value. -/
theorem martingale_realSup_eq_ratSup_max_endpoint_of_forall_continuousWithinAt
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (T : ℝ) (hT : 0 ≤ T)
    (ω : Ω)
    (hcont : ∀ t : ℝ,
      ContinuousWithinAt
        (fun s => M.martingalePart pathMap s ω) (Set.Ici t) t) :
    (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.martingalePart pathMap s ω‖ ^ 2) =
      max
        (⨆ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T),
          ‖M.martingalePart pathMap (q : ℝ) ω‖ ^ 2)
        (‖M.martingalePart pathMap T ω‖ ^ 2) := by
  let f : ℝ → ℝ := fun s => ‖M.martingalePart pathMap s ω‖ ^ 2
  obtain ⟨K, hK, hK_bound⟩ :=
    M.exists_martingalePart_norm_bound pathMap T hT
  have hfcont : ∀ t : ℝ, ContinuousWithinAt f (Set.Ici t) t := by
    intro t
    exact (hcont t).norm.pow 2
  have hfbound : ∃ B : ℝ, ∀ s : ℝ, 0 ≤ s → s ≤ T → f s ≤ B := by
    refine ⟨K ^ 2, ?_⟩
    intro s hs0 hsT
    have hnorm := hK_bound s ω hs0 hsT
    dsimp [f]
    nlinarith [norm_nonneg (M.martingalePart pathMap s ω)]
  have hfnonneg : ∀ s : ℝ, 0 ≤ s → s ≤ T → 0 ≤ f s := by
    intro s _hs0 _hsT
    exact sq_nonneg _
  have hle :
      (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T), f s) ≤
        max
          (⨆ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T), f (q : ℝ))
          (f T) :=
    realSup_le_ratSup_max_endpoint_of_right_continuous f T hT
      hfcont hfbound hfnonneg
  have hrat_le :
      (⨆ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T),
        ‖M.martingalePart pathMap (q : ℝ) ω‖ ^ 2) ≤
      (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.martingalePart pathMap s ω‖ ^ 2) :=
    M.ratSup_le_realSup pathMap T hT ω
  have hinner_bdd : ∀ s : ℝ,
      BddAbove (Set.range fun _ : 0 ≤ s ∧ s ≤ T => f s) := by
    intro s
    refine ⟨K ^ 2, ?_⟩
    rintro y ⟨hs, rfl⟩
    have hnorm := hK_bound s ω hs.1 hs.2
    dsimp [f]
    nlinarith [norm_nonneg (M.martingalePart pathMap s ω)]
  have houter_bdd : BddAbove (Set.range fun s : ℝ =>
      ⨆ (_ : 0 ≤ s ∧ s ≤ T), f s) := by
    refine ⟨K ^ 2, ?_⟩
    rintro y ⟨s, rfl⟩
    exact Real.iSup_le (fun hs => by
      have hnorm := hK_bound s ω hs.1 hs.2
      dsimp [f]
      nlinarith [norm_nonneg (M.martingalePart pathMap s ω)])
      (by positivity)
  have hend_le :
      ‖M.martingalePart pathMap T ω‖ ^ 2 ≤
      (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.martingalePart pathMap s ω‖ ^ 2) := by
    dsimp [f] at hinner_bdd houter_bdd
    exact le_trans
      (le_ciSup (hinner_bdd T) ⟨hT, le_rfl⟩)
      (le_ciSup houter_bdd T)
  apply le_antisymm
  · simpa [f] using hle
  · exact max_le hrat_le hend_le

/-- Canonical a.e. real/rational supremum comparison for the martingale
sup-square, conditional on the remaining drift-integral right-continuity
input. -/
theorem canonical_martingale_realSup_eq_ratSup_max_endpoint_ae_of_driftIntegral
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (T : ℝ) (hT : 0 ≤ T)
    (hI : ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      ∀ t : ℝ,
        ContinuousWithinAt
          (fun u : ℝ => fun i : Fin d =>
            ∫ s in Set.Icc (0 : ℝ) u,
              (M.rateSpec.drift
                (M.densityProcess M.canonicalPathMap s records)) i)
          (Set.Ici t) t) :
    (fun records : M.canonicalRecordΩ =>
      ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.martingalePart M.canonicalPathMap s records‖ ^ 2) =ᵐ[M.canonicalRecordMeasure x₀]
    (fun records : M.canonicalRecordΩ =>
      max
        (⨆ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T),
          ‖M.martingalePart M.canonicalPathMap (q : ℝ) records‖ ^ 2)
        (‖M.martingalePart M.canonicalPathMap T records‖ ^ 2)) := by
  filter_upwards
    [M.canonical_martingalePart_forall_continuousWithinAt_Ici_ae_of_driftIntegral
      x₀ hNA hI]
    with records hcont
  exact M.martingale_realSup_eq_ratSup_max_endpoint_of_forall_continuousWithinAt
    M.canonicalPathMap T hT records hcont

/-- Conditional closure of the canonical martingale sup-square integrability
input: after the drift-integral primitive is right-continuous a.e. at every
time, the uncountable-time supremum is a.e. equal to a measurable bounded proxy
formed from rational times plus the terminal value. -/
theorem canonical_martingale_sup_sq_integrable_of_driftIntegral
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (hI : ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      ∀ t : ℝ,
        ContinuousWithinAt
          (fun u : ℝ => fun i : Fin d =>
            ∫ s in Set.Icc (0 : ℝ) u,
              (M.rateSpec.drift
                (M.densityProcess M.canonicalPathMap s records)) i)
          (Set.Ici t) t) :
    ∀ T > 0,
      Integrable (fun records : M.canonicalRecordΩ =>
        ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖M.martingalePart M.canonicalPathMap s records‖ ^ 2)
        (M.canonicalRecordMeasure x₀) := by
  intro T hT
  let ratProxy : M.canonicalRecordΩ → ℝ := fun records =>
    ⨆ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T),
      ‖M.martingalePart M.canonicalPathMap (q : ℝ) records‖ ^ 2
  let endProxy : M.canonicalRecordΩ → ℝ := fun records =>
    ‖M.martingalePart M.canonicalPathMap T records‖ ^ 2
  let proxy : M.canonicalRecordΩ → ℝ := fun records =>
    max (ratProxy records) (endProxy records)
  have hproxy_meas : Measurable proxy := by
    exact (M.measurable_canonicalMartingalePart_ratSup T).max
      (M.measurable_canonicalMartingalePart_norm_sq T)
  obtain ⟨K, hK, hK_bound⟩ := M.exists_martingalePart_norm_bound
    M.canonicalPathMap T (le_of_lt hT)
  let C : ℝ := K ^ 2
  have hC_nonneg : 0 ≤ C := by positivity
  have hproxy_int : Integrable proxy (M.canonicalRecordMeasure x₀) := by
    refine MeasureTheory.Integrable.of_bound
      hproxy_meas.aestronglyMeasurable C ?_
    filter_upwards with records
    have hrat_nonneg : 0 ≤ ratProxy records := by
      dsimp [ratProxy]
      exact Real.iSup_nonneg fun q =>
        Real.iSup_nonneg fun _ => sq_nonneg _
    have hend_nonneg : 0 ≤ endProxy records := by
      dsimp [endProxy]
      exact sq_nonneg _
    have hproxy_nonneg : 0 ≤ proxy records := by
      dsimp [proxy]
      exact le_trans hrat_nonneg (le_max_left (ratProxy records) (endProxy records))
    have hrat_le : ratProxy records ≤ C := by
      dsimp [ratProxy, C]
      refine Real.iSup_le (fun q => ?_) hC_nonneg
      refine Real.iSup_le (fun hq => ?_) hC_nonneg
      have hnorm := hK_bound (q : ℝ) records hq.1 hq.2
      nlinarith [norm_nonneg
        (M.martingalePart M.canonicalPathMap (q : ℝ) records)]
    have hend_le : endProxy records ≤ C := by
      dsimp [endProxy, C]
      have hnorm := hK_bound T records (le_of_lt hT) le_rfl
      nlinarith [norm_nonneg (M.martingalePart M.canonicalPathMap T records)]
    have hproxy_le : proxy records ≤ C := by
      dsimp [proxy]
      exact max_le hrat_le hend_le
    rw [Real.norm_eq_abs, abs_of_nonneg hproxy_nonneg]
    exact hproxy_le
  have heq :
      proxy =ᵐ[M.canonicalRecordMeasure x₀]
        (fun records : M.canonicalRecordΩ =>
          ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
            ‖M.martingalePart M.canonicalPathMap s records‖ ^ 2) := by
    exact (M.canonical_martingale_realSup_eq_ratSup_max_endpoint_ae_of_driftIntegral
      x₀ hNA T (le_of_lt hT) hI).symm
  exact hproxy_int.congr heq

/-- Canonical martingale sup-square integrability under the no-absorbing
condition.  The proof combines deterministic drift-integral primitive
right-continuity with the rational-time measurable proxy. -/
theorem canonical_martingale_sup_sq_integrable
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing) :
    ∀ T > 0,
      Integrable (fun records : M.canonicalRecordΩ =>
        ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖M.martingalePart M.canonicalPathMap s records‖ ^ 2)
        (M.canonicalRecordMeasure x₀) :=
  M.canonical_martingale_sup_sq_integrable_of_driftIntegral x₀ hNA
    (M.canonical_driftIntegral_forall_continuousWithinAt_Ici_ae x₀)

/-- Canonical generator-residual sup-square integrability transfers from the
Kurtz-facing martingale residual once simplex-local drift alignment identifies
the two residuals a.s.  This is the regularity side needed before applying a
Doob/bracket estimate directly to `generatorMartingalePart`. -/
theorem canonical_generatorMartingale_sup_sq_integrable_of_boundaryCompatibleOnSimplex
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (hNA : M.NoAbsorbing) (hcons : M.ConservativeJumps)
    (hinit : M.InSimplex x₀) (hBC : M.BoundaryCompatibleOnSimplex) :
    ∀ T > 0,
      Integrable (fun records : M.canonicalRecordΩ =>
        ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖M.generatorMartingalePart M.canonicalPathMap s records‖ ^ 2)
        (M.canonicalRecordMeasure x₀) := by
  intro T hT
  have hmart :=
    M.canonical_martingale_sup_sq_integrable x₀ hNA T hT
  have hsup :
      (fun records : M.canonicalRecordΩ =>
        ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖M.martingalePart M.canonicalPathMap s records‖ ^ 2)
        =ᵐ[M.canonicalRecordMeasure x₀]
      (fun records : M.canonicalRecordΩ =>
        ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖M.generatorMartingalePart M.canonicalPathMap s records‖ ^ 2) := by
    filter_upwards
      [M.canonical_generatorMartingalePart_eq_martingalePart_ae_of_boundaryCompatibleOnSimplex
        x₀ hNA hcons hinit hBC]
      with records heq
    simp [heq]
  exact hmart.congr hsup

/-- The remaining stochastic QV estimate follows from a Doob/bracket inequality
against the instantaneous-QV time integral.  This theorem isolates the final
probabilistic obligation from the deterministic density-dependent rate bound. -/
theorem canonical_martingale_qv_bound_of_instantQV_doob
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    {A : ℝ} (hA : 0 < A)
    (hDoob : ∀ T > 0,
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.martingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      A * ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).stateAt s))
        ∂M.canonicalRecordMeasure x₀) :
    ∀ T > 0, ∃ C > 0,
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.martingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤ C * T / M.N := by
  intro T hT
  obtain ⟨C₀, hC₀, hinst⟩ :=
    M.canonical_instantQVRate_setIntegral_expectation_bound x₀ T (le_of_lt hT)
  refine ⟨A * C₀, mul_pos hA hC₀, ?_⟩
  calc
    ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.martingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀
        ≤ A * ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
          M.instantQVRate ((M.canonicalPathMap records).stateAt s))
          ∂M.canonicalRecordMeasure x₀ := hDoob T hT
    _ ≤ A * (C₀ * T / (M.N : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hinst (le_of_lt hA)
    _ = (A * C₀) * T / (M.N : ℝ) := by ring

/-- Variant of `canonical_martingale_qv_bound_of_instantQV_doob` where the
Doob/bracket input is stated for the residual compensated by the actual
finite-lattice generator drift.  Under simplex-local drift alignment, this is
equivalent to the Kurtz-facing `martingalePart` on the canonical law. -/
theorem canonical_martingale_qv_bound_of_generator_instantQV_doob
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (hNA : M.NoAbsorbing) (hcons : M.ConservativeJumps)
    (hinit : M.InSimplex x₀) (hBC : M.BoundaryCompatibleOnSimplex)
    {A : ℝ} (hA : 0 < A)
    (hDoob : ∀ T > 0,
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.generatorMartingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      A * ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).stateAt s))
        ∂M.canonicalRecordMeasure x₀) :
    ∀ T > 0, ∃ C > 0,
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.martingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤ C * T / M.N := by
  refine M.canonical_martingale_qv_bound_of_instantQV_doob x₀ hA ?_
  intro T hT
  have hsup :
      (fun records : M.canonicalRecordΩ =>
        ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖M.martingalePart M.canonicalPathMap s records‖ ^ 2)
        =ᵐ[M.canonicalRecordMeasure x₀]
      (fun records : M.canonicalRecordΩ =>
        ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖M.generatorMartingalePart M.canonicalPathMap s records‖ ^ 2) := by
    filter_upwards
      [M.canonical_generatorMartingalePart_eq_martingalePart_ae_of_boundaryCompatibleOnSimplex
        x₀ hNA hcons hinit hBC]
      with records heq
    simp [heq]
  calc
    ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.martingalePart M.canonicalPathMap s records‖ ^ 2
          ∂M.canonicalRecordMeasure x₀
        = ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖M.generatorMartingalePart M.canonicalPathMap s records‖ ^ 2
          ∂M.canonicalRecordMeasure x₀ := integral_congr_ae hsup
    _ ≤ A * ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).stateAt s))
        ∂M.canonicalRecordMeasure x₀ := hDoob T hT

/-- Coordinate-to-vector reduction for the remaining generator-side
Doob/bracket input.  If each coordinate clock-time supremum is controlled by
the same instantaneous-QV integral, then the vector-valued generator residual
is controlled with the dimension factor. -/
theorem canonical_generator_instantQV_doob_of_coord_bounds
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    {A : ℝ}
    (hVecInt : ∀ T > 0,
      Integrable (fun records : M.canonicalRecordΩ =>
        ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖M.generatorMartingalePart M.canonicalPathMap s records‖ ^ 2)
        (M.canonicalRecordMeasure x₀))
    (hCoordInt : ∀ T > 0, ∀ i : Fin d,
      Integrable (fun records : M.canonicalRecordΩ =>
        ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          (M.generatorMartingalePart M.canonicalPathMap s records i) ^ 2)
        (M.canonicalRecordMeasure x₀))
    (hCoord : ∀ T > 0, ∀ i : Fin d,
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        (M.generatorMartingalePart M.canonicalPathMap s records i) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      A * ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).stateAt s))
        ∂M.canonicalRecordMeasure x₀) :
    ∀ T > 0,
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.generatorMartingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      ((Fintype.card (Fin d) : ℝ) * A) *
        ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
          M.instantQVRate ((M.canonicalPathMap records).stateAt s))
          ∂M.canonicalRecordMeasure x₀ := by
  intro T hT
  let μ := M.canonicalRecordMeasure x₀
  let V : M.canonicalRecordΩ → ℝ := fun records =>
    ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
      ‖M.generatorMartingalePart M.canonicalPathMap s records‖ ^ 2
  let C : Fin d → M.canonicalRecordΩ → ℝ := fun i records =>
    ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
      (M.generatorMartingalePart M.canonicalPathMap s records i) ^ 2
  let Q : M.canonicalRecordΩ → ℝ := fun records =>
    ∫ s in Set.Icc (0 : ℝ) T,
      M.instantQVRate ((M.canonicalPathMap records).stateAt s)
  have hsumC_int : Integrable (fun records => ∑ i : Fin d, C i records) μ := by
    exact integrable_finset_sum Finset.univ fun i _ => hCoordInt T hT i
  have hpoint :
      V ≤ᵐ[μ] fun records : M.canonicalRecordΩ => ∑ i : Fin d, C i records := by
    filter_upwards with records
    simpa [V, C] using
      M.generatorMartingalePart_timeSup_norm_sq_le_sum_coord_timeSup_sq
        M.canonicalPathMap T (le_of_lt hT) records
  have hmono := integral_mono_ae (hVecInt T hT) hsumC_int hpoint
  calc
    ∫ records, V records ∂μ
        ≤ ∫ records, ∑ i : Fin d, C i records ∂μ := hmono
    _ = ∑ i : Fin d, ∫ records, C i records ∂μ := by
          rw [integral_finset_sum Finset.univ]
          intro i _
          exact hCoordInt T hT i
    _ ≤ ∑ _i : Fin d, A * ∫ records, Q records ∂μ := by
          exact Finset.sum_le_sum fun i _ => by
            simpa [C, Q, μ] using hCoord T hT i
    _ = (Fintype.card (Fin d) : ℝ) * (A * ∫ records, Q records ∂μ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ((Fintype.card (Fin d) : ℝ) * A) *
          ∫ records, Q records ∂μ := by ring
    _ = ((Fintype.card (Fin d) : ℝ) * A) *
        ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
          M.instantQVRate ((M.canonicalPathMap records).stateAt s))
          ∂M.canonicalRecordMeasure x₀ := by
          simp [Q, μ]

/-- Coordinate-to-vector reduction for the generator-side Doob/bracket input
when the coordinate estimates are stated against coordinate instantaneous-QV
time integrals.  The remaining comparison between summed coordinate QV and
vector QV is isolated as `hCoordQV`. -/
theorem canonical_generator_instantQV_doob_of_coord_instantCoordQV_bounds
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    {A B : ℝ} (hA : 0 ≤ A)
    (hVecInt : ∀ T > 0,
      Integrable (fun records : M.canonicalRecordΩ =>
        ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖M.generatorMartingalePart M.canonicalPathMap s records‖ ^ 2)
        (M.canonicalRecordMeasure x₀))
    (hCoordInt : ∀ T > 0, ∀ i : Fin d,
      Integrable (fun records : M.canonicalRecordΩ =>
        ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          (M.generatorMartingalePart M.canonicalPathMap s records i) ^ 2)
        (M.canonicalRecordMeasure x₀))
    (hCoord : ∀ T > 0, ∀ i : Fin d,
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        (M.generatorMartingalePart M.canonicalPathMap s records i) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      A * ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantCoordQVRate ((M.canonicalPathMap records).stateAt s) i)
        ∂M.canonicalRecordMeasure x₀)
    (hCoordQV : ∀ T > 0,
      (∑ i : Fin d,
        ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
          M.instantCoordQVRate ((M.canonicalPathMap records).stateAt s) i)
          ∂M.canonicalRecordMeasure x₀) ≤
      B * ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).stateAt s))
        ∂M.canonicalRecordMeasure x₀) :
    ∀ T > 0,
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.generatorMartingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      (A * B) * ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).stateAt s))
        ∂M.canonicalRecordMeasure x₀ := by
  intro T hT
  let μ := M.canonicalRecordMeasure x₀
  let V : M.canonicalRecordΩ → ℝ := fun records =>
    ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
      ‖M.generatorMartingalePart M.canonicalPathMap s records‖ ^ 2
  let C : Fin d → M.canonicalRecordΩ → ℝ := fun i records =>
    ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
      (M.generatorMartingalePart M.canonicalPathMap s records i) ^ 2
  let Qc : Fin d → ℝ := fun i =>
    ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
      M.instantCoordQVRate ((M.canonicalPathMap records).stateAt s) i)
      ∂M.canonicalRecordMeasure x₀
  let Q : ℝ :=
    ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
      M.instantQVRate ((M.canonicalPathMap records).stateAt s))
      ∂M.canonicalRecordMeasure x₀
  have hsumC_int : Integrable (fun records => ∑ i : Fin d, C i records) μ := by
    exact integrable_finset_sum Finset.univ fun i _ => hCoordInt T hT i
  have hpoint :
      V ≤ᵐ[μ] fun records : M.canonicalRecordΩ => ∑ i : Fin d, C i records := by
    filter_upwards with records
    simpa [V, C] using
      M.generatorMartingalePart_timeSup_norm_sq_le_sum_coord_timeSup_sq
        M.canonicalPathMap T (le_of_lt hT) records
  have hmono := integral_mono_ae (hVecInt T hT) hsumC_int hpoint
  calc
    ∫ records, V records ∂μ
        ≤ ∫ records, ∑ i : Fin d, C i records ∂μ := hmono
    _ = ∑ i : Fin d, ∫ records, C i records ∂μ := by
          rw [integral_finset_sum Finset.univ]
          intro i _
          exact hCoordInt T hT i
    _ ≤ ∑ i : Fin d, A * Qc i := by
          exact Finset.sum_le_sum fun i _ => by
            simpa [C, Qc, μ] using hCoord T hT i
    _ = A * (∑ i : Fin d, Qc i) := by
          rw [Finset.mul_sum]
    _ ≤ A * (B * Q) := by
          exact mul_le_mul_of_nonneg_left
            (by simpa [Qc, Q] using hCoordQV T hT) hA
    _ = (A * B) * Q := by ring
    _ = (A * B) * ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).stateAt s))
        ∂M.canonicalRecordMeasure x₀ := by
          simp [Q]

/-- Coordinate-to-vector generator-side Doob/bracket reduction with the
coordinate instantaneous-QV comparison discharged by the finite-dimensional
pointwise QV bound. -/
theorem canonical_generator_instantQV_doob_of_coord_instantCoordQV_bounds_card
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    {A : ℝ} (hA : 0 ≤ A)
    (hVecInt : ∀ T > 0,
      Integrable (fun records : M.canonicalRecordΩ =>
        ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖M.generatorMartingalePart M.canonicalPathMap s records‖ ^ 2)
        (M.canonicalRecordMeasure x₀))
    (hCoordInt : ∀ T > 0, ∀ i : Fin d,
      Integrable (fun records : M.canonicalRecordΩ =>
        ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          (M.generatorMartingalePart M.canonicalPathMap s records i) ^ 2)
        (M.canonicalRecordMeasure x₀))
    (hCoord : ∀ T > 0, ∀ i : Fin d,
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        (M.generatorMartingalePart M.canonicalPathMap s records i) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      A * ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantCoordQVRate ((M.canonicalPathMap records).stateAt s) i)
        ∂M.canonicalRecordMeasure x₀) :
    ∀ T > 0,
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.generatorMartingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      (A * (Fintype.card (Fin d) : ℝ)) *
        ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
          M.instantQVRate ((M.canonicalPathMap records).stateAt s))
          ∂M.canonicalRecordMeasure x₀ := by
  exact M.canonical_generator_instantQV_doob_of_coord_instantCoordQV_bounds
    x₀ hA hVecInt hCoordInt hCoord
    (fun T hT => by
      simpa using
        M.canonical_sum_instantCoordQVRate_setIntegral_le_card_mul_instantQVRate
          x₀ T (le_of_lt hT))

/-- Canonical record-law bridge under `NoAbsorbing`, now requiring only the
quadratic-variation estimate.  Sup-square nonnegativity and integrability are
proved from the canonical CTMC path regularity and bounded drift. -/
noncomputable def toCanonicalDensityProcessOfQV (M : DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    (martingale_qv_bound : ∀ T > 0, ∃ C > 0,
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.martingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤ C * T / M.N) :
    Ripple.Kurtz.DensityProcess d M.rateSpec M.N (M.canonicalRecordMeasure x₀) :=
  M.toCanonicalDensityProcess x₀
    (M.canonical_martingale_sup_sq_nonneg x₀)
    (M.canonical_martingale_sup_sq_integrable x₀ hNA)
    martingale_qv_bound

/-- Canonical bridge where the only remaining stochastic input is a
Doob/bracket inequality comparing the martingale supremum to the
instantaneous-QV time integral. -/
noncomputable def toCanonicalDensityProcessOfInstantQVDoob (M : DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1)) (hNA : M.NoAbsorbing)
    {A : ℝ} (hA : 0 < A)
    (hDoob : ∀ T > 0,
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.martingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      A * ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).stateAt s))
        ∂M.canonicalRecordMeasure x₀) :
    Ripple.Kurtz.DensityProcess d M.rateSpec M.N (M.canonicalRecordMeasure x₀) :=
  M.toCanonicalDensityProcessOfQV x₀ hNA
    (M.canonical_martingale_qv_bound_of_instantQV_doob x₀ hA hDoob)

/-- Canonical bridge whose remaining stochastic input is a Doob/bracket
inequality for the residual compensated by the actual finite-lattice generator
drift.  The bridge transfers it to the Kurtz-facing residual using
simplex-local drift alignment. -/
noncomputable def toCanonicalDensityProcessOfGeneratorInstantQVDoob
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (hNA : M.NoAbsorbing) (hcons : M.ConservativeJumps)
    (hinit : M.InSimplex x₀) (hBC : M.BoundaryCompatibleOnSimplex)
    {A : ℝ} (hA : 0 < A)
    (hDoob : ∀ T > 0,
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.generatorMartingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      A * ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).stateAt s))
        ∂M.canonicalRecordMeasure x₀) :
    Ripple.Kurtz.DensityProcess d M.rateSpec M.N (M.canonicalRecordMeasure x₀) :=
  M.toCanonicalDensityProcessOfQV x₀ hNA
    (M.canonical_martingale_qv_bound_of_generator_instantQV_doob
      x₀ hNA hcons hinit hBC hA hDoob)

end DensityDepCTMC
end Ripple.CTMC
