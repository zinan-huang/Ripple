import Ripple.PopulationProtocol.PopProto.Convergence.AugmentedState

/-!
# Original-chain occupation counts

Region exits do not erase prior visits. This chain retains the original
configuration and interaction counters and adds four cumulative region counts.
Each count records the configuration before an interaction, as in Table 1 of
Angluin--Aspnes--Eisenstat. Active regions exclude consensus. The central
occupation supermartingale therefore bounds all visits, including re-entry.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Ripple.PopulationProtocol.PopProto.Config

/-- Cumulative pre-interaction visits to the four active regions. -/
structure RegionCounts where
  central : ℕ
  blank : ℕ
  left : ℕ
  right : ℕ
  deriving Inhabited

/-- Add one visit to each active region containing the current configuration.
The region-disjointness theorem ensures at most one increment on a real step. -/
noncomputable def RegionCounts.record {n : ℕ} (s : RegionCounts) (c : Config n) :
    RegionCounts := by
  classical
  exact ⟨s.central + if c ∈ activeCentral then 1 else 0,
    s.blank + if c ∈ activeLargeB then 1 else 0,
    s.left + if c ∈ activeLargeX then 1 else 0,
    s.right + if c ∈ activeLargeY then 1 else 0⟩

/-- Original configuration, cumulative interaction counts, and region visits. -/
abbrev OccupationConfig (n : ℕ) := AugConfig n × RegionCounts

noncomputable instance {n : ℕ} : MeasurableSpace (OccupationConfig n) := ⊤
instance {n : ℕ} : DiscreteMeasurableSpace (OccupationConfig n) where
  forall_measurableSet _ := trivial

variable {n : ℕ}

/-- One original augmented transition, recording the current region. -/
noncomputable def occupationStepDist (hn : n ≥ 2) (a : OccupationConfig n) :
    PMF (OccupationConfig n) :=
  (augStepDist a.1 hn).map (fun b => (b, a.2.record a.1.1))

/-- The occupation chain does not stop at region boundaries. -/
noncomputable def occupationKernel (hn : n ≥ 2) :
    Kernel (OccupationConfig n) (OccupationConfig n) where
  toFun a := (occupationStepDist hn a).toMeasure
  measurable' := Measurable.of_discrete

instance (hn : n ≥ 2) : IsMarkovKernel (occupationKernel hn) where
  isProbabilityMeasure a := by
    change IsProbabilityMeasure (occupationStepDist hn a).toMeasure
    infer_instance

/-- Integrating a function after one step keeps the original augmented
transition measure; only the deterministic region counters are added. -/
theorem occupationKernel_lintegral (hn : n ≥ 2) (a : OccupationConfig n)
    (f : OccupationConfig n → ℝ≥0∞) :
    ∫⁻ b, f b ∂(occupationKernel hn a) =
      ∫⁻ b, f (b, a.2.record a.1.1) ∂(augStepDist a.1 hn).toMeasure := by
  change ∫⁻ b, f b ∂(occupationStepDist hn a).toMeasure = _
  unfold occupationStepDist
  rw [← PMF.toMeasure_map, lintegral_map Measurable.of_discrete Measurable.of_discrete]
  exact Measurable.of_discrete

/-- Exponential charge for all central visits, offset by interaction counts. -/
noncomputable def centralOccupationW (a : OccupationConfig n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp ((a.2.central : ℝ) / (n : ℝ))) * countingW a.1

/-- The interaction-only counting factor never increases in expectation on
the original chain. No regional condition is required for this weaker bound. -/
theorem countingW_original_per_step (hn : n ≥ 2) (a : AugConfig n) :
    ∫⁻ b, countingW b ∂(augStepDist a hn).toMeasure ≤ countingW a := by
  have hle : ∀ q : State × State,
      countingW (augStep a.1 a.2.1 a.2.2 q.1 q.2) ≤ countingW a := by
    intro ⟨i, r⟩
    simp only [countingW, augStep]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg' n)
    simp only [Nat.cast_add, Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_one]
    have h1 : (0 : ℝ) ≤ if isVB i r then (1 : ℝ) else 0 := by split_ifs <;> norm_num
    have h2 : (0 : ℝ) ≤ if isXY i r then (1 : ℝ) else 0 := by split_ifs <;> norm_num
    linarith
  unfold augStepDist
  rw [← PMF.toMeasure_map _ _ Measurable.of_discrete,
    lintegral_map Measurable.of_discrete Measurable.of_discrete]
  calc _ ≤ ∫⁻ _, countingW a ∂(a.1.interactionPMF hn).toMeasure :=
      lintegral_mono hle
    _ = countingW a := by simp

/-- The central occupation supermartingale is valid through every region
crossing. In the central region the extra visit charge is paid by the existing
one-step contraction; outside it the charge is unchanged. -/
theorem centralOccupationW_per_step (hn : n ≥ 2) (a : OccupationConfig n) :
    ∫⁻ b, centralOccupationW b ∂(occupationKernel hn a) ≤ centralOccupationW a := by
  classical
  rw [occupationKernel_lintegral]
  simp only [centralOccupationW]
  rw [lintegral_const_mul _ (Measurable.of_discrete : Measurable
    (countingW : AugConfig n → ℝ≥0∞))]
  by_cases hc : a.1.1 ∈ activeCentral
  · have hcontract := countingW_active_contraction hn a.1.1 hc.1 hc.2 a.1.2.1 a.1.2.2
    have hcancel :
        ENNReal.ofReal (Real.exp (((a.2.central : ℝ) + 1) / (n : ℝ))) *
          ENNReal.ofReal (Real.exp (-(1 : ℝ) / (n : ℝ))) =
        ENNReal.ofReal (Real.exp ((a.2.central : ℝ) / (n : ℝ))) := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      ring
    simpa only [RegionCounts.record, hc, if_pos, Nat.cast_add, Nat.cast_one,
      ← mul_assoc, hcancel] using
      (mul_le_mul_left' hcontract
        (ENNReal.ofReal (Real.exp (((a.2.central : ℝ) + 1) / (n : ℝ)))))
  · simpa only [RegionCounts.record, hc, if_false, Nat.add_zero] using
      (mul_le_mul_left' (countingW_original_per_step hn a.1)
        (ENNReal.ofReal (Real.exp ((a.2.central : ℝ) / (n : ℝ)))))

/-- From zero counters the original-chain central occupation exponential
moment is at most one, at every finite time. -/
theorem centralOccupationW_iteration (hn : n ≥ 2) (c₀ : Config n) (t : ℕ) :
    ∫⁻ a, centralOccupationW a
      ∂((occupationKernel hn ^ t) ((c₀, 0, 0), ⟨0, 0, 0, 0⟩)) ≤ 1 := by
  have h := Ripple.PopulationProtocol.PopProtoCommon.lintegral_geometric_decay (occupationKernel hn) centralOccupationW
    Measurable.of_discrete 1
    (fun a => by simpa using centralOccupationW_per_step hn a)
    t ((c₀, 0, 0), ⟨0, 0, 0, 0⟩)
  simpa [centralOccupationW, countingW] using h

/-- The central charge equals the exponential of visits minus interaction
charges, making the probability event refer to actual cumulative counts. -/
theorem centralOccupationW_eq (a : OccupationConfig n) :
    centralOccupationW a = ENNReal.ofReal (Real.exp
      (((a.2.central : ℝ) - 130 * (a.1.2.1 : ℝ) - 258 * (a.1.2.2 : ℝ)) / (n : ℝ))) := by
  unfold centralOccupationW countingW
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2
  ring

/-- Global central-occupation tail. This counts all central visits in the
first t original interactions, rather than only visits before the first exit. -/
theorem centralOccupation_tail (hn : n ≥ 2) (c₀ : Config n) (t : ℕ) (u : ℝ) :
    ((occupationKernel hn ^ t) ((c₀, 0, 0), ⟨0, 0, 0, 0⟩))
      {a : OccupationConfig n |
        130 * (a.1.2.1 : ℝ) + 258 * (a.1.2.2 : ℝ) + u ≤ (a.2.central : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-u / (n : ℝ))) := by
  let μ := (occupationKernel hn ^ t) ((c₀, 0, 0), ⟨0, 0, 0, 0⟩)
  let z := ENNReal.ofReal (Real.exp (u / (n : ℝ)))
  have hz0 : z ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hzt : z ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsub : {a : OccupationConfig n |
      130 * (a.1.2.1 : ℝ) + 258 * (a.1.2.2 : ℝ) + u ≤ (a.2.central : ℝ)} ⊆
      {a | z ≤ centralOccupationW a} := by
    intro a ha
    rw [Set.mem_setOf_eq, centralOccupationW_eq]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg' n)
    dsimp at ha
    linarith
  have hm : z * μ {a | z ≤ centralOccupationW a} ≤ 1 :=
    (mul_meas_ge_le_lintegral₀ (μ := μ)
      (Measurable.of_discrete : Measurable centralOccupationW).aemeasurable z).trans
      (centralOccupationW_iteration hn c₀ t)
  have hbound : μ {a | z ≤ centralOccupationW a} ≤ z⁻¹ := by
    calc _ = z⁻¹ * (z * μ {a | z ≤ centralOccupationW a}) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hz0 hzt, one_mul]
      _ ≤ z⁻¹ * 1 := mul_le_mul_left' hm _
      _ = z⁻¹ := mul_one _
  apply (measure_mono hsub).trans
  calc μ {a | z ≤ centralOccupationW a} ≤ z⁻¹ := hbound
    _ = ENNReal.ofReal (Real.exp (-u / (n : ℝ))) := by
      dsimp [z]
      rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]
      congr 2
      ring

end Ripple.PopulationProtocol.PopProto.Config
