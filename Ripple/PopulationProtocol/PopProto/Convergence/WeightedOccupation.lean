import Ripple.PopulationProtocol.PopProto.Convergence.OccupationTime

/-! # Composition of global occupation charges

A weighted one-step inequality for the actual scheduler lifts to the full
occupation chain. Region-count increments are deterministic functions of the
pre-interaction configuration; VB and XY charges follow the sampled pair.
-/
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Ripple.PopulationProtocol.PopProto.Config
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

/-- The exponential occupation charge times its compensating potential. -/
noncomputable def weightedOccupation (φ : Config n → ℝ≥0∞)
    (w : RegionCounts → ℝ) (vb xy : ℝ) (a : OccupationConfig n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp ((w a.2 - vb * (a.1.2.1 : ℝ) -
    xy * (a.1.2.2 : ℝ)) / (n : ℝ))) * φ a.1.1

/-- The one-step exponential charge on the original scheduler. -/
noncomputable def occupationStepCharge (φ : Config n → ℝ≥0∞)
    (d : Config n → ℝ) (vb xy : ℝ) (c : Config n) (q : State × State) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp ((d c - vb * (if isVB q.1 q.2 then 1 else 0) -
    xy * (if isXY q.1 q.2 then 1 else 0)) / (n : ℝ))) * φ (c.stepOrSelf q.1 q.2)

/-- Re-express a full occupation-chain step using the original scheduler. -/
theorem occupationKernel_lintegral_scheduler (hn : n ≥ 2) (a : OccupationConfig n)
    (f : OccupationConfig n → ℝ≥0∞) :
    ∫⁻ b, f b ∂(occupationKernel hn a) =
      ∫⁻ q : State × State,
        f (augStep a.1.1 a.1.2.1 a.1.2.2 q.1 q.2, a.2.record a.1.1)
        ∂(a.1.1.interactionPMF hn).toMeasure := by
  rw [occupationKernel_lintegral]
  unfold augStepDist
  rw [← PMF.toMeasure_map _ _ Measurable.of_discrete,
    lintegral_map Measurable.of_discrete Measurable.of_discrete]

/-- A genuine scheduler-level inequality lifts to an occupation-chain
supermartingale. The hypotheses are the local producers, not the desired
finite-time conclusion; callers must supply them for the concrete protocol. -/
theorem weightedOccupation_per_step (hn : n ≥ 2)
    (φ : Config n → ℝ≥0∞) (w : RegionCounts → ℝ) (d : Config n → ℝ) (vb xy : ℝ)
    (hw : ∀ s c, w (s.record c) = w s + d c)
    (hstep : ∀ c, ∫⁻ q, occupationStepCharge φ d vb xy c q
      ∂(c.interactionPMF hn).toMeasure ≤ φ c)
    (a : OccupationConfig n) :
    ∫⁻ b, weightedOccupation φ w vb xy b ∂(occupationKernel hn a) ≤
      weightedOccupation φ w vb xy a := by
  classical
  rw [occupationKernel_lintegral_scheduler]
  let z := ENNReal.ofReal (Real.exp ((w a.2 - vb * (a.1.2.1 : ℝ) -
    xy * (a.1.2.2 : ℝ)) / (n : ℝ)))
  have hfactor : ∀ q : State × State,
      weightedOccupation φ w vb xy
        (augStep a.1.1 a.1.2.1 a.1.2.2 q.1 q.2, a.2.record a.1.1) =
      z * occupationStepCharge φ d vb xy a.1.1 q := by
    intro q
    unfold weightedOccupation occupationStepCharge
    simp only [augStep, hw, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    dsimp [z]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 2
    ring
  simp_rw [hfactor]
  rw [lintegral_const_mul _ Measurable.of_discrete]
  exact mul_le_mul_left' (hstep a.1.1) z

/-- Global finite-time expectation bound for an occupation charge whose
concrete one-step producer is valid on the entire original state space. -/
theorem weightedOccupation_iteration (hn : n ≥ 2)
    (φ : Config n → ℝ≥0∞) (w : RegionCounts → ℝ) (d : Config n → ℝ) (vb xy : ℝ)
    (hw : ∀ s c, w (s.record c) = w s + d c)
    (hzero : w ⟨0, 0, 0, 0⟩ = 0)
    (hstep : ∀ c, ∫⁻ q, occupationStepCharge φ d vb xy c q
      ∂(c.interactionPMF hn).toMeasure ≤ φ c)
    (c₀ : Config n) (t : ℕ) :
    ∫⁻ a, weightedOccupation φ w vb xy a
      ∂((occupationKernel hn ^ t) ((c₀, 0, 0), ⟨0, 0, 0, 0⟩)) ≤ φ c₀ := by
  have h := Ripple.PopulationProtocol.PopProtoCommon.lintegral_geometric_decay (occupationKernel hn) (weightedOccupation φ w vb xy)
    Measurable.of_discrete 1
    (fun a => by simpa using weightedOccupation_per_step hn φ w d vb xy hw hstep a)
    t ((c₀, 0, 0), ⟨0, 0, 0, 0⟩)
  simpa [weightedOccupation, hzero] using h

end Ripple.PopulationProtocol.PopProto.Config
