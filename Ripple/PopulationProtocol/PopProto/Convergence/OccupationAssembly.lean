import Ripple.PopulationProtocol.PopProto.Convergence.CornerCharge

/-! # The occupation clock and original-chain marginal
Cumulative region visits equal elapsed time on every non-consensus trajectory.
This is a path invariant, not a bound on fixed-time regional occupancy.
-/
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Ripple.PopulationProtocol.PopProto.Config
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

/-- Total interactions recorded in the four active regions. -/
def RegionCounts.total (s : RegionCounts) : ℕ := s.central + s.blank + s.left + s.right

/-- A non-consensus opinionated configuration belongs to exactly one active
region, so recording it adds precisely one interaction. -/
theorem RegionCounts.record_total (s : RegionCounts) (c : Config n) (hn : n ≥ 2)
    (hop : c.hasOpinion) (hnot : ¬c.isConsensus) :
    (s.record c).total = s.total + 1 := by
  have hv : c.v ≥ 1 := hop
  have hby : c.b_count + c.y_count ≥ 1 := by
    by_contra h
    apply hnot
    left
    unfold allX
    have := c.sum_eq
    omega
  have hbx : c.b_count + c.x_count ≥ 1 := by
    by_contra h
    apply hnot
    right
    unfold allY
    have := c.sum_eq
    omega
  have hd := at_most_one_large c hn
  rcases region_classification c hn with hc | hb | hx | hy
  · have hh := hc
    unfold inCentral at hh
    simp [RegionCounts.record, RegionCounts.total, activeCentral, activeLargeB,
      activeLargeX, activeLargeY, hc, hh.1, hh.2.1, hh.2.2, hv]
    omega
  · have hx : ¬c.inLargeX := fun h => hd.1 ⟨hb, h⟩
    have hy : ¬c.inLargeY := fun h => hd.2.1 ⟨hb, h⟩
    have hc : ¬c.inCentral := fun h => h.1 hb
    simp [RegionCounts.record, RegionCounts.total, activeCentral, activeLargeB,
      activeLargeX, activeLargeY, hb, hx, hy, hc, hv]
    omega
  · have hb : ¬c.inLargeB := fun h => hd.1 ⟨h, hx⟩
    have hy : ¬c.inLargeY := fun h => hd.2.2 ⟨hx, h⟩
    have hc : ¬c.inCentral := fun h => h.2.1 hx
    simp [RegionCounts.record, RegionCounts.total, activeCentral, activeLargeB,
      activeLargeX, activeLargeY, hx, hb, hy, hc, hby]
    omega
  · have hb : ¬c.inLargeB := fun h => hd.2.1 ⟨h, hy⟩
    have hx : ¬c.inLargeX := fun h => hd.2.2 ⟨h, hy⟩
    have hc : ¬c.inCentral := fun h => h.2.2 hy
    simp [RegionCounts.record, RegionCounts.total, activeCentral, activeLargeB,
      activeLargeX, activeLargeY, hy, hb, hx, hc, hbx]
    omega

/-- Any predicate true after every possible sampled interaction holds almost
surely after one occupation-chain step. -/
theorem occupationKernel_ae_of_step (hn : n ≥ 2) (a : OccupationConfig n)
    (P : OccupationConfig n → Prop)
    (hP : ∀ q : State × State,
      P (augStep a.1.1 a.1.2.1 a.1.2.2 q.1 q.2, a.2.record a.1.1)) :
    ∀ᵐ b ∂(occupationKernel hn a), P b := by
  change ∀ᵐ b ∂(occupationStepDist hn a).toMeasure, P b
  unfold occupationStepDist
  rw [← PMF.toMeasure_map _ _ Measurable.of_discrete,
    ae_map_iff Measurable.of_discrete.aemeasurable
      (DiscreteMeasurableSpace.forall_measurableSet _)]
  unfold augStepDist
  rw [← PMF.toMeasure_map _ _ Measurable.of_discrete,
    ae_map_iff Measurable.of_discrete.aemeasurable
      (DiscreteMeasurableSpace.forall_measurableSet _)]
  exact ae_of_all _ hP

/-- At time t, every non-consensus original trajectory has recorded exactly
t region visits. Consensus trajectories cannot restart. -/
theorem occupation_clock (hn : n ≥ 2) (c₀ : Config n) (hop : c₀.hasOpinion) (t : ℕ) :
    ∀ᵐ a ∂((occupationKernel hn ^ t) ((c₀, 0, 0), ⟨0, 0, 0, 0⟩)),
      a.1.1.hasOpinion ∧ (¬a.1.1.isConsensus → a.2.total = t) := by
  induction t with
  | zero =>
    simp only [pow_zero]
    change ∀ᵐ a ∂(Kernel.id (((c₀, 0, 0), ⟨0, 0, 0, 0⟩) : OccupationConfig n)), _
    rw [Kernel.id_apply, ae_dirac_iff (DiscreteMeasurableSpace.forall_measurableSet _)]
    exact ⟨hop, fun _ => rfl⟩
  | succ t ih =>
    rw [ae_iff]
    have hm : MeasurableSet {a : OccupationConfig n |
        ¬(a.1.1.hasOpinion ∧ (¬a.1.1.isConsensus → a.2.total = t + 1))} :=
      DiscreteMeasurableSpace.forall_measurableSet _
    rw [Kernel.pow_succ_apply_eq_lintegral _ _ _ hm,
      lintegral_eq_zero_iff (Kernel.measurable_coe _ hm)]
    filter_upwards [ih] with a ha
    change _ = (0 : ℝ≥0∞)
    rw [← ae_iff]
    apply occupationKernel_ae_of_step
    intro ⟨i, r⟩
    constructor
    · exact hasOpinion_stepOrSelf a.1.1 i r ha.1
    · intro hnot
      have hprev : ¬a.1.1.isConsensus := by
        intro hc
        rcases hc with hx | hy
        · apply hnot
          change (a.1.1.stepOrSelf i r).isConsensus
          rw [allX_step_eq a.1.1 hx]
          exact Or.inl hx
        · apply hnot
          change (a.1.1.stepOrSelf i r).isConsensus
          rw [allY_step_eq a.1.1 hy]
          exact Or.inr hy
      change (a.2.record a.1.1).total = t + 1
      rw [RegionCounts.record_total a.2 a.1.1 hn ha.1 hprev, ha.2 hprev]

/-- The occupation counters leave the original augmented one-step marginal unchanged. -/
theorem occupationKernel_proj_step (hn : n ≥ 2) (a : OccupationConfig n)
    (S : Set (AugConfig n)) (hS : MeasurableSet S) :
    occupationKernel hn a (Prod.fst ⁻¹' S) = augTransitionKernel hn a.1 S := by
  change (occupationStepDist hn a).toMeasure (Prod.fst ⁻¹' S) =
    (augStepDist a.1 hn).toMeasure S
  unfold occupationStepDist
  rw [PMF.toMeasure_map_apply _ _ _ Measurable.of_discrete
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  rfl

/-- The entire finite-time augmented marginal is unchanged by recording occupations. -/
theorem occupationKernel_proj_pow (hn : n ≥ 2) (a₀ : OccupationConfig n) (t : ℕ)
    (S : Set (AugConfig n)) (hS : MeasurableSet S) :
    ((occupationKernel hn ^ t) a₀) (Prod.fst ⁻¹' S) =
      ((augTransitionKernel hn ^ t) a₀.1) S := by
  induction t generalizing S with
  | zero =>
    simp only [pow_zero]
    change Kernel.id a₀ _ = Kernel.id a₀.1 _
    rw [Kernel.id_apply, Kernel.id_apply,
      Measure.dirac_apply' a₀ (DiscreteMeasurableSpace.forall_measurableSet _),
      Measure.dirac_apply' a₀.1 hS]
    simp only [Set.indicator, Set.mem_preimage]
    split <;> rfl
  | succ t ih =>
    rw [Kernel.pow_succ_apply_eq_lintegral _ _ _
      (DiscreteMeasurableSpace.forall_measurableSet _),
      Kernel.pow_succ_apply_eq_lintegral _ _ _ hS]
    simp_rw [occupationKernel_proj_step hn _ S hS]
    rw [← lintegral_map (Kernel.measurable_coe _ hS) Measurable.of_discrete]
    congr 1
    exact Measure.ext (fun S' hS' => by
      rw [Measure.map_apply Measurable.of_discrete hS']
      exact ih S' hS')

end Ripple.PopulationProtocol.PopProto.Config
