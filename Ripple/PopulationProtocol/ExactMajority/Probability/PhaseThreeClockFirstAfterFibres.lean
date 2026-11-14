-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockFirstAfterFibres.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRows

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockFirstAfterFibres

open StageEventSpec PhaseThreeClockRows

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}
  (μ : Measure Ω) (ℱ : Filtration ℕ m₀)

theorem firstAfter_event_measurable (P : ℕ → Ω → Prop) (s u : ℕ)
    (hP : ∀ v, s ≤ v → MeasurableSet[ℱ v] {ω | P v ω}) :
    MeasurableSet[ℱ u] {ω | firstAfter (fun v => P v ω) s u} := by
  by_cases hsu : s ≤ u
  · have hprev : MeasurableSet[ℱ u]
        {ω | ∀ v, s ≤ v → v < u → ¬ P v ω} := by
      have hsets (v : ℕ) : MeasurableSet[ℱ u]
          {ω | s ≤ v → v < u → ¬ P v ω} := by
        by_cases hsv : s ≤ v
        · by_cases hvu : v < u
          · have hc := (((ℱ).mono hvu.le) _ (hP v hsv)).compl
            simpa only [hsv, hvu, true_implies, Set.compl_setOf] using hc
          · simp only [hvu, false_implies, implies_true,
              Set.setOf_true, MeasurableSet.univ]
        · simp only [hsv, false_implies, Set.setOf_true, MeasurableSet.univ]
      convert MeasurableSet.iInter hsets using 1
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    have heq : {ω | firstAfter (fun v => P v ω) s u} =
        {ω | P u ω} ∩ {ω | ∀ v, s ≤ v → v < u → ¬ P v ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, firstAfter, hsu, true_and]
    rw [heq]
    exact (hP u hsu).inter hprev
  · have heq : {ω | firstAfter (fun v => P v ω) s u} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, firstAfter, hsu, false_and, Set.mem_empty_iff_false]
    rw [heq]
    exact MeasurableSpace.measurableSet_empty _

theorem firstAfter_prefix_measurable (P : ℕ → Ω → Prop) (s u : ℕ)
    (E : Set Ω) (hE : MeasurableSet[ℱ s] E)
    (hP : ∀ v, s ≤ v → MeasurableSet[ℱ v] {ω | P v ω}) :
    MeasurableSet[ℱ u] (E ∩ {ω | firstAfter (fun v => P v ω) s u}) := by
  by_cases hsu : s ≤ u
  · exact (((ℱ).mono hsu) _ hE).inter
      (firstAfter_event_measurable ℱ P s u hP)
  · have heq : E ∩ {ω | firstAfter (fun v => P v ω) s u} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨-, hω⟩
      exact hsu hω.1
    rw [heq]
    exact MeasurableSpace.measurableSet_empty _

/-- A disjoint first-passage splice.  The endpoint events B u may depend
on the future; only the start fibres are used in conditional estimates. -/
theorem firstAfter_prefix_union (P : ℕ → Ω → Prop) (s : ℕ)
    (E : Set Ω) (hE : MeasurableSet[ℱ s] E)
    (hP : ∀ v, s ≤ v → MeasurableSet[ℱ v] {ω | P v ω})
    (B : ℕ → Set Ω) (epsilon : ℝ≥0∞)
    (hlocal : ∀ u,
      μ ((E ∩ {ω | firstAfter (fun v => P v ω) s u}) ∩ B u) ≤
        epsilon * μ (E ∩ {ω | firstAfter (fun v => P v ω) s u})) :
    μ (E ∩ {ω | ∃ u, firstAfter (fun v => P v ω) s u ∧ ω ∈ B u}) ≤
      epsilon * μ E := by
  let A : ℕ → Set Ω := fun u => E ∩ {ω | firstAfter (fun v => P v ω) s u}
  have hdisj : Pairwise (fun u v => Disjoint (A u) (A v)) := by
    intro u v huv
    apply Set.disjoint_left.mpr
    intro ω hu hv
    exact huv (firstAfter_unique (show firstAfter (fun w => P w ω) s u from hu.2)
      (show firstAfter (fun w => P w ω) s v from hv.2))
  have hmass : (∑' u, μ (A u)) ≤ μ E := by
    rw [← measure_iUnion hdisj (fun u =>
      ((ℱ).le u) _ (firstAfter_prefix_measurable ℱ P s u E hE hP))]
    apply measure_mono
    intro ω hω
    obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hω
    exact hu.1
  have hcover : E ∩ {ω | ∃ u, firstAfter (fun v => P v ω) s u ∧ ω ∈ B u} ⊆
      ⋃ u, A u ∩ B u := by
    rintro ω ⟨he, u, hu, hb⟩
    exact Set.mem_iUnion.mpr ⟨u, ⟨he, hu⟩, hb⟩
  calc
    _ ≤ μ (⋃ u, A u ∩ B u) := measure_mono hcover
    _ ≤ ∑' u, μ (A u ∩ B u) := measure_iUnion_le _
    _ ≤ ∑' u, epsilon * μ (A u) := ENNReal.tsum_le_tsum hlocal
    _ = epsilon * ∑' u, μ (A u) := by rw [ENNReal.tsum_mul_left]
    _ ≤ _ := mul_le_mul_left' hmass _

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockFirstAfterFibres

end
