import Ripple.Stochastic.FilteredItoIntegralCLM
import Mathlib.Probability.Process.Stopping

/-!
# Stopping a predictable square-integrable integrand

The stochastic interval `(0, τ]` is predictable. Indeed, its complement above
zero is a countable union of generating predictable rectangles, using rational
cuts between `τ(ω)` and `t`. Restriction to this interval therefore acts on the
installed predictable L² space, without any continuity or boundedness premise.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Ripple.Stochastic.StoppedPredictableIntegrand

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}

/-- The stochastic interval with its zero-time fibre removed. -/
def stoppingRegion (τ : Ω → WithTop ℝ≥0) : Set (ℝ≥0 × Ω) :=
  {z | 0 < z.1 ∧ (z.1 : WithTop ℝ≥0) ≤ τ z.2}

/-- The strict epigraph of a stopping time is a countable union of predictable
rectangles. Rational cuts are clipped at zero only to obtain nonnegative times. -/
theorem afterStop_eq_iUnion :
    {z : ℝ≥0 × Ω | τ z.2 < (z.1 : WithTop ℝ≥0)} =
      ⋃ q : ℚ, Set.Ioi (Real.toNNReal (q : ℝ)) ×ˢ
        {ω | τ ω ≤ (Real.toNNReal (q : ℝ) : WithTop ℝ≥0)} := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_Ioi]
  constructor
  · intro hz
    cases he : τ z.2 with
    | top => simp [he] at hz
    | coe a =>
      have hat : a < z.1 := by
        simpa only [he, WithTop.coe_lt_coe] using hz
      obtain ⟨q, haq, hqt⟩ := exists_rat_btwn
        (show (a : ℝ) < (z.1 : ℝ) from by exact_mod_cast hat)
      have hqnonneg : 0 ≤ (q : ℝ) := a.coe_nonneg.trans haq.le
      have hcut : (Real.toNNReal (q : ℝ) : ℝ) = (q : ℝ) :=
        Real.coe_toNNReal _ hqnonneg
      have hcutlt : Real.toNNReal (q : ℝ) < z.1 := by
        exact_mod_cast (show (Real.toNNReal (q : ℝ) : ℝ) < (z.1 : ℝ) by
          rw [hcut]
          exact hqt)
      have hcutge : a ≤ Real.toNNReal (q : ℝ) := by
        exact_mod_cast (show (a : ℝ) ≤ (Real.toNNReal (q : ℝ) : ℝ) by
          rw [hcut]
          exact haq.le)
      exact ⟨q, hcutlt, by simpa only [he, WithTop.coe_le_coe] using hcutge⟩
  · rintro ⟨q, hqt, hτq⟩
    exact lt_of_le_of_lt hτq (WithTop.coe_lt_coe.mpr hqt)

/-- The strict epigraph is measurable for the exact predictable σ-algebra used
by the Itô extension. This does not require a right-continuous filtration. -/
theorem measurableSet_afterStop (hτ : IsStoppingTime F τ) :
    MeasurableSet[F.predictable]
      {z : ℝ≥0 × Ω | τ z.2 < (z.1 : WithTop ℝ≥0)} := by
  rw [afterStop_eq_iUnion]
  exact MeasurableSet.iUnion fun q =>
    measurableSet_predictable_Ioi_prod (hτ.measurableSet_le (Real.toNNReal (q : ℝ)))

/-- The interval `(0,τ]` is predictable, including for stopping times which
may be infinite. -/
theorem measurableSet_stoppingRegion (hτ : IsStoppingTime F τ) :
    MeasurableSet[F.predictable] (stoppingRegion τ) := by
  have heq : stoppingRegion τ =
      (Set.Ioi (0 : ℝ≥0) ×ˢ (Set.univ : Set Ω)) \
        {z : ℝ≥0 × Ω | τ z.2 < (z.1 : WithTop ℝ≥0)} := by
    ext z
    simp [stoppingRegion, not_lt]
  rw [heq]
  exact (measurableSet_predictable_Ioi_prod (𝓕 := F) (i := 0)
    MeasurableSet.univ).diff (measurableSet_afterStop hτ)

/-- Predictable square-integrability is preserved by stopping. The conclusion
uses the trimmed product measure itself, rather than ambient product measurability. -/
theorem memLp_stopped {ν : Measure ℝ≥0} {μ : Measure Ω}
    {H : ℝ≥0 × Ω → ℝ} (hτ : IsStoppingTime F τ)
    (hH : MemLp H 2 ((ν.prod μ).trim F.predictable_le_prod)) :
    MemLp ((stoppingRegion τ).indicator H) 2
      ((ν.prod μ).trim F.predictable_le_prod) :=
  hH.indicator (measurableSet_stoppingRegion hτ)

/-- The stopped integrand as an element of the installed predictable L² space
on a finite horizon. -/
noncomputable def stoppedIntegrand {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hτ : IsStoppingTime F τ)
    (φ : Lp ℝ 2 (FilteredItoIntegralCLM.trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    Lp ℝ 2 (FilteredItoIntegralCLM.trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) :=
  (memLp_stopped hτ (Lp.memLp φ)).toLp ((stoppingRegion τ).indicator φ)

/-- The selected L² representative agrees almost everywhere with
`φ(t,ω) 1_{0<t≤τ(ω)}`. -/
theorem stoppedIntegrand_coeFn {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hτ : IsStoppingTime F τ)
    (φ : Lp ℝ 2 (FilteredItoIntegralCLM.trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    (stoppedIntegrand T hBmeas hτ φ : ℝ≥0 × Ω → ℝ) =ᵐ[
      FilteredItoIntegralCLM.trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas]
      (stoppingRegion τ).indicator φ :=
  (memLp_stopped hτ (Lp.memLp φ)).coeFn_toLp

/-- An a.e. uniform bound is retained by the stopped L² class. -/
theorem stoppedIntegrand_bound {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hτ : IsStoppingTime F τ)
    (φ : Lp ℝ 2 (FilteredItoIntegralCLM.trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ᵐ z ∂FilteredItoIntegralCLM.trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas,
      |φ z| ≤ K) :
    ∀ᵐ z ∂FilteredItoIntegralCLM.trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas,
      |stoppedIntegrand T hBmeas hτ φ z| ≤ K := by
  classical
  filter_upwards [stoppedIntegrand_coeFn T hBmeas hτ φ, hφ] with z hz hb
  rw [hz, Set.indicator_apply]
  split_ifs
  · exact hb
  · simpa using hK

end Ripple.Stochastic.StoppedPredictableIntegrand
