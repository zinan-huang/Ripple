import Ripple.Stochastic.FilteredItoIntegralL2

/-!
# Square-root rate integrands and their clocks

The coefficient `sqrt (N * f (Z t))` has square `N * f (Z t)` even when
rates vanish. Continuous adapted paths give continuous adapted coefficients.
The integral clock is expressed using the same nonnegative-time Lebesgue
measure as the arbitrary-filtration Itô integral.

This module supplies deterministic coefficient facts. It does not construct a
stochastic integral, its quadratic variation, or an internal Brownian family.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Ripple.Kurtz.StrongApprox

variable {Ω State : Type*}

/-- The physical-time integrand for one rate channel. -/
noncomputable def kurtzClockIntegrand (N : ℕ) (f : State → ℝ)
    (Z : ℝ≥0 → Ω → State) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.sqrt ((N : ℝ) * f (Z t ω))

/-- The rate clock, with Lebesgue measure on `ℝ≥0` explicitly specified. -/
noncomputable def kurtzRateClock (N : ℕ) (f : State → ℝ)
    (Z : ℝ≥0 → Ω → State) (t : ℝ≥0) (ω : Ω) : ℝ :=
  (N : ℝ) * ∫ s in Set.Ioc 0 t, f (Z s ω) ∂ Ripple.Stochastic.FilteredItoIntegralL2.timeMeasure

/-- The square root never requires strict positivity of the rate. -/
theorem kurtzClockIntegrand_nonneg (N : ℕ) (f : State → ℝ)
    (Z : ℝ≥0 → Ω → State) (t : ℝ≥0) (ω : Ω) :
    0 ≤ kurtzClockIntegrand N f Z t ω :=
  Real.sqrt_nonneg _

/-- Nonnegative rates identify the squared coefficient exactly. -/
theorem kurtzClockIntegrand_sq (N : ℕ) {f : State → ℝ}
    (hf : ∀ x, 0 ≤ f x) (Z : ℝ≥0 → Ω → State)
    (t : ℝ≥0) (ω : Ω) :
    (kurtzClockIntegrand N f Z t ω) ^ 2 = (N : ℝ) * f (Z t ω) := by
  exact Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) (hf _))

/-- A uniform rate bound gives a uniform bound on the integrand. -/
theorem norm_kurtzClockIntegrand_le (N : ℕ) {f : State → ℝ} {ε : ℝ}
    (hf : ∀ x, f x ≤ ε) (Z : ℝ≥0 → Ω → State)
    (t : ℝ≥0) (ω : Ω) :
    ‖kurtzClockIntegrand N f Z t ω‖ ≤ Real.sqrt ((N : ℝ) * ε) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (kurtzClockIntegrand_nonneg N f Z t ω)]
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hf _) (Nat.cast_nonneg N))

/-- The squared coefficient inherits the rate bound with the correct scale. -/
theorem kurtzClockIntegrand_sq_le (N : ℕ) {f : State → ℝ} {ε : ℝ}
    (hf : ∀ x, 0 ≤ f x) (hb : ∀ x, f x ≤ ε)
    (Z : ℝ≥0 → Ω → State) (t : ℝ≥0) (ω : Ω) :
    (kurtzClockIntegrand N f Z t ω) ^ 2 ≤ (N : ℝ) * ε := by
  rw [kurtzClockIntegrand_sq N hf]
  exact mul_le_mul_of_nonneg_left (hb _) (Nat.cast_nonneg N)

section Continuity

variable [TopologicalSpace State]

/-- Composition with a continuous rate preserves path continuity. -/
theorem continuous_kurtzClockIntegrand (N : ℕ) {f : State → ℝ}
    (hf : Continuous f) {Z : ℝ≥0 → Ω → State} {ω : Ω}
    (hZ : Continuous (fun t => Z t ω)) :
    Continuous (fun t => kurtzClockIntegrand N f Z t ω) :=
  Real.continuous_sqrt.comp (continuous_const.mul (hf.comp hZ))

/-- Almost-everywhere continuous input paths give the same path regularity. -/
theorem ae_continuous_kurtzClockIntegrand [MeasurableSpace Ω]
    (μ : Measure Ω) (N : ℕ) {f : State → ℝ} (hf : Continuous f)
    {Z : ℝ≥0 → Ω → State}
    (hZ : ∀ᵐ ω ∂μ, Continuous (fun t => Z t ω)) :
    ∀ᵐ ω ∂μ, Continuous (fun t => kurtzClockIntegrand N f Z t ω) := by
  filter_upwards [hZ] with ω hω
  exact continuous_kurtzClockIntegrand N hf hω

/-- Each continuous squared coefficient is integrable on every finite horizon. -/
theorem integrableOn_kurtzClockIntegrand_sq (N : ℕ) {f : State → ℝ}
    (hf : Continuous f) {Z : ℝ≥0 → Ω → State} {ω : Ω}
    (hZ : Continuous (fun t => Z t ω)) (T : ℝ≥0) :
    IntegrableOn (fun s => (kurtzClockIntegrand N f Z s ω) ^ 2)
      (Set.Ioc 0 T) Ripple.Stochastic.FilteredItoIntegralL2.timeMeasure := by
  have hc := (continuous_kurtzClockIntegrand N hf hZ).pow 2
  exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set
    (fun _ h => ⟨h.1.le, h.2⟩)

end Continuity

section Adaptedness

variable [MeasurableSpace Ω] [TopologicalSpace State] [MeasurableSpace State]
  [BorelSpace State]

/-- The coefficient uses only the current adapted state. -/
theorem adapted_kurtzClockIntegrand {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (N : ℕ) {f : State → ℝ} (hf : Continuous f)
    {Z : ℝ≥0 → Ω → State} (hZ : Adapted F Z) :
    Adapted F (kurtzClockIntegrand N f Z) := by
  intro t
  exact Real.continuous_sqrt.measurable.comp
    (measurable_const.mul (hf.measurable.comp (hZ t)))

/-- Real-valued adapted coefficients are also strongly adapted. -/
theorem stronglyAdapted_kurtzClockIntegrand
    {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (N : ℕ) {f : State → ℝ} (hf : Continuous f)
    {Z : ℝ≥0 → Ω → State} (hZ : Adapted F Z) :
    StronglyAdapted F (kurtzClockIntegrand N f Z) := by
  intro t
  exact (adapted_kurtzClockIntegrand N hf hZ t).stronglyMeasurable

end Adaptedness

/-- The integral of the squared coefficient is exactly the Kurtz rate clock.
No stochastic bracket identification is assumed or asserted here. -/
theorem integral_kurtzClockIntegrand_sq (N : ℕ) {f : State → ℝ}
    (hf : ∀ x, 0 ≤ f x) (Z : ℝ≥0 → Ω → State)
    (t : ℝ≥0) (ω : Ω) :
    (∫ s in Set.Ioc 0 t, (kurtzClockIntegrand N f Z s ω) ^ 2 ∂ Ripple.Stochastic.FilteredItoIntegralL2.timeMeasure) =
      kurtzRateClock N f Z t ω := by
  simp_rw [kurtzClockIntegrand_sq N hf]
  exact integral_const_mul _ _

end Ripple.Kurtz.StrongApprox
