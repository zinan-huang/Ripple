import Ripple.Kurtz.StrongApprox.KurtzClockAdapter
import Ripple.Stochastic.ContinuousAdaptedIntegrand
import Ripple.Stochastic.ContinuousItoHalfLineLinear
import Ripple.Stochastic.ContinuousItoLinear

/-!
# The actual Kurtz integrand in the predictable integral domain

The bound may depend on the population size and channel. No uniform bound in
the population size is required for local square integrability. The half-line
integral agrees with `continuousItoOfFun` on each finite horizon on one event
for every time in that horizon.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Ripple.Kurtz.StrongApprox
open Ripple.Stochastic
open FilteredItoIntegralCLM ContinuousItoConsistency ContinuousItoLinear ContinuousItoHalfLineLinear

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
  {B : ℝ≥0 → Ω → ℝ}

/-- The square-root rate coefficient is strongly predictable, obtained from
its actual adapted continuous state path. -/
theorem stronglyMeasurable_kurtzClockIntegrand
    (N : ℕ) {f : (Fin d → ℝ) → ℝ} (hf : Continuous f)
    {Z : ℝ≥0 → Ω → Fin d → ℝ} (ha : Adapted F Z)
    (hc : ∀ ω, Continuous (fun t => Z t ω)) :
    StronglyMeasurable[F.predictable] (Function.uncurry (kurtzClockIntegrand N f Z)) :=
  ContinuousAdaptedIntegrand.stronglyMeasurable_uncurry
    (adapted_kurtzClockIntegrand N hf ha)
    (fun ω => continuous_kurtzClockIntegrand N hf (hc ω))

/-- A bounded rate supplies membership in the installed trimmed predictable
L² space on every finite horizon. -/
theorem memLp_kurtzClockIntegrand
    (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (N : ℕ) {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) {eps : ℝ}
    (hb : ∀ x, f x ≤ eps) {Z : ℝ≥0 → Ω → Fin d → ℝ}
    (ha : Adapted F Z) (hc : ∀ ω, Continuous (fun t => Z t ω)) :
    MemLp (Function.uncurry (kurtzClockIntegrand N f Z)) 2
      (trimMeasure_T (𝓖 := F) (μ := P) T hBmeas) := by
  apply ContinuousAdaptedIntegrand.integrandMemLp T hBmeas
    (kurtzClockIntegrand N f Z) (adapted_kurtzClockIntegrand N hf ha)
    (fun ω => continuous_kurtzClockIntegrand N hf (hc ω)) (Real.sqrt ((N : ℝ) * eps))
  intro t ω
  simpa only [Real.norm_eq_abs] using norm_kurtzClockIntegrand_le N hb Z t ω

/-- The nonnegative clock expected by the inverse-clock construction. -/
def kurtzRateClockNN (N : ℕ) (f : (Fin d → ℝ) → ℝ)
    (Z : ℝ≥0 → Ω → Fin d → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (kurtzRateClock N f Z t ω).toNNReal

theorem kurtzRateClock_nonneg (N : ℕ) {f : (Fin d → ℝ) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (Z : ℝ≥0 → Ω → Fin d → ℝ) (t : ℝ≥0) (ω : Ω) :
    0 ≤ kurtzRateClock N f Z t ω := by
  unfold kurtzRateClock
  exact mul_nonneg (Nat.cast_nonneg N) (integral_nonneg fun s => hf (Z s ω))

theorem integral_kurtzClockIntegrand_sq_eq_nn (N : ℕ) {f : (Fin d → ℝ) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (Z : ℝ≥0 → Ω → Fin d → ℝ) (t : ℝ≥0) (ω : Ω) :
    (∫ s in Ioc 0 t, (kurtzClockIntegrand N f Z s ω) ^ 2
      ∂FilteredItoIntegralL2.timeMeasure) = (kurtzRateClockNN N f Z t ω : ℝ) := by
  rw [integral_kurtzClockIntegrand_sq N hf]
  exact (Real.coe_toNNReal _ (kurtzRateClock_nonneg N hf Z t ω)).symm

section IntegralAgreement
variable [IsFilteredPreBrownian B F P]

/-- Concrete specialization for the Kurtz integrand. All predictable L²
membership obligations are discharged from the bounded continuous rate. -/
theorem kurtz_halfLineIto_eq_continuousItoOfFun
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (N : ℕ) {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) {eps : ℝ}
    (hb : ∀ x, f x ≤ eps) {Z : ℝ≥0 → Ω → Fin d → ℝ}
    (ha : Adapted F Z) (hc : ∀ ω, Continuous (fun t => Z t ω)) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ t ≤ T,
      halfLineIto hB hBmeas (Function.uncurry (kurtzClockIntegrand N f Z))
        (fun n => memLp_kurtzClockIntegrand (P := P) hBmeas n N hf hb ha hc) t ω =
      continuousItoOfFun P F T hB hBmeas (kurtzClockIntegrand N f Z) t ω :=
  halfLineIto_eq_continuousItoOfFun hB hBmeas (kurtzClockIntegrand N f Z)
    (fun n => memLp_kurtzClockIntegrand (P := P) hBmeas n N hf hb ha hc) T
    (memLp_kurtzClockIntegrand (P := P) hBmeas T N hf hb ha hc)

end IntegralAgreement
end Ripple.Kurtz.StrongApprox
