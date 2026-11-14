import Ripple.Stochastic.KnightCompletionGrid
import Ripple.Stochastic.KnightTerminalValue
import Ripple.Stochastic.ClockInverseStopping
import Ripple.Stochastic.ContinuousItoHalfLineLinear

/-!
# Measurability of inverse-clock and terminal evaluations

The extended stopping time is evaluated only on its finite branch. On the
other branch the original contribution is the measurable terminal value.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Ripple.Stochastic.Knight
open Ripple.Analysis Ripple.ProbabilityTheory

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {F : Filtration ℝ≥0 mΩ}
  [F.IsRightContinuous]

/-- The total raw inverse evaluation is measurable whenever the original
process is jointly measurable. The value at an infinite inverse is explicitly
reset to its defining zero-time value. -/
theorem measurable_rawTimeChangePath
    {M : ℝ≥0 → Ω → ℝ} (hM : Measurable (Function.uncurry M))
    {A : ℝ≥0 → Ω → ℝ≥0} (ha : Adapted F A)
    (hc : ∀ ω, Continuous (fun t => A t ω))
    (hm : ∀ ω, Monotone (fun t => A t ω)) (hz : ∀ ω, A 0 ω = 0)
    (u : ℝ≥0) :
    Measurable (fun ω => rawTimeChangePath (fun t => M t ω) (fun t => A t ω) u) := by
  classical
  let τ := clockInverseTime A u
  have hτ := clockInverseTime_isStoppingTime ha hc hm hz u
  have hmτ := hτ.measurable'
  have ht : Measurable (fun ω => if τ ω = ⊤ then (0 : ℝ≥0) else (τ ω).untopA) :=
    Measurable.ite (measurableSet_eq_fun hmτ measurable_const) measurable_const hmτ.untopA
  have heq : (fun ω => rawTimeChangePath (fun t => M t ω) (fun t => A t ω) u) =
      fun ω => M (if τ ω = ⊤ then 0 else (τ ω).untopA) ω := by
    funext ω
    by_cases hf : clockInverse (fun t => A t ω) u = ⊤
    · simp [rawTimeChangePath, τ, clockInverseTime, hf]
    · have hτω : τ ω = ((clockInverse (fun t => A t ω) u).toNNReal : WithTop ℝ≥0) := by
        simp only [τ, clockInverseTime, if_neg hf]
      have hne : ¬ τ ω = ⊤ := by rw [hτω]; exact WithTop.coe_ne_top
      unfold rawTimeChangePath
      rw [if_neg hne, hτω, WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  rw [heq]
  exact hM.comp (ht.prodMk measurable_id)

/-- Measurability of the original contribution used by finite-clock
completion, including the seam itself. -/
theorem measurable_terminalOriginalPath
    {M : ℝ≥0 → Ω → ℝ} (hM : Measurable (Function.uncurry M))
    {A : ℝ≥0 → Ω → ℝ≥0} (ha : Adapted F A)
    (hc : ∀ ω, Continuous (fun t => A t ω))
    (hm : ∀ ω, Monotone (fun t => A t ω)) (hz : ∀ ω, A 0 ω = 0)
    {L : Ω → ℝ} (hL : Measurable L) (u : ℝ≥0) :
    Measurable (fun ω => terminalOriginalPath (fun t => M t ω) (fun t => A t ω) (L ω) u) := by
  classical
  have hterm := measurable_terminalClock (fun t => (ha t).mono (F.le t) le_rfl) hm
  exact Measurable.ite (measurableSet_lt measurable_const hterm)
    (measurable_rawTimeChangePath hM ha hc hm hz u) hL

end Ripple.Stochastic.Knight
