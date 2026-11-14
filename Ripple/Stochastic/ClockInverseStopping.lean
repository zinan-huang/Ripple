import Ripple.Analysis.ClockInverse
import Mathlib.Probability.Process.Stopping

/-!
# Inverse stopping times of adapted continuous clocks

Adapted continuous clocks and their inverse stopping times. Regularity is pathwise:
almost-everywhere regularity needs a completed filtration or a separately constructed
adapted good modification.
-/

open Set MeasureTheory
open scoped NNReal ENNReal

namespace Ripple.Stochastic

open Ripple.Analysis

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Explicit conversion to the extended-time owner used by Mathlib stopping times. -/
noncomputable def clockInverseTime (A : ℝ≥0 → Ω → ℝ≥0) (u : ℝ≥0)
    (ω : Ω) : WithTop ℝ≥0 :=
  if clockInverse (fun t => A t ω) u = ⊤ then ⊤
  else ((clockInverse (fun t => A t ω) u).toNNReal : WithTop ℝ≥0)

/-- Strict inverse-time events depend only on the current clock value. -/
theorem clockInverseTime_lt_iff {A : ℝ≥0 → Ω → ℝ≥0}
    (hc : ∀ ω, Continuous (fun t => A t ω))
    (hm : ∀ ω, Monotone (fun t => A t ω)) (hzero : ∀ ω, A 0 ω = 0)
    (u t : ℝ≥0) (ω : Ω) : clockInverseTime A u ω < t ↔ u < A t ω := by
  by_cases hf : clockInverse (fun s => A s ω) u = ⊤
  · simp only [clockInverseTime, if_pos hf, not_top_lt, false_iff]
    intro ht
    have hlt := (clockInverse_lt_iff (hc ω) (hm ω) (hzero ω) u t).mpr ht
    simpa [hf] using hlt
  · rw [clockInverseTime, if_neg hf, WithTop.coe_lt_coe]
    have he : ((clockInverse (fun s => A s ω) u).toNNReal : ℝ≥0∞) =
        clockInverse (fun s => A s ω) u := ENNReal.coe_toNNReal hf
    have hcast : (clockInverse (fun s => A s ω) u).toNNReal < t ↔
        clockInverse (fun s => A s ω) u < (t : ℝ≥0∞) := by
      rw [← ENNReal.coe_lt_coe, he]
    exact hcast.trans (clockInverse_lt_iff (hc ω) (hm ω) (hzero ω) u t)

/-- A right-continuous filtration suffices; completeness is unnecessary for
an everywhere continuous nondecreasing adapted clock starting at zero. -/
theorem clockInverseTime_isStoppingTime {F : Filtration ℝ≥0 mΩ}
    [F.IsRightContinuous] {A : ℝ≥0 → Ω → ℝ≥0} (ha : Adapted F A)
    (hc : ∀ ω, Continuous (fun t => A t ω))
    (hm : ∀ ω, Monotone (fun t => A t ω)) (hzero : ∀ ω, A 0 ω = 0)
    (u : ℝ≥0) : IsStoppingTime F (clockInverseTime A u) := by
  apply isStoppingTime_of_measurableSet_lt_of_isRightContinuous
  intro t
  have he : {ω | clockInverseTime A u ω < t} = {ω | u < A t ω} := by
    ext ω
    exact clockInverseTime_lt_iff hc hm hzero u t ω
  rw [he]
  exact (ha t) measurableSet_Ioi

end Ripple.Stochastic
