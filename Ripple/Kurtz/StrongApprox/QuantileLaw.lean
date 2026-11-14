/-
  Ripple.Kurtz.StrongApprox.QuantileLaw — the law of the generalized inverse under a uniform input

  If `U : Ω → ℝ` has `P{U ≤ t} = t` for `t ∈ [0,1]` (a uniform input, e.g. `U = Φ ∘ Z`), `F` is a
  monotone cdf on `ℕ` with values in `[0,1]` reaching every value of `U`, then
  `{natQuantile F (U ω) ≤ k} = {U ω ≤ F k}` pointwise, hence `P{natQuantile F U ≤ k} = F k` and
  `P{natQuantile F U = k} = F k − F (k−1)`: the generalized inverse has cdf `F`.
-/

import Mathlib
import Ripple.Kurtz.StrongApprox.QuantileCoupling

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory Set

/-- Pointwise: `natQuantile F u ≤ k ↔ u ≤ F k` for monotone `F` reaching `u`. -/
theorem natQuantile_le_iff {F : ℕ → ℝ} (hF : Monotone F) {u : ℝ} (hex : ∃ k, u ≤ F k) (k : ℕ) :
    natQuantile F u ≤ k ↔ u ≤ F k := by
  constructor
  · intro h
    exact (le_apply_natQuantile hex).trans (hF h)
  · intro h
    exact natQuantile_le_of_le h

/-- The set `{natQuantile F (U ω) ≤ k}` is the set `{U ω ≤ F k}`. -/
theorem setOf_natQuantile_le {Ω : Type*} {F : ℕ → ℝ} (hF : Monotone F) {U : Ω → ℝ}
    (hex : ∀ ω, ∃ k, U ω ≤ F k) (k : ℕ) :
    {ω | natQuantile F (U ω) ≤ k} = {ω | U ω ≤ F k} := by
  ext ω
  exact natQuantile_le_iff hF (hex ω) k

/-- Law of the generalized inverse: if `P{U ≤ t} = t` on `[0,1]` and `F k ∈ [0,1]`, then
`P{natQuantile F U ≤ k} = F k`. -/
theorem measure_natQuantile_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {F : ℕ → ℝ} (hF : Monotone F) (hF0 : ∀ k, 0 ≤ F k) (hF1 : ∀ k, F k ≤ 1)
    {U : Ω → ℝ} (hex : ∀ ω, ∃ k, U ω ≤ F k)
    (hU : ∀ t, 0 ≤ t → t ≤ 1 → P {ω | U ω ≤ t} = ENNReal.ofReal t) (k : ℕ) :
    P {ω | natQuantile F (U ω) ≤ k} = ENNReal.ofReal (F k) := by
  rw [setOf_natQuantile_le hF hex k]
  exact hU (F k) (hF0 k) (hF1 k)

/-- Point masses of the generalized inverse: `P{natQuantile F U = k+1} = F (k+1) − F k`
(as a difference of `ENNReal.ofReal`s, i.e. `ofReal (F (k+1)) − ofReal (F k)`), and
`P{natQuantile F U = 0} = F 0`. -/
theorem measure_natQuantile_eq_succ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P]
    {F : ℕ → ℝ} (hF : Monotone F) (hF0 : ∀ k, 0 ≤ F k) (hF1 : ∀ k, F k ≤ 1)
    {U : Ω → ℝ} (hU_meas : Measurable U) (hex : ∀ ω, ∃ k, U ω ≤ F k)
    (hU : ∀ t, 0 ≤ t → t ≤ 1 → P {ω | U ω ≤ t} = ENNReal.ofReal t) (k : ℕ) :
    P {ω | natQuantile F (U ω) = k + 1} = ENNReal.ofReal (F (k + 1)) - ENNReal.ofReal (F k) := by
  have hset : {ω | natQuantile F (U ω) = k + 1} =
      {ω | natQuantile F (U ω) ≤ k + 1} \ {ω | natQuantile F (U ω) ≤ k} := by
    ext ω; simp only [mem_setOf_eq, mem_diff, not_le]; omega
  have hsub : {ω | natQuantile F (U ω) ≤ k} ⊆ {ω | natQuantile F (U ω) ≤ k + 1} :=
    fun ω h => Nat.le_succ_of_le h
  have hmeas : MeasurableSet {ω | natQuantile F (U ω) ≤ k} := by
    rw [setOf_natQuantile_le hF hex k]
    exact hU_meas measurableSet_Iic
  rw [hset, measure_diff hsub hmeas.nullMeasurableSet (measure_ne_top _ _),
    measure_natQuantile_le P hF hF0 hF1 hex hU, measure_natQuantile_le P hF hF0 hF1 hex hU]

theorem measure_natQuantile_eq_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {F : ℕ → ℝ} (hF : Monotone F) (hF0 : ∀ k, 0 ≤ F k) (hF1 : ∀ k, F k ≤ 1)
    {U : Ω → ℝ} (hex : ∀ ω, ∃ k, U ω ≤ F k)
    (hU : ∀ t, 0 ≤ t → t ≤ 1 → P {ω | U ω ≤ t} = ENNReal.ofReal t) :
    P {ω | natQuantile F (U ω) = 0} = ENNReal.ofReal (F 0) := by
  have : {ω | natQuantile F (U ω) = 0} = {ω | natQuantile F (U ω) ≤ 0} := by
    ext ω; simp
  rw [this]
  exact measure_natQuantile_le P hF hF0 hF1 hex hU 0

end Ripple.Kurtz.StrongApprox
