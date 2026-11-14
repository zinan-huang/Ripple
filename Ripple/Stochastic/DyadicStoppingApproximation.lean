import Mathlib.Probability.Process.Stopping
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Dyadic approximation of nonnegative stopping times from above

Rounding upward to multiples of `2⁻ⁿ` preserves the stopping-time property.
For an arbitrary deterministic comparison time, its rounded stopping event is
an original stopping event at the lower dyadic cutoff. Finite stopping times
are approximated pointwise, and bounded stopping times take values in a finite
deterministic grid at each stage.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace Ripple.Stochastic.DyadicStoppingApproximation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {F : Filtration ℝ≥0 mΩ}

/-- The positive dyadic scale. -/
def dyadicScale (n : ℕ) : ℝ≥0 := (2 : ℝ≥0) ^ n

theorem dyadicScale_pos (n : ℕ) : 0 < dyadicScale n :=
  pow_pos (by norm_num) n

/-- The deterministic dyadic grid, including zero. -/
def dyadicGrid (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / dyadicScale n

/-- The integer index of the first dyadic grid point at or after the time. -/
def dyadicIndex (n : ℕ) (τ : Ω → ℝ≥0) (ω : Ω) : ℕ :=
  ⌈τ ω * dyadicScale n⌉₊

/-- Upward rounding of a finite nonnegative random time. -/
def dyadicStop (n : ℕ) (τ : Ω → ℝ≥0) (ω : Ω) : ℝ≥0 :=
  dyadicGrid n (dyadicIndex n τ ω)

/-- The last dyadic grid point at or before a deterministic time. -/
def dyadicCutoff (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  (⌊t * dyadicScale n⌋₊ : ℝ≥0) / dyadicScale n

/-- The lower cutoff never uses future information. -/
theorem dyadicCutoff_le (n : ℕ) (t : ℝ≥0) : dyadicCutoff n t ≤ t := by
  rw [dyadicCutoff, div_le_iff₀ (dyadicScale_pos n)]
  exact Nat.floor_le zero_le

/-- Exact comparison event for the rounded time. -/
theorem dyadicStop_le_iff (n : ℕ) (τ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    dyadicStop n τ ω ≤ t ↔ τ ω ≤ dyadicCutoff n t := by
  unfold dyadicStop dyadicGrid dyadicIndex dyadicCutoff
  rw [div_le_iff₀ (dyadicScale_pos n),
    ← Nat.le_floor_iff zero_le, Nat.ceil_le,
    le_div_iff₀ (dyadicScale_pos n)]

/-- Rounding upward preserves stopping times for an arbitrary filtration;
right-continuity is unnecessary. -/
theorem dyadicStop_isStoppingTime (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0))) (n : ℕ) :
    IsStoppingTime F (fun ω => (dyadicStop n τ ω : WithTop ℝ≥0)) := by
  intro t
  have heq : {ω | (dyadicStop n τ ω : WithTop ℝ≥0) ≤ t} =
      {ω | (τ ω : WithTop ℝ≥0) ≤ dyadicCutoff n t} := by
    ext ω
    simp only [Set.mem_setOf_eq, WithTop.coe_le_coe]
    exact dyadicStop_le_iff n τ t ω
  rw [heq]
  exact F.mono (dyadicCutoff_le n t) _ (hτ.measurableSet_le (dyadicCutoff n t))

/-- Upward rounding dominates the original time, including at zero. -/
theorem le_dyadicStop (n : ℕ) (τ : Ω → ℝ≥0) (ω : Ω) :
    τ ω ≤ dyadicStop n τ ω := by
  unfold dyadicStop dyadicGrid dyadicIndex
  rw [le_div_iff₀ (dyadicScale_pos n)]
  exact Nat.le_ceil _

/-- The rounding error is at most one grid width. -/
theorem dyadicStop_le_add_inv (n : ℕ) (τ : Ω → ℝ≥0) (ω : Ω) :
    dyadicStop n τ ω ≤ τ ω + (dyadicScale n)⁻¹ := by
  unfold dyadicStop dyadicGrid dyadicIndex
  calc
    (⌈τ ω * dyadicScale n⌉₊ : ℝ≥0) / dyadicScale n ≤
        (τ ω * dyadicScale n + 1) / dyadicScale n :=
      div_le_div_of_nonneg_right (Nat.ceil_lt_add_one zero_le).le zero_le
    _ = τ ω + (dyadicScale n)⁻¹ := by
      rw [add_div, mul_div_cancel_right₀ _ (ne_of_gt (dyadicScale_pos n)), one_div]

/-- Every finite time is the pointwise limit of its upper dyadic rounding. -/
theorem dyadicStop_tendsto (τ : Ω → ℝ≥0) (ω : Ω) :
    Tendsto (fun n => dyadicStop n τ ω) atTop (𝓝 (τ ω)) := by
  have hgeom : Tendsto (fun n => ((2 : ℝ≥0)⁻¹) ^ n) atTop (𝓝 0) :=
    NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have hupper : Tendsto (fun n => τ ω + (dyadicScale n)⁻¹) atTop (𝓝 (τ ω)) := by
    simpa only [dyadicScale, inv_pow, add_zero] using tendsto_const_nhds.add hgeom
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun n => le_dyadicStop n τ ω)
    (Eventually.of_forall fun n => dyadicStop_le_add_inv n τ ω)

/-- Grid points are strictly increasing in the integer index. -/
theorem dyadicGrid_strictMono (n : ℕ) : StrictMono (dyadicGrid n) := by
  intro i j hij
  apply div_lt_div_of_pos_right _ (dyadicScale_pos n)
  exact_mod_cast hij

@[simp] theorem dyadicGrid_zero (n : ℕ) : dyadicGrid n 0 = 0 := by
  simp [dyadicGrid]

@[simp] theorem dyadicStop_zero (n : ℕ) :
    dyadicStop n (fun _ : Ω => (0 : ℝ≥0)) = fun _ => 0 := by
  funext ω
  simp [dyadicStop, dyadicIndex, dyadicGrid]

/-- A deterministic upper bound gives an explicit finite bound on the index. -/
theorem dyadicIndex_le_of_le (n : ℕ) {τ : Ω → ℝ≥0} {T : ℝ≥0}
    (hτT : ∀ ω, τ ω ≤ T) (ω : Ω) :
    dyadicIndex n τ ω ≤ ⌈T * dyadicScale n⌉₊ := by
  exact Nat.ceil_mono (mul_le_mul_of_nonneg_right (hτT ω) zero_le)

/-- Each rounded stopping time lies in the advertised finite dyadic grid. -/
theorem dyadicStop_mem_grid (n : ℕ) {τ : Ω → ℝ≥0} {T : ℝ≥0}
    (hτT : ∀ ω, τ ω ≤ T) (ω : Ω) :
    ∃ k ≤ ⌈T * dyadicScale n⌉₊, dyadicStop n τ ω = dyadicGrid n k :=
  ⟨dyadicIndex n τ ω, dyadicIndex_le_of_le n hτT ω, rfl⟩

/-- The final grid point encloses the horizon; it need not equal the horizon. -/
theorem le_dyadicGrid_endpoint (n : ℕ) (T : ℝ≥0) :
    T ≤ dyadicGrid n ⌈T * dyadicScale n⌉₊ := by
  rw [dyadicGrid, le_div_iff₀ (dyadicScale_pos n)]
  exact Nat.le_ceil _

end Ripple.Stochastic.DyadicStoppingApproximation
