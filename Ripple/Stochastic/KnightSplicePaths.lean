import Ripple.Stochastic.KnightTimeChangePaths
import Mathlib.Tactic.Linarith

/-!
# Deterministic compactification and the post-seam inverse

Physical time is compressed into `[0,1)` by `r / (1-r)`. At time one the
clock is spliced to a clock of unit speed and the path to an auxiliary path.
For every internal level at least the terminal level, the strict inverse is
exactly `1 + (u-a)`, including equality and the case `a = 0`.

Only boundedness of the original clock is needed for this inverse formula.
Monotonicity and convergence to a finite terminal clock supply that bound.
The continuity of the whole splice, its martingale property, and its bracket
identification are separate obligations. No stochastic conclusion is assumed.
-/

open Set Filter
open scoped NNReal ENNReal Topology

namespace Ripple.ProbabilityTheory

open Ripple.Analysis

/-- The physical-time map used on the open side of the seam. Its total value
at or above one is irrelevant to the splice. -/
noncomputable def compactificationTime (r : ℝ≥0) : ℝ≥0 := r / (1 - r)

/-- Compactify the old clock before one, then append a unit-speed clock. -/
noncomputable def splicedClock (A : ℝ≥0 → ℝ≥0) (a r : ℝ≥0) : ℝ≥0 :=
  if r < 1 then A (compactificationTime r) else a + (r - 1)

/-- Compactify the old path before one, then append the auxiliary path to its
terminal value. Continuity at the seam needs convergence and `W 0 = 0`. -/
noncomputable def splicedPath (M : ℝ≥0 → ℝ) (m : ℝ) (W : ℝ≥0 → ℝ)
    (r : ℝ≥0) : ℝ :=
  if r < 1 then M (compactificationTime r) else m + W (r - 1)

/-- The appended unit-speed clock diverges, regardless of the original clock.
This is the deterministic unbounded-clock input for the splice construction. -/
theorem splicedClock_tendsto_atTop (A : ℝ≥0 → ℝ≥0) (a : ℝ≥0) :
    Tendsto (splicedClock A a) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_ge_atTop (1 + b)] with r hr
  have hrone : (1 : ℝ≥0) ≤ r :=
    (le_add_of_nonneg_right (bot_le : (0 : ℝ≥0) ≤ b)).trans hr
  rw [splicedClock, if_neg (not_lt_of_ge hrone)]
  have hrreal : (1 : ℝ) + (b : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hsub : ((r - 1 : ℝ≥0) : ℝ) = (r : ℝ) - 1 := by
    simpa using NNReal.coe_sub hrone
  have ha : (0 : ℝ) ≤ (a : ℝ) := a.coe_nonneg
  have hresult : (b : ℝ) ≤ (a : ℝ) + ((r - 1 : ℝ≥0) : ℝ) := by linarith
  exact_mod_cast hresult

/-- A monotone clock converging to a finite level never exceeds that level. -/
theorem clock_le_of_monotone_tendsto
    {A : ℝ≥0 → ℝ≥0} {a : ℝ≥0} (hm : Monotone A)
    (hlim : Tendsto A atTop (𝓝 a)) (t : ℝ≥0) : A t ≤ a := by
  refine le_of_tendsto_of_tendsto
    (tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 => A t) atTop (𝓝 (A t)))
    hlim ?_
  filter_upwards [eventually_ge_atTop t] with s hs
  exact hm hs

/-- A strict crossing characterization determines the installed extended-valued
inverse. This uses a right-neighborhood limit, without requiring continuity of
the clock itself. -/
theorem clockInverse_eq_of_crossing_iff
    {A : ℝ≥0 → ℝ≥0} {u R : ℝ≥0}
    (hcross : ∀ r, u < A r ↔ R < r) : clockInverse A u = (R : ℝ≥0∞) := by
  apply le_antisymm
  · have hcoe : Tendsto (fun r : ℝ≥0 => (r : ℝ≥0∞)) (𝓝[>] R)
        (𝓝 (R : ℝ≥0∞)) := by
      exact (show Continuous (fun r : ℝ≥0 => (r : ℝ≥0∞)) by
        fun_prop).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto_of_tendsto
      (tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 => clockInverse A u)
        (𝓝[>] R) (𝓝 (clockInverse A u))) hcoe ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact clockInverse_le_of_lt ((hcross r).mpr hr)
  · change (R : ℝ≥0∞) ≤ ⨅ r : ℝ≥0, ⨅ (_ : u < A r), (r : ℝ≥0∞)
    refine le_iInf fun r => le_iInf fun hr => ?_
    exact_mod_cast ((hcross r).mp hr).le

/-- Above the terminal level no pre-seam crossing is possible; the post-seam
strict crossing occurs precisely after `1 + (u-a)`. -/
theorem splicedClock_crossing_iff
    {A : ℝ≥0 → ℝ≥0} {a u : ℝ≥0} (hbound : ∀ t, A t ≤ a)
    (hu : a ≤ u) (r : ℝ≥0) :
    u < splicedClock A a r ↔ 1 + (u - a) < r := by
  by_cases hr : r < 1
  · have hleft : ¬ u < splicedClock A a r := by
      rw [splicedClock, if_pos hr]
      exact not_lt_of_ge ((hbound _).trans hu)
    have hright : ¬ 1 + (u - a) < r := by
      have hnonneg : (0 : ℝ≥0) ≤ u - a := bot_le
      intro h
      have hone : (1 : ℝ≥0) ≤ 1 + (u - a) := le_add_of_nonneg_right hnonneg
      exact (not_lt_of_ge hone) (h.trans hr)
    exact iff_of_false hleft hright
  · have hrle : (1 : ℝ≥0) ≤ r := le_of_not_gt hr
    rw [splicedClock, if_neg hr]
    have hsub : ((u - a : ℝ≥0) : ℝ) = (u : ℝ) - (a : ℝ) := NNReal.coe_sub hu
    have hrsub : ((r - 1 : ℝ≥0) : ℝ) = (r : ℝ) - 1 := by
      simpa using NNReal.coe_sub hrle
    constructor
    · intro h
      have hreal : (u : ℝ) < (a : ℝ) + ((r - 1 : ℝ≥0) : ℝ) := by
        exact_mod_cast h
      have hresult : (1 : ℝ) + ((u - a : ℝ≥0) : ℝ) < (r : ℝ) := by
        linarith
      exact_mod_cast hresult
    · intro h
      have hreal : (1 : ℝ) + ((u - a : ℝ≥0) : ℝ) < (r : ℝ) := by
        exact_mod_cast h
      have hresult : (u : ℝ) < (a : ℝ) + ((r - 1 : ℝ≥0) : ℝ) := by
        linarith
      exact_mod_cast hresult

/-- Exact inverse on the appended clock, including the terminal level itself.
The hypothesis is only a bound on the old clock, not an inverse identity. -/
theorem clockInverse_splicedClock_of_terminal_le
    {A : ℝ≥0 → ℝ≥0} {a u : ℝ≥0} (hbound : ∀ t, A t ≤ a)
    (hu : a ≤ u) :
    clockInverse (splicedClock A a) u = ((1 + (u - a) : ℝ≥0) : ℝ≥0∞) := by
  exact clockInverse_eq_of_crossing_iff (splicedClock_crossing_iff hbound hu)

/-- Terminal convergence supplies the bound for the post-seam inverse. -/
theorem clockInverse_splicedClock_of_tendsto
    {A : ℝ≥0 → ℝ≥0} {a u : ℝ≥0} (hm : Monotone A)
    (hlim : Tendsto A atTop (𝓝 a)) (hu : a ≤ u) :
    clockInverse (splicedClock A a) u = ((1 + (u - a) : ℝ≥0) : ℝ≥0∞) := by
  exact clockInverse_splicedClock_of_terminal_le (clock_le_of_monotone_tendsto hm hlim) hu

/-- The inverse-clock path of the splice is exactly the appended path at every
level on or after the terminal level, with no positivity assumption on it. -/
theorem rawTimeChangePath_spliced_of_terminal_le
    {A : ℝ≥0 → ℝ≥0} {a u : ℝ≥0} {M : ℝ≥0 → ℝ} {m : ℝ} {W : ℝ≥0 → ℝ}
    (hbound : ∀ t, A t ≤ a) (hu : a ≤ u) :
    rawTimeChangePath (splicedPath M m W) (splicedClock A a) u = m + W (u - a) := by
  rw [rawTimeChangePath, clockInverse_splicedClock_of_terminal_le hbound hu]
  simp only [ENNReal.toNNReal_coe]
  have hseam : ¬ (1 + (u - a) : ℝ≥0) < 1 :=
    not_lt_of_ge (le_add_of_nonneg_right (bot_le : (0 : ℝ≥0) ≤ u - a))
  simp [splicedPath, hseam]

/-- At the seam the inverse is one and the path value is exactly the terminal
value when the auxiliary path starts at zero. -/
theorem rawTimeChangePath_spliced_at_terminal
    {A : ℝ≥0 → ℝ≥0} {a : ℝ≥0} {M : ℝ≥0 → ℝ} {m : ℝ} {W : ℝ≥0 → ℝ}
    (hbound : ∀ t, A t ≤ a) (hW : W 0 = 0) :
    rawTimeChangePath (splicedPath M m W) (splicedClock A a) a = m := by
  rw [rawTimeChangePath_spliced_of_terminal_le hbound le_rfl]
  simp [hW]

/-- A zero terminal level gives the full appended path starting at internal
time zero; the same inverse formula handles the degenerate channel. -/
theorem rawTimeChangePath_spliced_zero_clock
    {A : ℝ≥0 → ℝ≥0} {M : ℝ≥0 → ℝ} {m : ℝ} {W : ℝ≥0 → ℝ}
    (hzero : ∀ t, A t = 0) (u : ℝ≥0) :
    rawTimeChangePath (splicedPath M m W) (splicedClock A 0) u = m + W u := by
  have hbound : ∀ t, A t ≤ (0 : ℝ≥0) := fun t => le_of_eq (hzero t)
  simpa using rawTimeChangePath_spliced_of_terminal_le
    (M := M) (m := m) (W := W) hbound (bot_le : (0 : ℝ≥0) ≤ u)

end Ripple.ProbabilityTheory
