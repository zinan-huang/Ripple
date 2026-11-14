import Ripple.Stochastic.KnightTimeChangePaths
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Finite-time evaluation of inverse-clock stopping

An infinite inverse leaves the process running; it is never evaluated through
`toNNReal`. This distinction is essential on finite-clock paths. These lemmas
identify the concrete stopped paths needed by the stochastic estimates.
-/

open Set Filter
open scoped NNReal ENNReal Topology

namespace Ripple.ProbabilityTheory
open Ripple.Analysis

/-- Evaluate the minimum of a finite time and the extended inverse safely. -/
noncomputable def clockStoppedTime (A : ℝ≥0 → ℝ≥0) (u t : ℝ≥0) : ℝ≥0 :=
  if clockInverse A u = ⊤ then t else min t (clockInverse A u).toNNReal

/-- The original path stopped at its inverse clock. -/
noncomputable def clockStoppedPath (M : ℝ≥0 → ℝ) (A : ℝ≥0 → ℝ≥0)
    (u t : ℝ≥0) : ℝ := M (clockStoppedTime A u t)

theorem clockStoppedTime_eq_self_of_le
    {A : ℝ≥0 → ℝ≥0} {u t : ℝ≥0} (h : (t : ℝ≥0∞) ≤ clockInverse A u) :
    clockStoppedTime A u t = t := by
  unfold clockStoppedTime
  split_ifs with hf
  · rfl
  · rw [← ENNReal.coe_toNNReal hf] at h
    exact min_eq_left (by exact_mod_cast h)

/-- A clock that stays below a level never triggers that level's stop. -/
theorem clockInverse_eq_top_of_bound {A : ℝ≥0 → ℝ≥0} {u : ℝ≥0}
    (h : ∀ t, A t ≤ u) : clockInverse A u = ⊤ := by
  apply top_unique
  change ⊤ ≤ ⨅ t : ℝ≥0, ⨅ (_ : u < A t), (t : ℝ≥0∞)
  refine le_iInf fun t => le_iInf fun ht => ?_
  exact False.elim ((not_lt_of_ge (h t)) ht)

/-- On the event that the terminal clock lies below the stopping level, the
entire stopped path equals the original path, simultaneously in time. -/
theorem clockStoppedPath_eq_of_terminal_le
    {A : ℝ≥0 → ℝ≥0} {M : ℝ≥0 → ℝ} {u : ℝ≥0}
    (hu : terminalClock A ≤ (u : ℝ≥0∞)) : clockStoppedPath M A u = M := by
  have hi : clockInverse A u = ⊤ := clockInverse_eq_top_of_bound fun t => by
    have h := (le_iSup (fun s : ℝ≥0 => (A s : ℝ≥0∞)) t).trans hu
    exact_mod_cast h
  funext t
  simp [clockStoppedPath, clockStoppedTime, hi]

/-- Stopping a continuous path at this extended inverse preserves continuity. -/
theorem continuous_clockStoppedPath
    {A : ℝ≥0 → ℝ≥0} {M : ℝ≥0 → ℝ} (hM : Continuous M) (u : ℝ≥0) :
    Continuous (clockStoppedPath M A u) := by
  unfold clockStoppedPath clockStoppedTime
  by_cases hf : clockInverse A u = ⊤
  · simp only [hf, if_true]
    exact hM
  · simp only [if_neg hf]
    exact hM.comp (continuous_id.min continuous_const)

/-- The stopped clock is capped by the stopping level. -/
theorem clock_at_stoppedTime_le
    {A : ℝ≥0 → ℝ≥0} (hc : Continuous A) (hm : Monotone A) (hz : A 0 = 0)
    (u t : ℝ≥0) : A (clockStoppedTime A u t) ≤ u := by
  apply (le_clockInverse_iff hc hm hz u _).mp
  unfold clockStoppedTime
  split_ifs with hf
  · simp [hf]
  · rw [← ENNReal.coe_toNNReal hf]
    exact_mod_cast min_le_right t (clockInverse A u).toNNReal

/-- Clock increments viewed from a deterministic physical time. -/
def shiftedClock (A : ℝ≥0 → ℝ≥0) (s r : ℝ≥0) : ℝ≥0 := A (s + r) - A s

/-- The shifted, clock-stopped increment is the actual increment on a flat
clock interval. This is a pathwise identity, not a stochastic integral rule. -/
theorem shifted_stopped_increment_of_flat
    {A : ℝ≥0 → ℝ≥0} {M : ℝ≥0 → ℝ} (hm : Monotone A)
    {s t ε : ℝ≥0} (hst : s ≤ t) (hflat : A s = A t) :
    clockStoppedPath (fun r => M (s + r) - M s) (shiftedClock A s) ε (t - s) =
      M t - M s := by
  have hinv : ((t - s : ℝ≥0) : ℝ≥0∞) ≤ clockInverse (shiftedClock A s) ε := by
    change _ ≤ ⨅ r : ℝ≥0, ⨅ (_ : ε < shiftedClock A s r), (r : ℝ≥0∞)
    refine le_iInf fun r => le_iInf fun hr => ?_
    have htr : t - s ≤ r := by
      apply le_of_not_gt
      intro hrt
      have hsrt : s + r ≤ t := by
        calc s + r ≤ s + (t - s) := add_le_add le_rfl hrt.le
             _ = t := add_tsub_cancel_of_le hst
      have hzero : shiftedClock A s r = 0 := by
        apply tsub_eq_zero_of_le
        exact (hm hsrt).trans_eq hflat.symm
      rw [hzero] at hr
      exact (not_lt_of_ge bot_le) hr
    exact_mod_cast htr
  rw [clockStoppedPath, clockStoppedTime_eq_self_of_le hinv, add_tsub_cancel_of_le hst]

end Ripple.ProbabilityTheory
