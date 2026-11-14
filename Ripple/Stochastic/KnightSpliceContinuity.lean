import Ripple.Stochastic.KnightSplicePaths
import Ripple.Stochastic.KnightTimeChangeContinuity
import Mathlib.Tactic.FieldSimp

/-!
# Compactification, pre-seam inverse matching, and seam continuity

The physical compression `t/(1+t)` is inverse to `r/(1-r)` below one.
The strict inverse of the spliced clock is the compressed old strict inverse
below the terminal clock. No strict increase of the old clock is assumed.
-/

open Set Filter
open scoped NNReal ENNReal Topology

namespace Ripple.ProbabilityTheory
open Ripple.Analysis

/-- Compress a finite physical time to a time strictly below the seam. -/
noncomputable def compressedTime (t : ℝ≥0) : ℝ≥0 := t / (1 + t)

theorem compressedTime_lt_one (t : ℝ≥0) : compressedTime t < 1 := by
  rw [compressedTime, div_lt_iff₀ (by positivity)]
  simp

/-- The strict order adjunction on the pre-seam interval. -/
theorem compressedTime_lt_iff {t r : ℝ≥0} (hr : r < 1) :
    compressedTime t < r ↔ t < compactificationTime r := by
  have hd : (0 : ℝ≥0) < 1 - r := tsub_pos_of_lt hr
  rw [compressedTime, compactificationTime, div_lt_iff₀ (by positivity), lt_div_iff₀ hd]
  have hsub : ((1 - r : ℝ≥0) : ℝ) = 1 - (r : ℝ) := by
    exact_mod_cast NNReal.coe_sub hr.le
  constructor <;> intro h
  · have hh : (t : ℝ) < (r : ℝ) * (1 + (t : ℝ)) := by exact_mod_cast h
    have hh' : (t : ℝ) * ((1 - r : ℝ≥0) : ℝ) < (r : ℝ) := by rw [hsub]; nlinarith
    exact_mod_cast hh'
  · have hh : (t : ℝ) * ((1 - r : ℝ≥0) : ℝ) < (r : ℝ) := by exact_mod_cast h
    rw [hsub] at hh
    have hh' : (t : ℝ) < (r : ℝ) * (1 + (t : ℝ)) := by nlinarith
    exact_mod_cast hh'

/-- Exact cancellation, including physical time zero. -/
theorem compactificationTime_compressedTime (t : ℝ≥0) :
    compactificationTime (compressedTime t) = t := by
  apply NNReal.eq
  have hr := compressedTime_lt_one t
  have hsub := NNReal.coe_sub hr.le
  have hd : (1 : ℝ) + (t : ℝ) ≠ 0 := by positivity
  simp only [compactificationTime, NNReal.coe_div, hsub, NNReal.coe_one,
    compressedTime, NNReal.coe_add] at *
  field_simp
  <;> ring

/-- Compactified physical time goes to infinity from the left of the seam. -/
theorem compactificationTime_tendsto_seam :
    Tendsto compactificationTime (𝓝[<] (1 : ℝ≥0)) atTop := by
  apply tendsto_atTop.2
  intro b
  have hnear : ∀ᶠ r in 𝓝[<] (1 : ℝ≥0), compressedTime b < r :=
    (eventually_gt_nhds (compressedTime_lt_one b)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hnear, self_mem_nhdsWithin] with r hbr hr
  exact ((compressedTime_lt_iff (show r < 1 from hr)).mp hbr).le

/-- Before the terminal clock, the strict crossing set of the splice is the
open interval above the compressed original inverse. -/
theorem splicedClock_crossing_iff_of_lt_terminal
    {A : ℝ≥0 → ℝ≥0} (hc : Continuous A) (hm : Monotone A) (hz : A 0 = 0)
    {a u : ℝ≥0} (ha : (a : ℝ≥0∞) = terminalClock A) (hu : u < a)
    (r : ℝ≥0) :
    u < splicedClock A a r ↔ compressedTime (clockInverse A u).toNNReal < r := by
  have hut : (u : ℝ≥0∞) < terminalClock A := by rw [← ha]; exact_mod_cast hu
  have hfin := clockInverse_ne_top_of_lt_terminal hut
  by_cases hr : r < 1
  · rw [splicedClock, if_pos hr, compressedTime_lt_iff hr]
    have he := ENNReal.coe_toNNReal hfin
    conv_rhs => rw [← ENNReal.coe_lt_coe, he]
    exact (clockInverse_lt_iff hc hm hz u (compactificationTime r)).symm
  · rw [splicedClock, if_neg hr]
    apply iff_of_true
    · exact hu.trans_le (le_add_of_nonneg_right bot_le)
    · exact (compressedTime_lt_one _).trans_le (le_of_not_gt hr)

/-- Exact pre-seam inverse matching, valid even when the original inverse jumps
across a clock plateau. -/
theorem clockInverse_splicedClock_of_lt_terminal
    {A : ℝ≥0 → ℝ≥0} (hc : Continuous A) (hm : Monotone A) (hz : A 0 = 0)
    {a u : ℝ≥0} (ha : (a : ℝ≥0∞) = terminalClock A) (hu : u < a) :
    clockInverse (splicedClock A a) u =
      (compressedTime (clockInverse A u).toNNReal : ℝ≥0∞) :=
  clockInverse_eq_of_crossing_iff (splicedClock_crossing_iff_of_lt_terminal hc hm hz ha hu)

/-- Evaluation after compactification agrees exactly with the original raw
inverse-clock path on the pre-seam branch. -/
theorem rawTimeChangePath_spliced_of_lt_terminal
    {A : ℝ≥0 → ℝ≥0} {M W : ℝ≥0 → ℝ} {m : ℝ}
    (hc : Continuous A) (hm : Monotone A) (hz : A 0 = 0)
    {a u : ℝ≥0} (ha : (a : ℝ≥0∞) = terminalClock A) (hu : u < a) :
    rawTimeChangePath (splicedPath M m W) (splicedClock A a) u =
      rawTimeChangePath M A u := by
  rw [rawTimeChangePath, clockInverse_splicedClock_of_lt_terminal hc hm hz ha hu]
  simp only [ENNReal.toNNReal_coe, splicedPath, compressedTime_lt_one, if_true,
    compactificationTime_compressedTime, rawTimeChangePath]

/-- The spliced raw path equals the completed path at every internal time.
The equality uses the strict inverse on both sides, including the seam. -/
theorem rawTimeChangePath_spliced_eq_completed
    {A : ℝ≥0 → ℝ≥0} {M W : ℝ≥0 → ℝ} {m : ℝ}
    (hc : Continuous A) (hm : Monotone A) (hz : A 0 = 0)
    (hfinite : terminalClock A ≠ ⊤) (u : ℝ≥0) :
    rawTimeChangePath (splicedPath M m W)
      (splicedClock A (terminalClock A).toNNReal) u = completedTimeChangePath M A m W u := by
  have ha := ENNReal.coe_toNNReal hfinite
  have hbound : ∀ t, A t ≤ (terminalClock A).toNNReal := by
    intro t
    have h : (A t : ℝ≥0∞) ≤ terminalClock A := le_iSup (fun s : ℝ≥0 => (A s : ℝ≥0∞)) t
    rw [← ha] at h
    exact_mod_cast h
  by_cases hu : u < (terminalClock A).toNNReal
  · rw [rawTimeChangePath_spliced_of_lt_terminal hc hm hz ha hu,
      completedTimeChangePath_of_lt_terminal]
    rw [← ha]
    exact_mod_cast hu
  · rw [rawTimeChangePath_spliced_of_terminal_le hbound (le_of_not_gt hu),
      completedTimeChangePath_of_terminal_le]
    rw [← ha]
    exact_mod_cast le_of_not_gt hu

/-- Convergence at physical infinity is precisely the left continuity needed
by the compactified path at physical seam time one. -/
theorem continuousAt_splicedPath_seam
    {M W : ℝ≥0 → ℝ} {m : ℝ} (hlim : Tendsto M atTop (𝓝 m))
    (hW : Continuous W) (hz : W 0 = 0) :
    ContinuousAt (splicedPath M m W) 1 := by
  apply continuousAt_if_lt_seam
  · simpa [hz] using hlim.comp compactificationTime_tendsto_seam
  · exact (continuous_const.add (hW.comp (continuous_id.sub continuous_const))).continuousAt

/-- The compactified clock joins continuously to the appended unit-speed clock. -/
theorem continuousAt_splicedClock_seam
    {A : ℝ≥0 → ℝ≥0} {a : ℝ≥0} (hlim : Tendsto A atTop (𝓝 a)) :
    ContinuousAt (splicedClock A a) 1 := by
  apply continuousAt_if_lt_seam
  · simpa using hlim.comp compactificationTime_tendsto_seam
  · exact (continuous_const.add (continuous_id.sub continuous_const)).continuousAt

end Ripple.ProbabilityTheory
