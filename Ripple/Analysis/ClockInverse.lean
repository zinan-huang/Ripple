import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.Basic

/-!
# Right inverses of nonnegative clocks

The right inverse `τ(u) = inf {t | A t > u}` of a nonnegative clock, including finite
terminal clocks and plateaux. The inverse is extended-valued; evaluation at `toNNReal`
requires a finiteness proof.
-/

open Set Filter
open scoped NNReal ENNReal Topology

namespace Ripple.Analysis

/-- The infimum of strict upper-level crossing times; an empty crossing set gives infinity. -/
noncomputable def clockInverse (A : ℝ≥0 → ℝ≥0) (u : ℝ≥0) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : u < A t), (t : ℝ≥0∞)

/-- The terminal clock, whether finite or infinite. -/
noncomputable def terminalClock (A : ℝ≥0 → ℝ≥0) : ℝ≥0∞ :=
  ⨆ t, (A t : ℝ≥0∞)

theorem clockInverse_le_of_lt {A : ℝ≥0 → ℝ≥0} {u t : ℝ≥0}
    (h : u < A t) : clockInverse A u ≤ t :=
  iInf_le_of_le t (iInf_le_of_le h le_rfl)

theorem clockInverse_lt_iff_exists {A : ℝ≥0 → ℝ≥0} {u : ℝ≥0} {b : ℝ≥0∞} :
    clockInverse A u < b ↔ ∃ t : ℝ≥0, u < A t ∧ (t : ℝ≥0∞) < b := by
  simp only [clockInverse, iInf_lt_iff, exists_prop]

theorem clockInverse_mono (A : ℝ≥0 → ℝ≥0) : Monotone (clockInverse A) := by
  intro u v huv
  refine le_iInf fun t => le_iInf fun hvt => ?_
  exact clockInverse_le_of_lt (huv.trans_lt hvt)

theorem clockInverse_ne_top_of_lt_terminal {A : ℝ≥0 → ℝ≥0} {u : ℝ≥0}
    (h : (u : ℝ≥0∞) < terminalClock A) : clockInverse A u ≠ ⊤ := by
  obtain ⟨t, ht⟩ := (lt_iSup_iff.mp h)
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top
    (clockInverse_le_of_lt (by exact_mod_cast ht))

/-- Strict upper-level inversion is right continuous, even for a discontinuous clock. -/
theorem clockInverse_rightContinuous (A : ℝ≥0 → ℝ≥0) (u : ℝ≥0) :
    ContinuousWithinAt (clockInverse A) (Ici u) u := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact ha.trans_le (clockInverse_mono A hv)
  · intro b hb
    obtain ⟨t, ht, htb⟩ := clockInverse_lt_iff_exists.mp hb
    have hev : ∀ᶠ v in 𝓝[≥] u, v < A t :=
      (eventually_lt_nhds ht).filter_mono nhdsWithin_le_nhds
    filter_upwards [hev] with v hv
    exact (clockInverse_le_of_lt hv).trans_lt htb

/-- The entire sublevel set is the initial interval ending at the right inverse. -/
theorem le_clockInverse_iff {A : ℝ≥0 → ℝ≥0}
    (hc : Continuous A) (hm : Monotone A) (hzero : A 0 = 0) (u t : ℝ≥0) :
    (t : ℝ≥0∞) ≤ clockInverse A u ↔ A t ≤ u := by
  constructor
  · intro ht
    by_cases htzero : t = 0
    · simpa [htzero, hzero] using (bot_le : (0 : ℝ≥0) ≤ u)
    have hpos : (0 : ℝ≥0) < t := bot_lt_iff_ne_bot.mpr htzero
    have hcl : t ∈ closure (Ico (0 : ℝ≥0) t) := by
      rw [closure_Ico (ne_of_lt hpos)]
      exact ⟨bot_le, le_rfl⟩
    apply closure_minimal (s := Ico (0 : ℝ≥0) t)
      (t := A ⁻¹' Iic u) ?_ (isClosed_Iic.preimage hc) hcl
    intro r hr
    change A r ≤ u
    apply le_of_not_gt
    intro hur
    have hle := ht.trans (clockInverse_le_of_lt hur)
    exact (not_le_of_gt hr.2) (by exact_mod_cast hle)
  · intro ht
    refine le_iInf fun r => le_iInf fun hur => ?_
    have htr : t ≤ r := le_of_not_gt fun hrt =>
      (not_lt_of_ge ((hm hrt.le).trans ht)) hur
    exact_mod_cast htr

theorem clockInverse_lt_iff {A : ℝ≥0 → ℝ≥0}
    (hc : Continuous A) (hm : Monotone A) (hzero : A 0 = 0) (u t : ℝ≥0) :
    clockInverse A u < t ↔ u < A t := by
  simpa only [not_le] using not_congr (le_clockInverse_iff hc hm hzero u t)

/-- A finite inverse evaluates the clock at precisely its level. -/
theorem clock_at_clockInverse {A : ℝ≥0 → ℝ≥0}
    (hc : Continuous A) (hm : Monotone A) (hzero : A 0 = 0) {u : ℝ≥0}
    (hu : (u : ℝ≥0∞) < terminalClock A) :
    A (clockInverse A u).toNNReal = u := by
  have hfin := clockInverse_ne_top_of_lt_terminal hu
  let T := (clockInverse A u).toNNReal
  have hT : (T : ℝ≥0∞) = clockInverse A u := ENNReal.coe_toNNReal hfin
  apply le_antisymm
  · exact (le_clockInverse_iff hc hm hzero u T).mp hT.le
  · apply le_of_not_gt
    intro hlt
    have hev : ∀ᶠ t in 𝓝[>] T, A t < u :=
      (hc.continuousAt.eventually (gt_mem_nhds hlt)).filter_mono nhdsWithin_le_nhds
    obtain ⟨t, ht, htu⟩ := (hev.and self_mem_nhdsWithin).exists
    have hinv : clockInverse A u < t := by
      rw [← hT]
      exact_mod_cast htu
    exact (not_lt_of_ge ht.le) ((clockInverse_lt_iff hc hm hzero u t).mp hinv)

/-- The inverse of the current level lies to the right of the current time. -/
theorem self_le_clockInverse_level {A : ℝ≥0 → ℝ≥0}
    (hc : Continuous A) (hm : Monotone A) (hzero : A 0 = 0) (t : ℝ≥0) :
    (t : ℝ≥0∞) ≤ clockInverse A (A t) :=
  (le_clockInverse_iff hc hm hzero _ _).mpr le_rfl

/-- All times between a point and its finite inverse have the same clock value. -/
theorem clock_constant_on_plateau {A : ℝ≥0 → ℝ≥0}
    (hc : Continuous A) (hm : Monotone A) (hzero : A 0 = 0) (t : ℝ≥0)
    (hu : (A t : ℝ≥0∞) < terminalClock A) :
    EqOn A (fun _ => A t) (Icc t (clockInverse A (A t)).toNNReal) := by
  intro r hr
  exact le_antisymm
    ((hm hr.2).trans_eq (clock_at_clockInverse hc hm hzero hu)) (hm hr.1)

/-- Sublevel characterization also describes terminal plateaux whose inverse is infinite. -/
theorem clockInverse_level_eq_top_iff {A : ℝ≥0 → ℝ≥0} (hm : Monotone A) (t : ℝ≥0) :
    clockInverse A (A t) = ⊤ ↔ ∀ r, t ≤ r → A r = A t := by
  constructor
  · intro h r htr
    apply le_antisymm ?_ (hm htr)
    apply le_of_not_gt
    intro hlt
    have := clockInverse_le_of_lt hlt
    rw [h] at this
    exact ENNReal.coe_ne_top (top_unique this)
  · intro h
    apply top_unique
    refine le_iInf fun r => le_iInf fun hlt => ?_
    by_cases htr : t ≤ r
    · exact False.elim ((ne_of_lt hlt) (h r htr).symm)
    · exact False.elim ((not_lt_of_ge (hm (le_of_not_ge htr))) hlt)

end Ripple.Analysis
