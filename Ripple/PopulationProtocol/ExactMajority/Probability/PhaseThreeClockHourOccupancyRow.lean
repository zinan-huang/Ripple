-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockHourOccupancyRow.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockHourGeometry
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockActivationRows

/-!
# Exact-hour occupancy and previous-end rows on the genuine seed fibre

The witness guards are only the first-passage clauses from ClockCore.
For every correct choice of those witnesses, the exact_hour and
previous_end rows follow deterministically from the implemented unit
front law, seed initialization, and the observed macroscopic activation.

The resulting seed-fibre failure event is empty. This does not construct
the endpoints, their raw widths, or their embedded passage budgets.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockHourOccupancyRow

open TimeTheorem PairLog StageEventSpec PhaseThreeClockProducer
  PhaseThreeClockVirtual PhaseThreeClockCore PhaseThreeClockCoreCounts
  PhaseThreeClockSeedTails PhaseThreeClockActivationSeed
  PhaseThreeClockEmbeddingBridge PhaseThreeClockRawLocalRow
  PhaseThreeClockActivationRows PhaseThreeClockHourGeometry

variable {n : ℕ}

theorem current_positive_front_zero_at_seed (init : InputCfg n)
    (ω : InputLog n) (s ell : ℕ) (hseed : ω ∈ seedPrefix init s) (hell : 1 ≤ ell) :
    PhaseThreeClockGatedLaw.frontCount (virtualLabels init ω s) ell = 0 := by
  classical
  rw [virtual_eq_actual_at_seedPrefix init ω s hseed]
  have hzero (i : Fin init.card) (hr : (labelsAt init ω s i).role = .clock) :
      PhaseThreeClockGatedLaw.effMinute (labelsAt init ω s i) = 0 := by
    by_cases ha : 3 ≤ (labelsAt init ω s i).phase.val
    · have hp := (hseed.2.phase_range _ (labelsAt_mem_trace init ω s i)).2
      have heq : (labelsAt init ω s i).phase.val = 3 := by omega
      have hm := Phase3Pre3.clock_minute_zero_of_Phase3EntryAgent
        (hseed.2.fresh _ (labelsAt_mem_trace init ω s i) heq) hr
      simp only [PhaseThreeClockGatedLaw.effMinute, if_pos ha, hm]
    · simp only [PhaseThreeClockGatedLaw.effMinute, if_neg ha]
  unfold PhaseThreeClockGatedLaw.frontCount
  apply Finset.card_eq_zero.mpr
  ext i
  constructor
  · intro hi
    simp only [PhaseThreeClockGatedLaw.aboveSet, Finset.mem_filter,
      Finset.mem_univ, true_and] at hi
    have hz := hzero i hi.1
    omega
  · intro hi
    simp at hi

theorem core_front_step_bounds_of_asyncEntry (init : InputCfg n)
    (ω : InputLog n) (s T ell v : ℕ) (hseed : ω ∈ seedPrefix init s)
    (hentry : AsyncEntry init ω s T) (hell : 1 ≤ ell) (hcap : ell ≤ clockTop n)
    (hsv : s ≤ v) :
    frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) ell ≤
      frontCountL init (virtualLabels init ω s) (virtualLabels init ω (v + 1)) ell ∧
    frontCountL init (virtualLabels init ω s) (virtualLabels init ω (v + 1)) ell ≤
      frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) ell + 1 := by
  simp only [core_front_eq_current_of_asyncEntry init ω s T v ell hseed hentry hsv,
    core_front_eq_current_of_asyncEntry init ω s T (v + 1) ell hseed hentry (by omega)]
  cases hd : drawLabels init ω (v + 1) with
  | none =>
      simp only [PhaseThreeClockGatedLaw.frontCount_virtualLabels_succ_of_none init ω v hd ell]
      omega
  | some ij =>
      rcases ij with ⟨i, j⟩
      simp only [frontCount_virtualLabels_succ_of_asyncEntry init ω s T hentry v hsv
        i j hd ell hell hcap]
      by_cases hg : PhaseThreeClockGatedLevelOne.GatedTick ell
          (virtualLabels init ω v) i j
      · simp only [if_pos hg]
        omega
      · simp only [if_neg hg]
        omega

theorem core_front_mono_of_asyncEntry (init : InputCfg n)
    (ω : InputLog n) (s T ell u v : ℕ) (hseed : ω ∈ seedPrefix init s)
    (hentry : AsyncEntry init ω s T) (hell : 1 ≤ ell) (hcap : ell ≤ clockTop n)
    (hsu : s ≤ u) (huv : u ≤ v) :
    frontCountL init (virtualLabels init ω s) (virtualLabels init ω u) ell ≤
      frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) ell := by
  induction v, huv using Nat.le_induction with
  | base => exact le_rfl
  | succ v huv ih =>
      exact ih.trans (core_front_step_bounds_of_asyncEntry init ω s T ell v
        hseed hentry hell hcap (hsu.trans huv)).1

theorem core_positive_front_zero_at_seed (init : InputCfg n)
    (ω : InputLog n) (s T ell : ℕ) (hseed : ω ∈ seedPrefix init s)
    (hentry : AsyncEntry init ω s T) (hell : 1 ≤ ell) :
    frontCountL init (virtualLabels init ω s) (virtualLabels init ω s) ell = 0 := by
  rw [core_front_eq_current_of_asyncEntry init ω s T s ell hseed hentry le_rfl]
  exact current_positive_front_zero_at_seed init ω s ell hseed hell

def HourPassages (init : InputCfg n) (ω : InputLog n) (s : ℕ)
    (w : ClockTimes init) : Prop :=
  ActivationFirstAt init ω s w.activation ∧
  w.start 0 = w.activation ∧
  (∀ h, 1 ≤ h → h ≤ PhaseThreeModel.Numeric.hourIndex n →
    firstAfter (fun v => highThreshold (clockCount (virtualCfg init ω s)) ≤
      frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) (256 * h))
      s (w.start h)) ∧
  (∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    firstAfter (fun v => smallThreshold (clockCount (virtualCfg init ω s)) ≤
      frontCountL init (virtualLabels init ω s) (virtualLabels init ω v)
        (256 * (h + 1))) s (w.finish h))

def ExactHourRow (init : InputCfg n) (ω : InputLog n) (s : ℕ)
    (w : ClockTimes init) : Prop :=
  ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    ∀ v, w.start h ≤ v → v ≤ w.finish h →
      899 * clockCount (virtualCfg init ω s) ≤
        1000 * exactHourClocksL init (virtualLabels init ω s) (virtualLabels init ω v) h

def PreviousEndRow (init : InputCfg n) (w : ClockTimes init) : Prop :=
  ∀ h, 1 ≤ h → h ≤ PhaseThreeModel.Numeric.hourIndex n →
    w.finish (h - 1) < w.start h

theorem hourPassages_of_virtualCore (init : InputCfg n) (ω : InputLog n)
    (s T : ℕ) (w : ClockTimes init) (hc : VirtualClockCore init ω s T w) :
    HourPassages init ω s w :=
  ⟨hc.activation_first, hc.start_zero, hc.start_positive, hc.finish_first⟩

theorem exact_hour_row_of_passages (init : InputCfg n) (ω : InputLog n)
    (s T : ℕ) (w : ClockTimes init) (hseed : ω ∈ seedPrefix init s)
    (hentry : AsyncEntry init ω s T) (hw : HourPassages init ω s w) :
    ExactHourRow init ω s w := by
  intro h hh
  have hnext : 256 * (h + 1) ≤ clockTop n := by
    unfold clockTop
    omega
  have hinit := core_positive_front_zero_at_seed init ω s T (256 * (h + 1))
    hseed hentry (by omega)
  have hunit := fun v hv =>
    (core_front_step_bounds_of_asyncEntry init ω s T (256 * (h + 1)) v
      hseed hentry (by omega) hnext hv).2
  by_cases hz : h = 0
  · subst h
    rw [hw.2.1]
    exact zero_hour_window_occupancy init (virtualLabels init ω) s w.activation
      (w.finish 0) (clockCount (virtualCfg init ω s)) hw.1.1
      (hw.2.2.2 0 hh) (by rw [hinit]; exact Nat.zero_le _) hunit
      (fun v hv => (active_role_floors_after_activationFirst init ω s w.activation
        hseed hw.1 v hv).2)
  · have hpos : 1 ≤ h := by omega
    apply positive_hour_window_occupancy init (virtualLabels init ω) s
      (w.start h) (w.finish h) h (clockCount (virtualCfg init ω s)) hpos
      (hw.2.2.1 h hpos hh) (hw.2.2.2 h hh)
      (by rw [hinit]; exact Nat.zero_le _) hunit
    intro u v hsu huv
    exact core_front_mono_of_asyncEntry init ω s T (256 * h) u v
      hseed hentry (by omega) (by unfold clockTop; omega) hsu huv

theorem previous_end_row_of_passages (init : InputCfg n) (hn : 1 ≤ n)
    (ω : InputLog n) (s T : ℕ) (w : ClockTimes init)
    (hseed : ω ∈ seedPrefix init s) (hentry : AsyncEntry init ω s T)
    (hw : HourPassages init ω s w) :
    PreviousEndRow init w := by
  intro h hpos hh
  have hdensity := (seed_role_density init ω s hseed).2
  have hC : 1 ≤ clockCount (virtualCfg init ω s) := by omega
  have hthreshold :
      smallThreshold (clockCount (virtualCfg init ω s)) <
        highThreshold (clockCount (virtualCfg init ω s)) := by
    have hlow := highThreshold_rounding (clockCount (virtualCfg init ω s))
    have hhigh := smallThreshold_rounding (clockCount (virtualCfg init ω s))
    omega
  have hprev := hw.2.2.2 (h - 1) (by omega)
  have heq : h - 1 + 1 = h := by omega
  rw [heq] at hprev
  have hinit := core_positive_front_zero_at_seed init ω s T (256 * h)
    hseed hentry (by omega)
  apply successive_quantile_firstAfter_lt hthreshold hprev (hw.2.2.1 h hpos hh)
    (by rw [hinit]; exact Nat.zero_le _)
  intro v hv
  exact (core_front_step_bounds_of_asyncEntry init ω s T (256 * h) v hseed hentry
    (by omega) (by unfold clockTop; omega) hv).2

def hourOccupancyFailureAt (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
    SeedProfile n init (trace init ω s) ∧
    ∃ T, ∃ w : ClockTimes init, AsyncEntry init ω s T ∧ HourPassages init ω s w ∧
      (¬ ExactHourRow init ω s w ∨ ¬ PreviousEndRow init w)}

/-- These two completed Core rows have no additional error budget. -/
theorem seed_hour_occupancy_null (init : InputCfg n) (hn : 1 ≤ n) (s : ℕ) :
    law init (hourOccupancyFailureAt init s) = 0 := by
  have hempty : hourOccupancyFailureAt init s = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ω ⟨hs, hp, T, w, he, hw, hbad⟩
    have hseed : ω ∈ seedPrefix init s := ⟨hs, hp⟩
    rcases hbad with hbad | hbad
    · exact hbad (exact_hour_row_of_passages init ω s T w hseed he hw)
    · exact hbad (previous_end_row_of_passages init hn ω s T w hseed he hw)
  rw [hempty, measure_empty]


/-- The exact_hour field has zero additional seed-fibre error. -/
theorem seed_exact_hour_row_tail (init : InputCfg n) (hn : 1 ≤ n) (s : ℕ) :
    law init {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
      SeedProfile n init (trace init ω s) ∧
      ∃ T, ∃ w : ClockTimes init, AsyncEntry init ω s T ∧ HourPassages init ω s w ∧
        ¬ ExactHourRow init ω s w} ≤
      0 * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  calc
    law init {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
        SeedProfile n init (trace init ω s) ∧
        ∃ T, ∃ w : ClockTimes init, AsyncEntry init ω s T ∧ HourPassages init ω s w ∧
          ¬ ExactHourRow init ω s w} ≤ law init (hourOccupancyFailureAt init s) := by
      apply measure_mono
      rintro ω ⟨hs, hp, T, w, he, hw, hbad⟩
      exact ⟨hs, hp, T, w, he, hw, Or.inl hbad⟩
    _ = 0 := seed_hour_occupancy_null init hn s
    _ = 0 * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by simp

/-- The previous_end field has zero additional seed-fibre error. -/
theorem seed_previous_end_row_tail (init : InputCfg n) (hn : 1 ≤ n) (s : ℕ) :
    law init {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
      SeedProfile n init (trace init ω s) ∧
      ∃ T, ∃ w : ClockTimes init, AsyncEntry init ω s T ∧ HourPassages init ω s w ∧
        ¬ PreviousEndRow init w} ≤
      0 * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  calc
    law init {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
        SeedProfile n init (trace init ω s) ∧
        ∃ T, ∃ w : ClockTimes init, AsyncEntry init ω s T ∧ HourPassages init ω s w ∧
          ¬ PreviousEndRow init w} ≤ law init (hourOccupancyFailureAt init s) := by
      apply measure_mono
      rintro ω ⟨hs, hp, T, w, he, hw, hbad⟩
      exact ⟨hs, hp, T, w, he, hw, Or.inr hbad⟩
    _ = 0 := seed_hour_occupancy_null init hn s
    _ = 0 * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by simp

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockHourOccupancyRow

end
