-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockCanonicalRows.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockBasicRows
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRows

/-!
# Completed step-3 fields at the compiled canonical witness

Every genuine first-passage coordinate used by BasicClockRows agrees
with PhaseThreeClockRows.virtualTimes. Equality is proved only on the
specified level and hour ranges; no equality of initialization maps or
of entire ClockTimes records is asserted.

The canonical first-passage clauses fail only on the already proved
null event. The complete BasicClockRows package has the same shared
n^(-8) original-law tail, both on a genuine seed fibre and in the exact
compiled rowFailure format.

This is not a RowPassage producer: fine_raw_local is still missing.
No RowShape, RowActivation, or full virtual-core tail is asserted.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockCanonicalRows

open TimeTheorem PairLog StageEventSpec PhaseThreeClockProducer
  PhaseThreeClockVirtual PhaseThreeClockCore PhaseThreeClockRows
  PhaseThreeClockSeedTails PhaseThreeClockRawLocalRow PhaseThreeClockActivationRows
  PhaseThreeClockHourOccupancyRow PhaseThreeClockPassageOrderRows
  PhaseThreeClockBasicRows

variable {n : ℕ}

theorem virtualTimes_activation_eq_of_passages (init : InputCfg n)
    (ω : InputLog n) (s : ℕ) (w : ClockTimes init)
    (hw : PassageTimes init ω s w) :
    (virtualTimes init ω s).activation = w.activation := by
  change firstAfterTime (activationPred init (virtualLabels init ω)) s = w.activation
  exact firstAfterTime_eq hw.hours.1

theorem virtualTimes_cap_eq_of_passages (init : InputCfg n)
    (ω : InputLog n) (s : ℕ) (w : ClockTimes init)
    (hw : PassageTimes init ω s w) :
    (virtualTimes init ω s).cap = w.cap := by
  change firstAfterTime (fun v =>
    frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) (clockTop n) =
      clockCount (virtualCfg init ω s)) s = w.cap
  exact firstAfterTime_eq hw.cap

theorem virtualTimes_first_eq_of_passages (init : InputCfg n)
    (ω : InputLog n) (s : ℕ) (w : ClockTimes init)
    (hw : PassageTimes init ω s w) (ell : ℕ) (hell : ell ≤ clockTop n) :
    (virtualTimes init ω s).first ell = w.first ell := by
  by_cases hz : ell = 0
  · subst ell
    simp only [virtualTimes, canonicalTimes, ↓reduceIte, ite_true, hw.first_zero]
  · simp only [virtualTimes, canonicalTimes, if_neg hz]
    exact firstAfterTime_eq (hw.levels.1 ell (by omega) hell)

theorem virtualTimes_bulk_eq_of_passages (init : InputCfg n)
    (ω : InputLog n) (s : ℕ) (w : ClockTimes init)
    (hw : PassageTimes init ω s w) (ell : ℕ) (hell : ell ≤ clockTop n) :
    (virtualTimes init ω s).bulk ell = w.bulk ell := by
  by_cases hz : ell = 0
  · subst ell
    simp only [virtualTimes, canonicalTimes, ↓reduceIte, ite_true, hw.bulk_zero]
  · simp only [virtualTimes, canonicalTimes, if_neg hz]
    exact firstAfterTime_eq (hw.levels.2 ell (by omega) hell)

theorem virtualTimes_start_eq_of_passages (init : InputCfg n)
    (ω : InputLog n) (s : ℕ) (w : ClockTimes init)
    (hw : PassageTimes init ω s w) (h : ℕ)
    (hh : h ≤ PhaseThreeModel.Numeric.hourIndex n) :
    (virtualTimes init ω s).start h = w.start h := by
  by_cases hz : h = 0
  · subst h
    calc
      (virtualTimes init ω s).start 0 = (virtualTimes init ω s).activation :=
        canonicalTimes_start_zero init (virtualLabels init ω) (virtualCfg init ω) s
      _ = w.activation := virtualTimes_activation_eq_of_passages init ω s w hw
      _ = w.start 0 := hw.hours.2.1.symm
  · simp only [virtualTimes, canonicalTimes, if_neg hz]
    exact firstAfterTime_eq (hw.hours.2.2.1 h (by omega) hh)

theorem virtualTimes_finish_eq_of_passages (init : InputCfg n)
    (ω : InputLog n) (s : ℕ) (w : ClockTimes init)
    (hw : PassageTimes init ω s w) (h : ℕ)
    (hh : h ≤ PhaseThreeModel.Numeric.hourIndex n) :
    (virtualTimes init ω s).finish h = w.finish h := by
  change firstAfterTime (fun v =>
    smallThreshold (clockCount (virtualCfg init ω s)) ≤
      frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) (256 * (h + 1)))
    s = w.finish h
  exact firstAfterTime_eq (hw.hours.2.2.2 h hh)

theorem passageTimes_virtualTimes (init : InputCfg n)
    (ω : InputLog n) (s : ℕ) (w : ClockTimes init)
    (hw : PassageTimes init ω s w) :
    PassageTimes init ω s (virtualTimes init ω s) := by
  constructor
  · exact canonicalTimes_first_zero init (virtualLabels init ω) (virtualCfg init ω) s
  · exact canonicalTimes_bulk_zero init (virtualLabels init ω) (virtualCfg init ω) s
  · constructor
    · intro ell hp hell
      rw [virtualTimes_first_eq_of_passages init ω s w hw ell hell]
      exact hw.levels.1 ell hp hell
    · intro ell hp hell
      rw [virtualTimes_bulk_eq_of_passages init ω s w hw ell hell]
      exact hw.levels.2 ell hp hell
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [virtualTimes_activation_eq_of_passages init ω s w hw]
      exact hw.hours.1
    · exact canonicalTimes_start_zero init (virtualLabels init ω) (virtualCfg init ω) s
    · intro h hp hh
      rw [virtualTimes_start_eq_of_passages init ω s w hw h hh]
      exact hw.hours.2.2.1 h hp hh
    · intro h hh
      rw [virtualTimes_finish_eq_of_passages init ω s w hw h hh]
      exact hw.hours.2.2.2 h hh
  · rw [virtualTimes_cap_eq_of_passages init ω s w hw]
    exact hw.cap

/-- Transport the completed fields, not the entire witness record. -/
theorem basicRows_virtualTimes (init : InputCfg n) (ω : InputLog n)
    (s T : ℕ) (w : ClockTimes init) (hb : BasicClockRows init ω s T w) :
    BasicClockRows init ω s T (virtualTimes init ω s) := by
  have hw := hb.passages
  have ha := virtualTimes_activation_eq_of_passages init ω s w hw
  have hc := virtualTimes_cap_eq_of_passages init ω s w hw
  constructor
  · exact passageTimes_virtualTimes init ω s w hw
  · intro ell hp hell
    rw [virtualTimes_bulk_eq_of_passages init ω s w hw ell hell,
      virtualTimes_first_eq_of_passages init ω s w hw ell hell]
    exact hb.raw_local ell hp hell
  · intro h hh v hsv hvf
    apply hb.exact_hour h hh v
    · simpa only [virtualTimes_start_eq_of_passages init ω s w hw h hh] using hsv
    · simpa only [virtualTimes_finish_eq_of_passages init ω s w hw h hh] using hvf
  · intro h hp hh
    rw [virtualTimes_finish_eq_of_passages init ω s w hw (h - 1) (by omega),
      virtualTimes_start_eq_of_passages init ω s w hw h hh]
    exact hb.previous_end h hp hh
  · intro v hav hvc
    apply hb.active_main_floor v
    · simpa only [ha] using hav
    · simpa only [hc] using hvc
  · intro v hav hvc
    apply hb.active_clock_floor v
    · simpa only [ha] using hav
    · simpa only [hc] using hvc
  · change (virtualTimes init ω s).activation ≤ (virtualTimes init ω s).cap
    rw [ha, hc]
    exact hb.activation_before_cap
  · change T ≤ (virtualTimes init ω s).cap
    rw [hc]
    exact hb.all_before_cap
  · intro ell hell
    rw [virtualTimes_first_eq_of_passages init ω s w hw ell hell,
      virtualTimes_bulk_eq_of_passages init ω s w hw ell hell, hc]
    exact hb.level_before_cap ell hell
  · intro h hh
    rw [virtualTimes_start_eq_of_passages init ω s w hw h hh,
      virtualTimes_finish_eq_of_passages init ω s w hw h hh, hc]
    exact hb.hour_before_cap h hh

def canonicalPassageFailureAt (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
    SeedProfile n init (trace init ω s) ∧
    ∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T ∧
      ¬ PassageTimes init ω s (virtualTimes init ω s)}

/-- Canonical first-passage existence has zero error, independent of P3a. -/
theorem seed_canonical_passage_times_null (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n) (s : ℕ) :
    law init (canonicalPassageFailureAt init s) = 0 := by
  apply le_antisymm ?_ bot_le
  apply le_trans (measure_mono ?_) (le_of_eq (seed_passage_times_null init hc hn s))
  rintro ω ⟨hs, hp, T, -, he, hbad⟩
  refine ⟨⟨hs, hp⟩, T, he, ?_⟩
  rintro ⟨w, hw⟩
  exact hbad (passageTimes_virtualTimes init ω s w hw)

theorem canonical_passage_times_global_null (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n) :
    law init (PhaseThreeClockRows.rowFailure init
      (fun ω s _T => PassageTimes init ω s (virtualTimes init ω s))) = 0 := by
  apply le_antisymm ?_ bot_le
  apply splice_of_local (law init) (seedTime init 3)
    (PhaseThreeClockRows.rowFailure init
      (fun ω s _T => PassageTimes init ω s (virtualTimes init ω s))) 0
    (fun s => (pairLogFiltration _ _).le s _ (seedTime_pastTime init 3 s))
  · rintro ω ⟨s, T, hs, -, -, -⟩
    rw [hs]
    exact WithTop.coe_ne_top
  · intro s
    rw [zero_mul]
    apply le_trans (measure_mono ?_)
      (le_of_eq (seed_canonical_passage_times_null init hc hn s))
    rintro ω ⟨⟨u, T, hu, hT, he, hbad⟩, hs⟩
    have hus : u = s := WithTop.coe_injective (hu.symm.trans hs)
    subst u
    exact ⟨hs, he.seed_profile, T, hT, he, hbad⟩

def canonicalBasicFailureAt (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
    SeedProfile n init (trace init ω s) ∧
    ∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T ∧
      ¬ BasicClockRows init ω s T (virtualTimes init ω s)}

theorem canonicalBasicFailureAt_subset (init : InputCfg n) (s : ℕ) :
    canonicalBasicFailureAt init s ⊆ basicFailureAt init s := by
  rintro ω ⟨hs, hp, T, hT, he, hbad⟩
  refine ⟨hs, hp, ⟨T, hT, he⟩, ?_⟩
  rintro ⟨U, w, hU, heU, hb⟩
  have hUT : U = T := firstHit_unique heU.all_first he.all_first
  subst U
  exact hbad (basicRows_virtualTimes init ω s T w hb)

/-- The requested genuine-seed fibre tail, with failure at the compiled
virtualTimes and the entry time occurring in the event itself. -/
theorem seed_canonical_basic_rows_tail (init : InputCfg n)
    (hm : 20 ≤ init.card) (hcard : init.card = n)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) (hlarge : 42 ≤ n)
    (s : ℕ) :
    law init (canonicalBasicFailureAt init s) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 8) *
        law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} :=
  (measure_mono (canonicalBasicFailureAt_subset init s)).trans
    (seed_basic_clock_rows_tail init hm hcard hn hlarge s)

/-- Exact compiled rowFailure format. AsyncEntry supplies SeedProfile. -/
theorem canonical_basic_rows_global_tail (init : InputCfg n)
    (hm : 20 ≤ init.card) (hcard : init.card = n)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) (hlarge : 42 ≤ n) :
    law init (PhaseThreeClockRows.rowFailure init
      (fun ω s T => BasicClockRows init ω s T (virtualTimes init ω s))) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 8) := by
  apply (measure_mono ?_).trans
    (basic_clock_rows_global_tail init hm hcard hn hlarge)
  rintro ω ⟨s, T, hs, hT, he, hbad⟩
  refine ⟨s, canonicalBasicFailureAt_subset init s ?_⟩
  exact ⟨hs, he.seed_profile, T, hT, he, hbad⟩

theorem seed_canonical_raw_local_tail (init : InputCfg n)
    (hm : 20 ≤ init.card) (hcard : init.card = n)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) (hlarge : 42 ≤ n)
    (s : ℕ) :
    law init {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
      SeedProfile n init (trace init ω s) ∧
      ∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T ∧
        ¬ RawLocalRow init (virtualTimes init ω s)} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 8) *
        law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply (measure_mono ?_).trans (seed_canonical_basic_rows_tail init hm hcard hn hlarge s)
  rintro ω ⟨hs, hp, T, hT, he, hbad⟩
  exact ⟨hs, hp, T, hT, he, fun hb => hbad hb.raw_local⟩

theorem canonical_raw_local_global_tail (init : InputCfg n)
    (hm : 20 ≤ init.card) (hcard : init.card = n)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) (hlarge : 42 ≤ n) :
    law init (PhaseThreeClockRows.rowFailure init
      (fun ω s _T => RawLocalRow init (virtualTimes init ω s))) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 8) := by
  apply (measure_mono ?_).trans (canonical_basic_rows_global_tail init hm hcard hn hlarge)
  rintro ω ⟨s, T, hs, hT, he, hbad⟩
  exact ⟨s, T, hs, hT, he, fun hb => hbad hb.raw_local⟩

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockCanonicalRows

end
