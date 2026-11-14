-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockBasicRows.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockPassageOrderRows

/-!
# A common witness for the completed step-3 Core rows

The output retains the genuine seed, AsyncEntry, and one common ClockTimes
witness. All first-passage coordinates exist outside an original-law null
set; the only nonzero error in this package is the shared P3a n^(-8) row.

BasicClockRows deliberately lists only the completed Core fields. It is
not VirtualClockCore: shape, width, timing deadlines, and the other
probabilistic rows are still absent.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockBasicRows

open TimeTheorem PairLog StageEventSpec PhaseThreeClockProducer
  PhaseThreeClockSeedTails PhaseThreeClockRawLocalRow
  PhaseThreeClockActivationRows PhaseThreeClockHourOccupancyRow
  PhaseThreeClockPassageOrderRows

variable {n : ℕ}

structure BasicClockRows (init : InputCfg n) (ω : InputLog n) (s T : ℕ)
    (w : ClockTimes init) : Prop where
  passages : PassageTimes init ω s w
  raw_local : RawLocalRow init w
  exact_hour : ExactHourRow init ω s w
  previous_end : PreviousEndRow init w
  active_main_floor : ActiveMainRow init ω s w
  active_clock_floor : ActiveClockRow init ω s w
  activation_before_cap : ActivationBeforeCapRow init w
  all_before_cap : AllBeforeCapRow init T w
  level_before_cap : LevelBeforeCapRow init w
  hour_before_cap : HourBeforeCapRow init w

theorem basicRows_of_passages (init : InputCfg n) (hn : 1 ≤ n)
    (ω : InputLog n) (s T : ℕ) (w : ClockTimes init)
    (hseed : ω ∈ seedPrefix init s) (hentry : AsyncEntry init ω s T)
    (hw : PassageTimes init ω s w) (hraw : RawLocalRow init w) :
    BasicClockRows init ω s T w := by
  have hfloors := active_role_rows_of_activationFirst init ω s w hseed hw.hours.1
  have horders := passage_order_rows init hn ω s T w hseed hentry hw
  exact ⟨hw, hraw, exact_hour_row_of_passages init ω s T w hseed hentry hw.hours,
    previous_end_row_of_passages init hn ω s T w hseed hentry hw.hours,
    hfloors.1, hfloors.2, horders.1, horders.2.1, horders.2.2.1, horders.2.2.2⟩

def BasicGoodAt (init : InputCfg n) (s : ℕ) (ω : InputLog n) : Prop :=
  ∃ T, ∃ w : ClockTimes init, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T ∧
    BasicClockRows init ω s T w

def basicFailureAt (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
    SeedProfile n init (trace init ω s) ∧
    (∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T) ∧
      ¬ BasicGoodAt init s ω}

/-- A single shared witness supplies all completed fields.
There is no union factor for the number of fields or the seed time. -/
theorem seed_basic_clock_rows_tail (init : InputCfg n)
    (hm : 20 ≤ init.card) (hcard : init.card = n)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) (hlarge : 42 ≤ n)
    (s : ℕ) :
    law init (basicFailureAt init s) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 8) *
        law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  classical
  let B : Set (InputLog n) :=
    {ω | ω ∈ seedPrefix init s ∧ ∃ T, AsyncEntry init ω s T ∧
      ¬ ∃ w : ClockTimes init, PassageTimes init ω s w}
  have hB : law init B = 0 :=
    seed_passage_times_null init (by omega) hlarge s
  have hsub : basicFailureAt init s ⊆ B ∪ rawLocalFailureAt init s := by
    rintro ω ⟨hs, hsp, ⟨T, hT, hentry⟩, hbad⟩
    have hseed : ω ∈ seedPrefix init s := ⟨hs, hsp⟩
    by_cases hw : ∃ w : ClockTimes init, PassageTimes init ω s w
    · obtain ⟨w, hw⟩ := hw
      by_cases hraw : RawLocalRow init w
      · exact False.elim (hbad ⟨T, w, hT, hentry,
          basicRows_of_passages init (by omega) ω s T w hseed hentry hw hraw⟩)
      · exact Or.inr ⟨hs, hsp, T, w, hT, hentry, hw.levels, hraw⟩
    · exact Or.inl ⟨hseed, T, hentry, hw⟩
  calc
    law init (basicFailureAt init s) ≤ law init (B ∪ rawLocalFailureAt init s) :=
      measure_mono hsub
    _ ≤ law init B + law init (rawLocalFailureAt init s) := measure_union_le _ _
    _ = law init (rawLocalFailureAt init s) := by rw [hB, zero_add]
    _ ≤ _ := seed_raw_local_tail init hm hcard hn s

theorem basic_clock_rows_global_tail (init : InputCfg n)
    (hm : 20 ≤ init.card) (hcard : init.card = n)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) (hlarge : 42 ≤ n) :
    law init {ω | ∃ s, ω ∈ basicFailureAt init s} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 8) := by
  apply splice_of_local (law init) (seedTime init 3)
    {ω | ∃ s, ω ∈ basicFailureAt init s} _
    (fun s => (pairLogFiltration _ _).le s _ (seedTime_pastTime init 3 s))
  · rintro ω ⟨s, hs⟩
    rw [hs.1]
    exact WithTop.coe_ne_top
  · intro s
    apply (measure_mono ?_).trans
      (seed_basic_clock_rows_tail init hm hcard hn hlarge s)
    rintro ω ⟨⟨u, hu⟩, hs⟩
    have hus : u = s := WithTop.coe_injective (hu.1.symm.trans hs)
    subst u
    exact hu

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockBasicRows

end
