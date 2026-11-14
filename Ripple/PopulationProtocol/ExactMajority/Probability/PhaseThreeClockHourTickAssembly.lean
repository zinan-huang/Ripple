-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockHourTickAssembly.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockTwoMinuteGap
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockBeforeTwentyRows

/-!
P9 from the positive-minute lower passages and the high-passage allowance.
Hour zero starts at activation and uses levels 20 through 254. Positive
hours use 254 lower passages and subtract at most 8*C contacts before
their genuine high-threshold start. The raw conversion retains the
observed first-seed mass.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockHourTickAssembly

open TimeTheorem PairLog StageEventSpec PhaseThreeModel.Numeric
  PhaseThreeClockCore PhaseThreeClockVirtual PhaseThreeClockProducer
  PhaseThreeClockRows PhaseThreeClockSeedTails PhaseThreeClockActivationSeed
  PhaseThreeClockRawLocalRow PhaseThreeClockActivationRows
  PhaseThreeClockHourOccupancyRow PhaseThreeClockWorkRows
  PhaseThreeClockBeforeTwentyRows PhaseThreeClockHourThinningRows
  PhaseThreeClockJointCore PhaseThreeClockContactIntervals
  PhaseThreeClockTwoMinuteGap

variable {n : ℕ}

theorem lower_twenty_ticks_of_positive (init : InputCfg n)
    (ω : InputLog n) (s : ℕ) (w : ClockTimes init)
    (hp : LevelPassages init ω s w)
    (hlower : ∀ i, 1 ≤ i → i < clockTop n →
      (2 / 5 : ℝ) * (clockCount (virtualCfg init ω s) : ℝ) ≤
        (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
          (w.bulk i) (w.bulk (i + 1)) : ℝ)) :
    LowerTwentyTicks init ω s w := by
  have htop : 1 + 19 ≤ clockTop n := by unfold clockTop; omega
  have hchain := lower_contact_chain init ω s w hp
    ((2 / 5 : ℝ) * (clockCount (virtualCfg init ω s) : ℝ))
    hlower 1 19 (by omega) htop
  change (38 / 5 : ℝ) * (clockCount (virtualCfg init ω s) : ℝ) ≤ _
  calc
    _ = (19 : ℝ) * ((2 / 5 : ℝ) * (clockCount (virtualCfg init ω s) : ℝ)) := by ring
    _ ≤ _ := by simpa only [Nat.cast_ofNat] using hchain

theorem lower_hour_ticks_of_passages (init : InputCfg n)
    (hn : populationThreshold ≤ n) (ω : InputLog n) (s T : ℕ)
    (w : ClockTimes init) (hseed : ω ∈ seedPrefix init s)
    (he : AsyncEntry init ω s T) (hp : LevelPassages init ω s w)
    (hhour : HourPassages init ω s w) (hj : JointFrontFields init ω s w)
    (hbefore : w.activation ≤ w.bulk 20)
    (hlower : ∀ i, 1 ≤ i → i < clockTop n →
      (2 / 5 : ℝ) * (clockCount (virtualCfg init ω s) : ℝ) ≤
        (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
          (w.bulk i) (w.bulk (i + 1)) : ℝ))
    (hupper : ∀ h, 1 ≤ h → h ≤ hourIndex n →
      clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
        (w.bulk (256 * h)) (w.start h) ≤ 8 * clockCount (virtualCfg init ω s)) :
    LowerHourTicks init ω s w := by
  intro h hh
  have hcap : 256 * (h + 1) ≤ clockTop n := by unfold clockTop; omega
  have hgap := bulk_before_small_finish init hn ω s T w hseed he hp hj
    (256 * (h + 1)) (w.finish h) (by omega) hcap (hhour.2.2.2 h hh)
  by_cases hz : h = 0
  · subst h
    have hchain := lower_contact_chain init ω s w hp
      ((2 / 5 : ℝ) * (clockCount (virtualCfg init ω s) : ℝ))
      hlower 20 234 (by omega) (by unfold clockTop; omega)
    have hleft := core_contact_antitone_left init (virtualLabels init ω s)
      (drawLabels init ω) w.activation (w.bulk 20) (w.bulk 254) hbefore
    have hright := core_contact_mono_right init (virtualLabels init ω s)
      (drawLabels init ω) w.activation (w.bulk 254) (w.finish 0) hgap.le
    have hleftR :
        (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
          (w.bulk 20) (w.bulk 254) : ℝ) ≤
        (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
          w.activation (w.bulk 254) : ℝ) := by exact_mod_cast hleft
    have hrightR :
        (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
          w.activation (w.bulk 254) : ℝ) ≤
        (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
          w.activation (w.finish 0) : ℝ) := by exact_mod_cast hright
    rw [hhour.2.1]
    norm_num only [Nat.cast_ofNat] at hchain
    linarith only [hchain, hleftR, hrightR]
  · have hpos : 1 ≤ h := by omega
    let a := 256 * h
    let b := 256 * (h + 1) - 2
    have ha : 1 ≤ a := by dsimp only [a]; omega
    have hab : a + 254 = b := by dsimp only [a, b]; omega
    have hchain := lower_contact_chain init ω s w hp
      ((2 / 5 : ℝ) * (clockCount (virtualCfg init ω s) : ℝ))
      hlower a 254 ha (by dsimp only [a]; omega)
    rw [hab] at hchain
    have htriangle := core_contact_triangle init (virtualLabels init ω s)
      (drawLabels init ω) (w.bulk a) (w.start h) (w.bulk b)
    have hmono := core_contact_mono_right init (virtualLabels init ω s)
      (drawLabels init ω) (w.start h) (w.bulk b) (w.finish h) hgap.le
    have hhigh := hupper h hpos hh
    have htriR :
        (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
          (w.bulk a) (w.bulk b) : ℝ) ≤
        (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
          (w.bulk a) (w.start h) : ℝ) +
        (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
          (w.start h) (w.bulk b) : ℝ) := by exact_mod_cast htriangle
    have hmonoR :
        (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
          (w.start h) (w.bulk b) : ℝ) ≤
        (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
          (w.start h) (w.finish h) : ℝ) := by exact_mod_cast hmono
    have hhighR :
        (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
          (w.bulk a) (w.start h) : ℝ) ≤
        8 * (clockCount (virtualCfg init ω s) : ℝ) := by exact_mod_cast hhigh
    norm_num only [Nat.cast_ofNat] at hchain
    linarith only [hchain, htriR, hmonoR, hhighR]

def RawWidthAfterTicks (init : InputCfg n) (ω : InputLog n) (s : ℕ) (_T : ℕ) : Prop :=
  HourPassages init ω s (virtualTimes init ω s) →
    LowerHourTicks init ω s (virtualTimes init ω s) →
      RawWidthRow init ω s (virtualTimes init ω s)

/-- Global form of the seed-prefix raw-width conversion. -/
theorem raw_width_after_ticks_row_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) :
    law init (rowFailure init (RawWidthAfterTicks init)) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 98) := by
  apply splice_of_local (law init) (seedTime init 3)
    (rowFailure init (RawWidthAfterTicks init)) _
    (fun s => (pairLogFiltration _ _).le s _ (seedTime_pastTime init 3 s))
  · rintro ω ⟨s, T, hs, -, -, -⟩
    rw [hs]
    exact WithTop.coe_ne_top
  · intro s
    apply (measure_mono ?_).trans (seed_raw_width_after_ticks_tail init hn s)
    rintro ω ⟨⟨u, T, hu, -, he, hb⟩, hs⟩
    have hus : u = s := WithTop.coe_injective (hu.symm.trans hs)
    subst u
    have hbad : HourPassages init ω s (virtualTimes init ω s) ∧
        LowerHourTicks init ω s (virtualTimes init ω s) ∧
        ¬ RawWidthRow init ω s (virtualTimes init ω s) := by
      simpa only [RawWidthAfterTicks, _root_.not_imp] using hb
    exact ⟨hs, he.seed_profile, T, virtualTimes init ω s, he,
      hbad.1, hbad.2.1, hbad.2.2⟩

/-- Assemble the complete existing RowShape once the two width estimates
and the actual raw-hour windows have been obtained. -/
theorem rowShape_of_joint_high_raw (init : InputCfg n) (hn : 1 ≤ n)
    (ω : InputLog n) (s T : ℕ) (w : ClockTimes init)
    (hseed : ω ∈ seedPrefix init s) (he : AsyncEntry init ω s T)
    (hhour : HourPassages init ω s w) (hj : JointFrontFields init ω s w)
    (hhigh : ∀ v, s ≤ v → v ≤ w.cap →
      frontHeightL init (virtualLabels init ω s) (virtualLabels init ω v) -
        frontQuantileL init (virtualLabels init ω s) (virtualLabels init ω v)
          (highThreshold (clockCount (virtualCfg init ω s))) ≤
        2 * PhaseThreeModel.Numeric.frontWidth (clockCount (virtualCfg init ω s)) + 20)
    (hraw : RawWidthRow init ω s w) :
    RowShape init (virtualLabels init ω) (virtualCfg init ω) (drawLabels init ω) s w := by
  obtain ⟨hwork, hworknext⟩ := work_rows_of_rawWidth init hn ω s w hseed hraw
  obtain ⟨hmain, hclock⟩ := active_role_rows_of_activationFirst init ω s w hseed hhour.1
  exact
    { bulk_width := hj.bulk_width
      high_width := hhigh
      front_shape := hj.front_shape
      tick_local := hj.tick_local
      previous_end := previous_end_row_of_passages init hn ω s T w hseed he hhour
      raw_width := hraw
      exact_hour := exact_hour_row_of_passages init ω s T w hseed he hhour
      first_work_allowance := hwork
      second_work_allowance := hworknext
      active_main_floor := hmain
      active_clock_floor := hclock }

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockHourTickAssembly

end
