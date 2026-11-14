-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockBeforeTwentyRows.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockHourThinningRows

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockBeforeTwentyRows

open TimeTheorem PairLog StageEventSpec PhaseThreeModel.Numeric
  PhaseThreeClockProducer PhaseThreeClockVirtual PhaseThreeClockCore
  PhaseThreeClockCoreCounts PhaseThreeClockRows PhaseThreeClockSeedTails
  PhaseThreeClockActivationSeed PhaseThreeClockMacroscopicActivation
  PhaseThreeClockRawLocalRow PhaseThreeClockBeforeTwenty
  PhaseThreeClockHourThinningRows

variable {n : ℕ}

structure TwentyPassages (init : InputCfg n) (ω : InputLog n)
    (s : ℕ) (w : ClockTimes init) : Prop where
  activation_first :
    firstAfter (activationPred init (virtualLabels init ω)) s w.activation
  bulk_one :
    firstAfter (fun v =>
      bulkThreshold (clockCount (virtualCfg init ω s)) ≤
        frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) 1)
      s (w.bulk 1)
  bulk_twenty :
    firstAfter (fun v =>
      bulkThreshold (clockCount (virtualCfg init ω s)) ≤
        frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) 20)
      s (w.bulk 20)

def LowerTwentyTicks (init : InputCfg n) (ω : InputLog n)
    (s : ℕ) (w : ClockTimes init) : Prop :=
  (38 / 5 : ℝ) * (clockCount (virtualCfg init ω s) : ℝ) ≤
    (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
      (w.bulk 1) (w.bulk 20) : ℝ)

theorem bulk_one_le_bulk_twenty (init : InputCfg n) (ω : InputLog n)
    (s : ℕ) (w : ClockTimes init) (hw : TwentyPassages init ω s w) :
    w.bulk 1 ≤ w.bulk 20 := by
  classical
  have hfront :
      frontCountL init (virtualLabels init ω s) (virtualLabels init ω (w.bulk 20)) 20 ≤
        frontCountL init (virtualLabels init ω s) (virtualLabels init ω (w.bulk 20)) 1 := by
    unfold frontCountL StageEventSpec.labelCount
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨hi.1, by omega⟩
  by_contra hnot
  exact hw.bulk_one.2.2 (w.bulk 20) hw.bulk_twenty.1 (by omega)
    (hw.bulk_twenty.2.1.trans hfront)

theorem twenty_failure_after_ticks_subset (init : InputCfg n) (s : ℕ) :
    {ω | ∃ T, ∃ w : ClockTimes init, AsyncEntry init ω s T ∧
      TwentyPassages init ω s w ∧ LowerTwentyTicks init ω s w ∧
      w.bulk 20 < w.activation} ⊆ seedTwentyFailure init s := by
  rintro ω ⟨T, w, he, hw, hticks, hbad⟩
  have hseed : ω ∈ seedPrefix init s :=
    ⟨(seedTime_eq_iff init 3 ω s).2 he.first_phase_seed, he.seed_profile⟩
  have hcard := seedPrefix_card_eq init ω s hseed
  have hcount := seed_core_clockCount_eq_mask init ω s hseed
  have hfirst :
      firstAfter (fun v =>
        bulkThreshold (PhaseThreeClockGatedLaw.clockSet (labelsAt init ω s)).card ≤
          PhaseThreeClockGatedLaw.frontCount (virtualLabels init ω v) 1)
        s (w.bulk 1) := by
    refine ⟨hw.bulk_one.1, ?_, ?_⟩
    · have h := hw.bulk_one.2.1
      rw [hcount, core_front_eq_current_of_asyncEntry init ω s T (w.bulk 1) 1
        hseed he hw.bulk_one.1] at h
      exact h
    · intro v hsv hvu hv
      apply hw.bulk_one.2.2 v hsv hvu
      rw [hcount, core_front_eq_current_of_asyncEntry init ω s T v 1 hseed he hsv]
      exact hv
  obtain ⟨a, ha, -, -⟩ := exists_macroscopic_firstAfter_of_asyncEntry init ω s T he
  have hva := macroscopicTime_firstAfter_core_virtual init hcard s a ω ha
  have hae : a = w.activation := firstAfter_unique hva hw.activation_first
  have htime : macroscopicTime init s ω = (w.activation : WithTop ℕ) := by
    simpa only [hae] using ha
  refine ⟨w.bulk 1, hfirst, w.bulk 20, bulk_one_le_bulk_twenty init ω s w hw, ?_, ?_⟩
  · change (38 / 5 : ℝ) * _ ≤ _ at hticks
    rw [hcount, clockContactsL_virtual_seed init ω s (w.bulk 1) (w.bulk 20) hseed] at hticks
    exact hticks
  · rw [htime]
    exact_mod_cast hbad

theorem seed_before_twenty_after_ticks_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (s : ℕ) :
    law init {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
      SeedProfile n init (trace init ω s) ∧
      ∃ T, ∃ w : ClockTimes init, AsyncEntry init ω s T ∧
        TwentyPassages init ω s w ∧ LowerTwentyTicks init ω s w ∧
        w.bulk 20 < w.activation} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 99) *
        law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply (measure_mono ?_).trans
    ((seed_twenty_population_prefix_tail init hn s (seedPrefix init s)
      (seedPrefix_measurable init s) (fun _ h => h)).trans
        (mul_le_mul_left' (measure_mono (show seedPrefix init s ⊆
          {ω | seedTime init 3 ω = (s : WithTop ℕ)} from fun _ h => h.1)) _))
  rintro ω ⟨hs, hp, hb⟩
  exact ⟨⟨hs, hp⟩, twenty_failure_after_ticks_subset init s hb⟩

/-- A conditional subrow, with an unconditional rowFailure estimate.
Its premises are intersected events, not future conditioning. -/
def BeforeTwentyAfterTicks (init : InputCfg n) (ω : InputLog n) (s : ℕ) (_T : ℕ) : Prop :=
  TwentyPassages init ω s (virtualTimes init ω s) →
    LowerTwentyTicks init ω s (virtualTimes init ω s) →
      (virtualTimes init ω s).activation ≤ (virtualTimes init ω s).bulk 20

theorem before_twenty_after_ticks_row_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) :
    law init (rowFailure init (BeforeTwentyAfterTicks init)) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 99) := by
  apply splice_of_local (law init) (seedTime init 3)
    (rowFailure init (BeforeTwentyAfterTicks init)) _
    (fun s => (pairLogFiltration _ _).le s _ (seedTime_pastTime init 3 s))
  · rintro ω ⟨s, T, hs, -, -, -⟩
    rw [hs]
    exact WithTop.coe_ne_top
  · intro s
    apply (measure_mono ?_).trans (seed_before_twenty_after_ticks_tail init hn s)
    rintro ω ⟨⟨u, T, hu, -, he, hb⟩, hs⟩
    have hus : u = s := WithTop.coe_injective (hu.symm.trans hs)
    subst u
    have hbad : TwentyPassages init ω s (virtualTimes init ω s) ∧
        LowerTwentyTicks init ω s (virtualTimes init ω s) ∧
        (virtualTimes init ω s).bulk 20 < (virtualTimes init ω s).activation := by
      simpa only [BeforeTwentyAfterTicks, _root_.not_imp, not_le] using hb
    exact ⟨hs, he.seed_profile, T, virtualTimes init ω s, he,
      hbad.1, hbad.2.1, hbad.2.2⟩

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockBeforeTwentyRows

end
