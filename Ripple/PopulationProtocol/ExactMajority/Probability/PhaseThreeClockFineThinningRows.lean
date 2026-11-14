-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockFineThinningRows.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockFineThinning
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockJointFields

noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockFineThinningRows

open TimeTheorem PairLog StageEventSpec PhaseThreeModel.Numeric
  PhaseThreeClockProducer PhaseThreeClockVirtual PhaseThreeClockCore PhaseThreeClockCoreCounts
  PhaseThreeClockRows PhaseThreeClockSeedTails PhaseThreeClockActivationSeed
  PhaseThreeClockGatedLaw PhaseThreeClockMarkedWindow PhaseThreeClockMacroscopicActivation
  PhaseThreeClockShapeSeedFibre PhaseThreeClockSharpActivationSeed
  PhaseThreeClockThinningCalibrated PhaseThreeClockRawLocalRow
  PhaseThreeClockHourThinningRows PhaseThreeClockFineThinning PhaseThreeClockShapeFreeze PhaseThreeClockJointFields

variable {n : ℕ}

def FinePassages (init : InputCfg n) (ω : InputLog n) (s : ℕ) (w : ClockTimes init) : Prop :=
  firstAfter (activationPred init (virtualLabels init ω)) s w.activation ∧
  ∀ ell, 1 ≤ ell → ell ≤ clockTop n →
    firstAfter (fun v => 1 ≤ frontCountL init (virtualLabels init ω s)
      (virtualLabels init ω v) ell) s (w.first ell) ∧
    firstAfter (fun v => bulkThreshold (StageEventSpec.clockCount (virtualCfg init ω s)) ≤
      frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) ell) s (w.bulk ell)

def FineTickRow (init : InputCfg n) (ω : InputLog n) (s : ℕ) (w : ClockTimes init) : Prop :=
  ∀ ell, 1 ≤ ell → ell ≤ clockTop n →
    clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
      (max (w.first ell) w.activation) (w.bulk ell) ≤
        fineTicks (StageEventSpec.clockCount (virtualCfg init ω s))

def FineRawRow (init : InputCfg n) (ω : InputLog n) (s : ℕ) (w : ClockTimes init) : Prop :=
  ∀ ell, 1 ≤ ell → ell ≤ clockTop n →
    w.bulk ell ≤ max (w.first ell) w.activation +
      2000 * n * PhaseThreeModel.Numeric.frontWidth (StageEventSpec.clockCount (virtualCfg init ω s))

/-- Unfolding `seedFineFailure` by rewriting (a direct defeq makes the kernel time out). -/
theorem mem_seedFineFailure_iff (init : InputCfg n) (s ell : ℕ) (ω : InputLog n) :
    ω ∈ seedFineFailure init s ell ↔
      ω ∈ fineThinningFailure init (clockSet (labelsAt init ω s)) s ell := by
  have hdef : seedFineFailure init s ell =
      {ω | ω ∈ fineThinningFailure init (clockSet (labelsAt init ω s)) s ell} := rfl
  rw [hdef, Set.mem_setOf_eq]

theorem fine_failure_after_ticks_subset (init : InputCfg n)
    (hn : populationThreshold ≤ n) (s : ℕ) :
    {ω | ∃ T, ∃ w : ClockTimes init, AsyncEntry init ω s T ∧
      FinePassages init ω s w ∧ FineTickRow init ω s w ∧ ¬ FineRawRow init ω s w} ⊆
      allFineFailure init s := by
  classical
  rintro ω ⟨T, w, he, hp, ht, hb⟩
  have hseed : ω ∈ seedPrefix init s :=
    ⟨(seedTime_eq_iff init 3 ω s).2 he.first_phase_seed, he.seed_profile⟩
  let C := clockSet (labelsAt init ω s)
  have hcard := seedPrefix_card_eq init ω s hseed
  have hcount := seed_core_clockCount_eq_mask init ω s hseed
  obtain ⟨ell, hell, htop, hbad⟩ : ∃ ell, 1 ≤ ell ∧ ell ≤ clockTop n ∧
      max (w.first ell) w.activation + 2000 * n *
        PhaseThreeModel.Numeric.frontWidth (StageEventSpec.clockCount (virtualCfg init ω s)) < w.bulk ell := by
    simpa only [FineRawRow, not_forall, _root_.not_imp, not_le, exists_prop] using hb
  have transfer (b t : ℕ)
      (hf : firstAfter (fun v => b ≤ frontCountL init (virtualLabels init ω s)
        (virtualLabels init ω v) ell) s t) :
      firstAfter (fun v => b ≤ frontCount (virtualLabels init ω v) ell) s t := by
    refine ⟨hf.1, ?_, ?_⟩
    · simpa only [core_front_eq_current_of_asyncEntry init ω s T t ell hseed he hf.1] using hf.2.1
    · intro v hsv hvt hv
      apply hf.2.2 v hsv hvt
      simpa only [core_front_eq_current_of_asyncEntry init ω s T v ell hseed he hsv] using hv
  have hf := transfer 1 (w.first ell) (hp.2 ell hell htop).1
  have hbulk := transfer _ (w.bulk ell) (hp.2 ell hell htop).2
  rw [hcount] at hbulk
  have ha : firstAfter (fun v => macroscopicThreshold init.card ≤
      PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω v)) s w.activation := by
    have hp1 : firstAfter (fun v => Nat.ceil ((99 : ℝ) * (n : ℝ) / 100) ≤
        activeCountL init (virtualLabels init ω v)) s w.activation := hp.1
    simpa only [hcard, macroscopicThreshold, activeCountL_eq_activeCount] using hp1
  have hstart := fineStart_eq_firstAfter init ω s ell (w.first ell) w.activation
    (by simpa only [Nat.succ_le_iff] using hf) ha
  have hidx : ell - 1 < clockCap n := by change ell ≤ clockCap n at htop; omega
  apply Set.mem_iUnion.mpr
  refine ⟨⟨ell - 1, hidx⟩, ?_⟩
  have hi : ell - 1 + 1 = ell := by omega
  change ω ∈ seedFineFailure init s (ell - 1 + 1)
  rw [hi, mem_seedFineFailure_iff]
  apply Set.mem_iUnion.mpr
  refine ⟨max (w.first ell) w.activation, hstart, ?_⟩
  change (StageEventSpec.clockContacts init ω s _ _ : ℝ) < (fineTicks C.card : ℝ)
  by_contra hnot
  have hc : fineTicks C.card ≤ PhaseThreeClockThinning.maskContacts init C
      (max (w.first ell) w.activation)
      (max (w.first ell) w.activation + 2000 * n * PhaseThreeModel.Numeric.frontWidth C.card) ω := by
    have hnat : fineTicks C.card ≤ StageEventSpec.clockContacts init ω s
        (max (w.first ell) w.activation)
        (max (w.first ell) w.activation + 2000 * init.card * PhaseThreeModel.Numeric.frontWidth C.card) := by
      exact_mod_cast (le_of_not_gt hnot)
    simpa only [hcard, C, PhaseThreeClockThinning.maskContacts_seed_eq_stageEvent] using hnat
  have hbudget := ht ell hell htop
  rw [hcount, clockContactsL_virtual_seed init ω s _ _ hseed] at hbudget
  have hbudget' : PhaseThreeClockThinning.maskContacts init C
      (max (w.first ell) w.activation) (w.bulk ell) ω ≤ fineTicks C.card := by
    simpa only [C, PhaseThreeClockThinning.maskContacts_seed_eq_stageEvent] using hbudget
  have hsafe : shapeSafeAt init C s (w.bulk ell) ω :=
    ⟨⟨hseed, rfl⟩, fun i => ((PhaseThreeClockEmbeddingBridge.virtualLabels_clockEnvironment_of_asyncEntry
      init ω s T he (w.bulk ell) hbulk.1).phase_range i).2⟩
  obtain ⟨hm, hlo, hCm⟩ := seed_clock_calibration_inputs init hn ω s C.card hseed rfl
  have hCp := (logarithmic_inputs hm hlo hCm).1
  have hbp : 1 ≤ bulkThreshold C.card := by
    have : 0 < Nat.ceil ((C.card : ℝ) / 10) := Nat.ceil_pos.mpr (by positivity)
    exact this
  have hend := fine_raw_of_tick_budget_and_contacts init C s ell w.activation (w.first ell)
    (w.bulk ell) (2000 * n * PhaseThreeModel.Numeric.frontWidth C.card) hell hbp htop ω hsafe hbulk hbudget' hc
  rw [hcount] at hbad
  exact (not_lt_of_ge hend) hbad

def FineAfterTicks (init : InputCfg n) (ω : InputLog n) (s : ℕ) (_T : ℕ) : Prop :=
  FinePassages init ω s (virtualTimes init ω s) →
    FineTickRow init ω s (virtualTimes init ω s) →
      FineRawRow init ω s (virtualTimes init ω s)

theorem fine_after_ticks_row_tail (init : InputCfg n) (hn : populationThreshold ≤ n) :
    law init (rowFailure init (FineAfterTicks init)) ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 98) := by
  apply splice_of_local (law init) (seedTime init 3) (rowFailure init (FineAfterTicks init)) _
    (fun s => (pairLogFiltration _ _).le s _ (seedTime_pastTime init 3 s))
  · rintro ω ⟨s, T, hs, -, -, -⟩
    rw [hs]
    exact WithTop.coe_ne_top
  · intro s
    apply (measure_mono ?_).trans
      ((all_fine_prefix_tail init hn s (seedPrefix init s)
        (seedPrefix_measurable init s) (fun _ h => h)).trans
        (mul_le_mul_left' (measure_mono (show seedPrefix init s ⊆
          {ω | seedTime init 3 ω = (s : WithTop ℕ)} from fun _ h => h.1)) _))
    rintro ω ⟨⟨u, T, hu, -, he, hb⟩, hs⟩
    have hus : u = s := WithTop.coe_injective (hu.symm.trans hs)
    subst u
    have hbad : FinePassages init ω s (virtualTimes init ω s) ∧
        FineTickRow init ω s (virtualTimes init ω s) ∧
        ¬ FineRawRow init ω s (virtualTimes init ω s) := by
      simpa only [FineAfterTicks, _root_.not_imp] using hb
    exact ⟨⟨hs, he.seed_profile⟩, fine_failure_after_ticks_subset init hn s
      ⟨T, virtualTimes init ω s, he, hbad.1, hbad.2.1, hbad.2.2⟩⟩

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockFineThinningRows

end
