-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockJointCanonicalTails.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockJointLocalTails
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockFineThinningRows
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockInitializationRows
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRowsGuarded

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockJointCanonicalTails

open PhaseThreeClockProducer PhaseThreeClockActivationSeed

open TimeTheorem PairLog StageEventSpec PhaseThreeModel.Numeric
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockCore
  PhaseThreeClockRows PhaseThreeClockRowsGuarded PhaseThreeClockSeedTails
  PhaseThreeClockProducer PhaseThreeClockActivationSeed
  PhaseThreeClockRawLocalRow PhaseThreeClockPassageOrderRows
  PhaseThreeClockCanonicalRows PhaseThreeClockJointCore
  PhaseThreeClockJointFields PhaseThreeClockJointLocalTails
  PhaseThreeClockBulkShapeBudget PhaseThreeClockShapeFreeze
  PhaseThreeClockFirstBulkBase PhaseThreeClockSharpActivationSeed
  PhaseThreeClockMarkedShape PhaseThreeClockShapeSeedFibre
  PhaseThreeClockRareChainFibres PhaseThreeClockFineThinningRows
  PhaseThreeClockInitializationRows

variable {n : ℕ}

theorem rowFailure_empty_of_card_ne (init : InputCfg n) (hcard : init.card ≠ n)
    (R : InputLog n → ℕ → ℕ → Prop) : rowFailure init R = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro ω ⟨s, T, hs, -, he, -⟩
  exact hcard (seedPrefix_card_eq init ω s ⟨hs, he.seed_profile⟩)

theorem canonical_passages_null_of_threshold (init : InputCfg n)
    (hn : populationThreshold ≤ n) :
    law init (rowFailure init
      (fun ω s _T => PassageTimes init ω s (virtualTimes init ω s))) = 0 := by
  by_cases hcard : init.card = n
  · have hlarge := (strong_bulk_family_calibration hn).1
    exact canonical_passage_times_global_null init (by omega) (by omega)
  · rw [rowFailure_empty_of_card_ne init hcard, measure_empty]

structure CanonicalFrontPacket (init : InputCfg n) (ω : InputLog n)
    (s : ℕ) (_T : ℕ) : Prop where
  passages : PassageTimes init ω s (virtualTimes init ω s)
  raw_local : RawLocalRow init (virtualTimes init ω s)
  joint : JointFrontFields init ω s (virtualTimes init ω s)

theorem current_firstAfter_of_core (init : InputCfg n) (ω : InputLog n)
    (s T ell b u : ℕ) (hseed : ω ∈ seedPrefix init s)
    (he : AsyncEntry init ω s T)
    (hf : firstAfter (fun v => b ≤ frontCountL init (virtualLabels init ω s)
      (virtualLabels init ω v) ell) s u) :
    firstAfter (fun v => b ≤ PhaseThreeClockGatedLaw.frontCount
      (virtualLabels init ω v) ell) s u := by
  refine ⟨hf.1, ?_, ?_⟩
  · simpa only [core_front_eq_current_of_asyncEntry init ω s T u ell hseed he hf.1]
      using hf.2.1
  · intro v hsv hvu hv
    apply hf.2.2 v hsv hvu
    simpa only [core_front_eq_current_of_asyncEntry init ω s T v ell hseed he hsv]
      using hv

/-- Unfolding the `seed*` failure sets by rewriting; the direct defeq makes the kernel time out. -/
theorem mem_seedCountActivationFailure_iff (init : InputCfg n) (s : ℕ) (ω : InputLog n) :
    ω ∈ seedCountActivationFailure init s ↔
      ω ∈ sharpActivationFailure init s
        (PhaseThreeClockGatedLaw.clockCount (labelsAt init ω s)) := by
  unfold seedCountActivationFailure
  rw [Set.mem_setOf_eq]

theorem mem_seedActivationBulkFailure_iff (init : InputCfg n) (s : ℕ) (ω : InputLog n) :
    ω ∈ seedActivationBulkFailure init s ↔
      ω ∈ activationBulkFailure init (clockSet (labelsAt init ω s)) s := by
  unfold seedActivationBulkFailure
  rw [Set.mem_setOf_eq]

theorem mem_seedMarkedShapeFailure_iff (init : InputCfg n) (ell s : ℕ) (ω : InputLog n) :
    ω ∈ seedMarkedShapeFailure init ell s ↔
      ω ∈ markedShapeFailure init (clockSet (labelsAt init ω s)) ell s := by
  unfold seedMarkedShapeFailure
  rw [Set.mem_setOf_eq]

theorem mem_seedCoarseBulkFailure_iff (init : InputCfg n) (ell s : ℕ) (ω : InputLog n) :
    ω ∈ seedCoarseBulkFailure init ell s ↔
      ω ∈ coarseBulkFailure init (clockSet (labelsAt init ω s)) ell s := by
  unfold seedCoarseBulkFailure
  rw [Set.mem_setOf_eq]

theorem mem_seedRareChainFailure_iff (init : InputCfg n) (s : ℕ) (ω : InputLog n) :
    ω ∈ seedRareChainFailure init s ↔
      ω ∈ rareChainFamilyFailure init (clockSet (labelsAt init ω s)).card s (clockCap n) := by
  unfold seedRareChainFailure
  rw [Set.mem_setOf_eq]

theorem canonical_front_packet_of_local_good (init : InputCfg n)
    (hn : populationThreshold ≤ n) (ω : InputLog n) (s T : ℕ)
    (hT : T ≤ earlyHorizon n) (he : AsyncEntry init ω s T)
    (hw : PassageTimes init ω s (virtualTimes init ω s))
    (hgood : ω ∉ jointLocalFailure init s) :
    CanonicalFrontPacket init ω s T := by
  have hseed : ω ∈ seedPrefix init s :=
    ⟨(seedTime_eq_iff init 3 ω s).2 he.first_phase_seed, he.seed_profile⟩
  have hcard := seedPrefix_card_eq init ω s hseed
  have hg : ω ∉ rawFamilyFailure init s ∧
      ω ∉ seedCountActivationFailure init s ∧
      ω ∉ markedFamilyFailure init s ∧
      ω ∉ seedActivationBulkFailure init s ∧
      ω ∉ coarseFamilyFailure init s ∧ ω ∉ seedRareChainFailure init s := by
    simpa only [jointLocalFailure, Set.mem_union, not_or] using hgood
  have hr : RawLocalRow init (virtualTimes init ω s) := by
    intro ell hell htop
    by_contra hnot
    have hbad : ω ∈ rawLocalFailureAt init s :=
      ⟨hseed.1, hseed.2, T, virtualTimes init ω s, hT, he, hw.levels,
        fun h => hnot (h ell hell htop)⟩
    exact hg.1 (rawLocalFailureAt_subset init s hcard hbad).2
  let C := clockSet (labelsAt init ω s)
  have hC := clockMask_card_eq_virtual_seed init C s ω hseed rfl
  have hsafe := shapeSafeAt_of_asyncEntry init C s T ω hseed rfl he
  have hbulk (ell : ℕ) (hell : 1 ≤ ell) (htop : ell ≤ clockCap n) :
      firstAfter (fun v => bulkThreshold C.card ≤
        PhaseThreeClockGatedLaw.frontCount (virtualLabels init ω v) ell)
        s ((virtualTimes init ω s).bulk ell) := by
    have hh := current_firstAfter_of_core init ω s T ell _
      ((virtualTimes init ω s).bulk ell) hseed he (hw.levels.2 ell hell htop)
    have hC' : StageEventSpec.clockCount (virtualCfg init ω s) = C.card := hC.symm
    simpa only [hC'] using hh
  refine ⟨hw, hr, ?_⟩
  apply joint_core_fields_of_local_good init hn C s T (virtualTimes init ω s) ω
    he rfl hw.levels hw.hours.1 hr
  · exact fun h => hg.2.1 ((mem_seedCountActivationFailure_iff init s ω).2 h)
  · intro ell hell htop
    intro hb
    apply hg.2.2.1
    exact Set.mem_iUnion.mpr ⟨ell,
      Set.mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hell, by omega⟩,
        (mem_seedMarkedShapeFailure_iff init ell s ω).2 hb⟩⟩
  · have ha := macroscopicTime_eq_activationFirst init s
      (virtualTimes init ω s).activation ω hcard hw.hours.1
    have hb := activation_bulk_contacts_le init C s (virtualTimes init ω s).activation
      ((virtualTimes init ω s).bulk 1) ω ha
      (hsafe _ (hbulk 1 (by omega) (by unfold clockCap clockHours; omega)).1)
      (hbulk 1 (by omega) (by unfold clockCap clockHours; omega))
      (fun h => hg.2.2.2.1 ((mem_seedActivationBulkFailure_iff init s ω).2 h))
    omega
  · intro ell hell htop
    apply coarse_bulk_contacts_of_good init C ell s
      ((virtualTimes init ω s).bulk ell) ((virtualTimes init ω s).bulk (ell + 1)) ω
      (hsafe _ (hbulk (ell + 1) (by omega) (by omega)).1)
      (hbulk ell hell htop.le) (hbulk (ell + 1) (by omega) (by omega))
    intro hb
    apply hg.2.2.2.2.1
    exact Set.mem_iUnion.mpr ⟨ell,
      Set.mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hell, by omega⟩,
        (mem_seedCoarseBulkFailure_iff init ell s ω).2 hb⟩⟩
  · exact fun h => hg.2.2.2.2.2 ((mem_seedRareChainFailure_iff init s ω).2 h)

def jointEntryFailure (init : InputCfg n) : Set (InputLog n) :=
  {ω | ∃ s T : ℕ, seedTime init 3 ω = (s : WithTop ℕ) ∧
    T ≤ earlyHorizon n ∧ AsyncEntry init ω s T ∧ ω ∈ jointLocalFailure init s}

theorem joint_entry_global_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) :
    law init (jointEntryFailure init) ≤ ENNReal.ofReal (jointError n) := by
  by_cases hcard : init.card = n
  · apply splice_of_local (law init) (seedTime init 3) (jointEntryFailure init) _
      (fun s => (pairLogFiltration _ _).le s _ (seedTime_pastTime init 3 s))
    · rintro ω ⟨s, T, hs, -, -, -⟩
      rw [hs]
      exact WithTop.coe_ne_top
    · intro s
      apply (measure_mono ?_).trans
        ((joint_local_prefix_tail init hn hcard s (seedPrefix init s)
          (seedPrefix_measurable init s) (fun _ h => h)).trans
          (mul_le_mul_left' (measure_mono (show seedPrefix init s ⊆
            {ω | seedTime init 3 ω = (s : WithTop ℕ)} from fun _ h => h.1)) _))
      rintro ω ⟨⟨u, T, hu, -, he, hb⟩, hs⟩
      have hus : u = s := WithTop.coe_injective (hu.symm.trans hs)
      subst u
      exact ⟨⟨hs, he.seed_profile⟩, hb⟩
  · have he : jointEntryFailure init = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨s, T, hs, -, he, -⟩
      exact hcard (seedPrefix_card_eq init ω s ⟨hs, he.seed_profile⟩)
    rw [he, measure_empty]
    exact zero_le

theorem canonical_front_packet_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) :
    law init (rowFailure init (CanonicalFrontPacket init)) ≤
      ENNReal.ofReal (jointError n) := by
  have hsub : rowFailure init (CanonicalFrontPacket init) ⊆
      jointEntryFailure init ∪ rowFailure init
        (fun ω s _T => PassageTimes init ω s (virtualTimes init ω s)) := by
    rintro ω ⟨s, T, hs, hT, he, hb⟩
    by_cases hw : PassageTimes init ω s (virtualTimes init ω s)
    · left
      refine ⟨s, T, hs, hT, he, ?_⟩
      by_contra hgood
      exact hb (canonical_front_packet_of_local_good init hn ω s T hT he hw hgood)
    · exact Or.inr ⟨s, T, hs, hT, he, hw⟩
  calc
    _ ≤ law init _ := measure_mono hsub
    _ ≤ law init (jointEntryFailure init) +
        law init (rowFailure init
          (fun ω s _T => PassageTimes init ω s (virtualTimes init ω s))) :=
      measure_union_le _ _
    _ = law init (jointEntryFailure init) := by
      rw [canonical_passages_null_of_threshold init hn, add_zero]
    _ ≤ _ := joint_entry_global_tail init hn

theorem canonical_front_fields_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) :
    law init (rowFailure init
      (fun ω s _T => JointFrontFields init ω s (virtualTimes init ω s))) ≤
        ENNReal.ofReal (jointError n) := by
  apply (measure_mono ?_).trans (canonical_front_packet_tail init hn)
  rintro ω ⟨s, T, hs, hT, he, hb⟩
  exact ⟨s, T, hs, hT, he, fun h => hb h.joint⟩

theorem finePassages_of_passages (init : InputCfg n) (ω : InputLog n)
    (s : ℕ) (w : ClockTimes init) (hw : PassageTimes init ω s w) :
    FinePassages init ω s w :=
  ⟨hw.hours.1, fun ell hell htop => ⟨hw.levels.1 ell hell htop, hw.levels.2 ell hell htop⟩⟩

theorem passage_row_of_packet_and_fine (init : InputCfg n) (hn : 1 ≤ n)
    (ω : InputLog n) (s T : ℕ) (he : AsyncEntry init ω s T)
    (hp : CanonicalFrontPacket init ω s T) (hf : FineAfterTicks init ω s T) :
    passageRow init ω s T := by
  have hseed : ω ∈ seedPrefix init s :=
    ⟨(seedTime_eq_iff init 3 ω s).2 he.first_phase_seed, he.seed_profile⟩
  have hord := passage_order_rows init hn ω s T (virtualTimes init ω s)
    hseed he hp.passages
  have hraw := hf (finePassages_of_passages init ω s _ hp.passages) hp.joint.tick_local
  exact
    { level_first := hp.passages.levels.1
      level_bulk := hp.passages.levels.2
      start_positive := hp.passages.hours.2.2.1
      finish_first := hp.passages.hours.2.2.2
      cap_first := hp.passages.cap
      activation_before_cap := hord.1
      level_before_cap := hord.2.2.1
      hour_before_cap := hord.2.2.2
      raw_local := hp.raw_local
      fine_raw_local := hraw }

theorem joint_spare_budget {n : ℕ} (hn : 2 ≤ n) :
    jointError n + 4 / (n : ℝ) ^ 98 ≤ 2 / (n : ℝ) ^ 10 ∧
      2 / (n : ℝ) ^ 10 ≤ 1 / (n : ℝ) ^ 8 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  have hpow : (8 : ℝ) ≤ (n : ℝ) ^ 88 :=
    (by norm_num : (8 : ℝ) ≤ 2 ^ 88).trans
      (pow_le_pow_left₀ (by norm_num) hnR 88)
  have hsmall : (8 : ℝ) / (n : ℝ) ^ 98 ≤ 1 / (n : ℝ) ^ 10 := by
    have h98 : (n : ℝ) ^ 98 = (n : ℝ) ^ 10 * (n : ℝ) ^ 88 := by rw [← pow_add]
    rw [div_le_div_iff₀ (by positivity) (by positivity), h98]
    nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 10)]
  constructor
  · unfold jointError
    have e1 : (4 : ℝ) / (n : ℝ) ^ 98 + 4 / (n : ℝ) ^ 98 = 8 / (n : ℝ) ^ 98 := by ring
    have e2 : (2 : ℝ) / (n : ℝ) ^ 10 = 1 / (n : ℝ) ^ 10 + 1 / (n : ℝ) ^ 10 := by ring
    linarith only [hsmall, e1, e2]
  · have htwo : (2 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith only [hnR]
    have h10 : (n : ℝ) ^ 10 = (n : ℝ) ^ 8 * (n : ℝ) ^ 2 := by rw [← pow_add]
    rw [div_le_div_iff₀ (by positivity) (by positivity), h10]
    nlinarith [mul_le_mul_of_nonneg_left htwo (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 8)]

/-- A complete actual passage row bound; the guarded field follows by inclusion. -/
theorem passage_row_tail (init : InputCfg n) (hn : populationThreshold ≤ n) :
    law init (rowFailure init (passageRow init)) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 8) := by
  have hlarge := (strong_bulk_family_calibration hn).1
  have hsub : rowFailure init (passageRow init) ⊆
      rowFailure init (CanonicalFrontPacket init) ∪
        rowFailure init (FineAfterTicks init) := by
    rintro ω ⟨s, T, hs, hT, he, hb⟩
    by_cases hp : CanonicalFrontPacket init ω s T
    · right
      exact ⟨s, T, hs, hT, he, fun hf =>
        hb (passage_row_of_packet_and_fine init (by omega) ω s T he hp hf)⟩
    · exact Or.inl ⟨s, T, hs, hT, he, hp⟩
  calc
    _ ≤ law init _ := measure_mono hsub
    _ ≤ law init (rowFailure init (CanonicalFrontPacket init)) +
        law init (rowFailure init (FineAfterTicks init)) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (jointError n) + ENNReal.ofReal (1 / (n : ℝ) ^ 98) :=
      add_le_add (canonical_front_packet_tail init hn) (fine_after_ticks_row_tail init hn)
    _ = ENNReal.ofReal (jointError n + 1 / (n : ℝ) ^ 98) := by
      rw [ENNReal.ofReal_add (by unfold jointError; positivity) (by positivity)]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hb := joint_spare_budget (n := n) (by omega)
      have hz : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 98 := by positivity
      have e4 : (4 : ℝ) / (n : ℝ) ^ 98 = 4 * (1 / (n : ℝ) ^ 98) := by ring
      linarith only [hb.1, hb.2, hz, e4]

theorem guarded_passage_row_tail (init : InputCfg n) (hn : populationThreshold ≤ n) :
    law init (guardedFailure init (guardPassage init) (passageRow init)) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 8) := by
  apply (measure_mono ?_).trans (passage_row_tail init hn)
  rintro ω ⟨s, T, hs, hT, he, -, hb⟩
  exact ⟨s, T, hs, hT, he, hb⟩

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockJointCanonicalTails

end
