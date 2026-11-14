-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockGuardedInitialTails.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockJointCanonicalTails
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockHighRows
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockHourTickAssembly
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockLowerPassageRows
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockCapDeadlineTail
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockContactTail

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockGuardedInitialTails

open PhaseThreeClockProducer PhaseThreeClockActivationSeed

open TimeTheorem PairLog StageEventSpec PhaseThreeModel.Numeric
  PhaseThreeClockProducer PhaseThreeClockVirtual PhaseThreeClockCore
  PhaseThreeClockRows PhaseThreeClockRowsGuarded PhaseThreeClockSeedTails
  PhaseThreeClockActivationSeed PhaseThreeClockRawLocalRow
  PhaseThreeClockPassageOrderRows PhaseThreeClockInitializationRows
  PhaseThreeClockJointCore PhaseThreeClockJointLocalTails
  PhaseThreeClockJointCanonicalTails PhaseThreeClockBulkShapeBudget
  PhaseThreeClockBeforeTwentyRows PhaseThreeClockHourThinningRows
  PhaseThreeClockHighFibres PhaseThreeClockHighRows PhaseThreeClockHourTickAssembly
  PhaseThreeClockLowerPassageRows

variable {n : ℕ}

def HighFamilyGood (init : InputCfg n) (ω : InputLog n) (s : ℕ) (_T : ℕ) : Prop :=
  ω ∉ allHighFailure init s

theorem high_family_global_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) :
    law init (rowFailure init (HighFamilyGood init)) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 98) := by
  classical
  apply splice_of_local (law init) (seedTime init 3)
    (rowFailure init (HighFamilyGood init)) _
    (fun s => (pairLogFiltration _ _).le s _ (seedTime_pastTime init 3 s))
  · rintro ω ⟨s, T, hs, -, -, -⟩
    rw [hs]
    exact WithTop.coe_ne_top
  · intro s
    apply (measure_mono ?_).trans
      ((all_high_prefix_tail init hn s (seedPrefix init s)
        (seedPrefix_measurable init s) (fun _ h => h)).trans
        (mul_le_mul_left' (measure_mono (show seedPrefix init s ⊆
          {ω | seedTime init 3 ω = (s : WithTop ℕ)} from fun _ h => h.1)) _))
    rintro ω ⟨⟨u, T, hu, -, he, hb⟩, hs⟩
    have hus : u = s := WithTop.coe_injective (hu.symm.trans hs)
    subst u
    exact ⟨⟨hs, he.seed_profile⟩, by simpa only [HighFamilyGood, not_not] using hb⟩

theorem twentyPassages_of_passages (init : InputCfg n) (ω : InputLog n)
    (s : ℕ) (w : ClockTimes init) (hp : PassageTimes init ω s w) :
    TwentyPassages init ω s w where
  activation_first := hp.hours.1
  bulk_one := hp.levels.2 1 (by omega) (by unfold clockTop; omega)
  bulk_twenty := hp.levels.2 20 (by omega) (by unfold clockTop; omega)

theorem activation_row_of_packet_lower_twenty (init : InputCfg n)
    (hn : 1 ≤ n) (ω : InputLog n) (s T : ℕ)
    (he : AsyncEntry init ω s T) (hp : CanonicalFrontPacket init ω s T)
    (hlower : ∀ i, 1 ≤ i → i < clockTop n →
      (2 / 5 : ℝ) * (clockCount (virtualCfg init ω s) : ℝ) ≤
        (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
          ((virtualTimes init ω s).bulk i) ((virtualTimes init ω s).bulk (i + 1)) : ℝ))
    (hconvert : BeforeTwentyAfterTicks init ω s T) :
    activationRow init ω s T := by
  have hbefore := hconvert (twentyPassages_of_passages init ω s _ hp.passages)
    (lower_twenty_ticks_of_positive init ω s _ hp.passages.levels hlower)
  exact activation_row_of_before_twenty init hn ω s T
    ⟨(seedTime_eq_iff init 3 ω s).2 he.first_phase_seed, he.seed_profile⟩
    he hp.passages hbefore

theorem shape_row_of_packet_lower_high_raw (init : InputCfg n)
    (hn : populationThreshold ≤ n) (ω : InputLog n) (s T : ℕ)
    (he : AsyncEntry init ω s T) (hp : CanonicalFrontPacket init ω s T)
    (hact : activationRow init ω s T)
    (hlower : ∀ i, 1 ≤ i → i < clockTop n →
      (2 / 5 : ℝ) * (clockCount (virtualCfg init ω s) : ℝ) ≤
        (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
          ((virtualTimes init ω s).bulk i) ((virtualTimes init ω s).bulk (i + 1)) : ℝ))
    (hhigh : HighFamilyGood init ω s T)
    (hraw : RawWidthAfterTicks init ω s T) :
    shapeRow init ω s T := by
  have hseed : ω ∈ seedPrefix init s :=
    ⟨(seedTime_eq_iff init 3 ω s).2 he.first_phase_seed, he.seed_profile⟩
  have hlarge := (strong_bulk_family_calibration hn).1
  have hwidth := high_width_of_good init ω s T (virtualTimes init ω s)
    he hp.passages.levels hp.joint hlower hhigh
  have hupper := high_hour_ticks_of_good init ω s T (virtualTimes init ω s)
    he hp.passages.levels hp.passages.hours hhigh
  have hlowerHour := lower_hour_ticks_of_passages init hn ω s T (virtualTimes init ω s)
    hseed he hp.passages.levels hp.passages.hours hp.joint
    hact.activation_before_twenty hlower hupper
  exact rowShape_of_joint_high_raw init (by omega) ω s T (virtualTimes init ω s)
    hseed he hp.passages.hours hp.joint hwidth (hraw hp.passages.hours hlowerHour)

theorem joint_four_spares_ennreal {n : ℕ} (hn : 2 ≤ n) :
    ENNReal.ofReal (jointError n) + 4 * ENNReal.ofReal (1 / (n : ℝ) ^ 98) ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 10) := by
  have he :
      ENNReal.ofReal (jointError n) + 4 * ENNReal.ofReal (1 / (n : ℝ) ^ 98) =
        ENNReal.ofReal (jointError n + 4 / (n : ℝ) ^ 98) := by
    rw [show (4 : ℝ) / (n : ℝ) ^ 98 = 4 * (1 / (n : ℝ) ^ 98) by ring,
      ENNReal.ofReal_add (by unfold jointError; positivity) (by positivity),
      ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [he]
  exact ENNReal.ofReal_le_ofReal (joint_spare_budget hn).1

theorem joint_four_spares_eighth {n : ℕ} (hn : 2 ≤ n) :
    ENNReal.ofReal (jointError n) + 4 * ENNReal.ofReal (1 / (n : ℝ) ^ 98) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 8) :=
  (joint_four_spares_ennreal hn).trans
    (ENNReal.ofReal_le_ofReal (joint_spare_budget hn).2)

theorem activation_row_tail (init : InputCfg n) (hn : populationThreshold ≤ n) :
    law init (rowFailure init (activationRow init)) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 8) := by
  have hlarge := (strong_bulk_family_calibration hn).1
  have hsub : rowFailure init (activationRow init) ⊆
      rowFailure init (CanonicalFrontPacket init) ∪
        (rowFailure init (LowerAfterJoint init) ∪
          rowFailure init (BeforeTwentyAfterTicks init)) := by
    rintro ω ⟨s, T, hs, hT, he, hb⟩
    by_cases hp : CanonicalFrontPacket init ω s T
    · by_cases hl : LowerAfterJoint init ω s T
      · right
        right
        exact ⟨s, T, hs, hT, he, fun ht =>
          hb (activation_row_of_packet_lower_twenty init (by omega) ω s T he hp
            (hl hp.passages.levels hp.joint) ht)⟩
      · exact Or.inr (Or.inl ⟨s, T, hs, hT, he, hl⟩)
    · exact Or.inl ⟨s, T, hs, hT, he, hp⟩
  have hshort : ENNReal.ofReal (1 / (n : ℝ) ^ 99) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 98) := by
    simpa only [Nat.cast_one, one_mul] using
      spare_family_coefficient 1 n (by omega) (by omega)
  calc
    _ ≤ law init _ := measure_mono hsub
    _ ≤ law init (rowFailure init (CanonicalFrontPacket init)) +
        (law init (rowFailure init (LowerAfterJoint init)) +
          law init (rowFailure init (BeforeTwentyAfterTicks init))) :=
      (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ ENNReal.ofReal (jointError n) +
        (ENNReal.ofReal (1 / (n : ℝ) ^ 98) +
          ENNReal.ofReal (1 / (n : ℝ) ^ 99)) :=
      add_le_add (canonical_front_packet_tail init hn)
        (add_le_add (lower_after_joint_row_tail init hn)
          (before_twenty_after_ticks_row_tail init hn))
    _ ≤ ENNReal.ofReal (jointError n) +
        (ENNReal.ofReal (1 / (n : ℝ) ^ 98) +
          ENNReal.ofReal (1 / (n : ℝ) ^ 98)) :=
      add_le_add le_rfl (add_le_add le_rfl hshort)
    _ = ENNReal.ofReal (jointError n) +
        2 * ENNReal.ofReal (1 / (n : ℝ) ^ 98) := by ring
    _ ≤ ENNReal.ofReal (jointError n) +
        4 * ENNReal.ofReal (1 / (n : ℝ) ^ 98) := by gcongr <;> norm_num
    _ ≤ _ := joint_four_spares_eighth (by omega)

theorem guarded_shape_row_tail (init : InputCfg n) (hn : populationThreshold ≤ n) :
    law init (guardedFailure init (guardShape init) (shapeRow init)) ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 10) := by
  have hlarge := (strong_bulk_family_calibration hn).1
  have hsub : guardedFailure init (guardShape init) (shapeRow init) ⊆
      rowFailure init (CanonicalFrontPacket init) ∪
        (rowFailure init (LowerAfterJoint init) ∪
          (rowFailure init (HighFamilyGood init) ∪
            rowFailure init (RawWidthAfterTicks init))) := by
    rintro ω ⟨s, T, hs, hT, he, hguard, hb⟩
    by_cases hp : CanonicalFrontPacket init ω s T
    · by_cases hl : LowerAfterJoint init ω s T
      · by_cases hh : HighFamilyGood init ω s T
        · right
          right
          right
          exact ⟨s, T, hs, hT, he, fun hr =>
            hb (shape_row_of_packet_lower_high_raw init hn ω s T he hp hguard.1
              (hl hp.passages.levels hp.joint) hh hr)⟩
        · exact Or.inr (Or.inr (Or.inl ⟨s, T, hs, hT, he, hh⟩))
      · exact Or.inr (Or.inl ⟨s, T, hs, hT, he, hl⟩)
    · exact Or.inl ⟨s, T, hs, hT, he, hp⟩
  calc
    _ ≤ law init _ := measure_mono hsub
    _ ≤ law init (rowFailure init (CanonicalFrontPacket init)) +
        (law init (rowFailure init (LowerAfterJoint init)) +
          (law init (rowFailure init (HighFamilyGood init)) +
            law init (rowFailure init (RawWidthAfterTicks init)))) := by
      refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
      exact (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ ENNReal.ofReal (jointError n) +
        (ENNReal.ofReal (1 / (n : ℝ) ^ 98) +
          (ENNReal.ofReal (1 / (n : ℝ) ^ 98) +
            ENNReal.ofReal (1 / (n : ℝ) ^ 98))) :=
      add_le_add (canonical_front_packet_tail init hn)
        (add_le_add (lower_after_joint_row_tail init hn)
          (add_le_add (high_family_global_tail init hn)
            (raw_width_after_ticks_row_tail init hn)))
    _ = ENNReal.ofReal (jointError n) +
        3 * ENNReal.ofReal (1 / (n : ℝ) ^ 98) := by ring
    _ ≤ ENNReal.ofReal (jointError n) +
        4 * ENNReal.ofReal (1 / (n : ℝ) ^ 98) := by gcongr <;> norm_num
    _ ≤ _ := joint_four_spares_ennreal (by omega)

/-- The three requested actual fields of the compiled guarded row interface. -/
structure StepThreeRowTails (init : InputCfg n) : Prop where
  activation : law init (rowFailure init (activationRow init)) ≤
    ENNReal.ofReal (1 / (n : ℝ) ^ 8)
  passage : law init (guardedFailure init (guardPassage init) (passageRow init)) ≤
    ENNReal.ofReal (1 / (n : ℝ) ^ 8)
  shape : law init (guardedFailure init (guardShape init) (shapeRow init)) ≤
    ENNReal.ofReal (2 / (n : ℝ) ^ 10)

theorem step_three_row_tails (init : InputCfg n) (hn : populationThreshold ≤ n) :
    StepThreeRowTails init where
  activation := activation_row_tail init hn
  passage := guarded_passage_row_tail init hn
  shape := guarded_shape_row_tail init hn


/-- The complete compiled guarded interface, with only the independently
owned Main row left as an input.  The step-three fields above are proved
from the protocol law; they are not assumptions of this theorem. -/
theorem guarded_row_tails_of_main (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (hmain : law init (guardedFailure init (guardMain init) (mainRow init)) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 29)) :
    GuardedRowTails init := by
  have hn : populationThreshold ≤ n := (time_population_bounds hinput.1).1
  have hstep := step_three_row_tails init hn
  refine ⟨hstep.activation, hstep.passage, hstep.shape,
    PhaseThreeClockCapDeadlineTail.guarded_cap_tail init hinput, hmain, ?_⟩
  simpa only [guardedFailure, guardMain,
    PhaseThreeClockContactTail.guardedContactFailure, and_assoc] using
      PhaseThreeClockContactTail.guarded_contact_tail init hinput

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockGuardedInitialTails

end
