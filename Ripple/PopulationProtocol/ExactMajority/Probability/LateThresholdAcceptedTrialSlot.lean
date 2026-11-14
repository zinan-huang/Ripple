-- Ripple/PopulationProtocol/ExactMajority/Probability/LateThresholdAcceptedTrialSlot.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateThresholdAcceptedCounterCoupling

/-!
# Threshold-aware accepted-trial zero slot

This file supersedes `LateAcceptedTrialSlot` for row two.  It preserves the
same finite family and unconditional stopping-line charge, but uses the
corrected counter and an explicit terminal-to-horizon retention theorem.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateThresholdAcceptedTrialSlot

open TimeTheorem PairLog PairLogAuxiliary
open AveragingRecordedExpectation LateSamplingScalar
open LateF6Acceptance LateF6Hazards LateF6OriginalLaw
open LateSamplingCounterTail LateAcceptedTrialTail
open LateAcceptedRectangleHazard LateSamplingClassGates
open LateAcceptedCounterCoupling LateAcceptedTrialSlot
open LateSamplingCalibration LateSamplingEarlyRoles LateSamplingSplice
open LateSamplingFirstHit LateFrozenPoolTail LateFrozenPoolOriginalLaw
open LateSamplingRowTwoCounterRepair
open LateThresholdAcceptedCounterCoupling

variable {L K n : ℕ}

/-- Recorded-future exponential estimate for the repaired counter. -/
theorem recorded_threshold_accepted_trial_tail
    (init : Cfg L K) (hn : 2 ≤ init.card)
    (s k M A : ℕ) (J : Finset (Fin (L + 1)))
    (γ : ℝ) (hM : 0 < M) (hA : A ≤ M)
    (hγ : 0 ≤ γ) (hγA : γ ≤ (A : ℝ) / M)
    (p : (i : Finset.Iic s) → Draw L K)
    (m N : ℕ) :
    recordedFuture init s p
      (acceptedTrialFailureOf
        (thresholdAcceptedCounter init s k M A J γ)
        (acceptedBadRate M A γ) γ m N) ≤
      ENNReal.ofReal (Real.exp (-2 * γ ^ 2 * m)) := by
  let Q := thresholdAcceptedCounter init s k M A J γ
  have htail := CounterSpec.constant_tail Q hn (acceptedBadRate M A γ) γ
    (acceptedBadRate_nonneg hM hA hγ) hγ
    (thresholdAcceptedCounter_hazard init hn s k M A J γ
      hM hA hγ hγA)
    p m N
  have heq : acceptedTrialFailureOf Q (acceptedBadRate M A γ) γ m N =
      {ω | m ≤ eventCount Q.eventTrial N ω ∧
        (acceptedBadRate M A γ + γ) * eventCount Q.eventTrial N ω ≤
          badCount Q.badTrial N ω} := by
    ext ω
    change ((m : ℝ) ≤ (Q.state ω (Q.start + N)).1 ∧
      (acceptedBadRate M A γ + γ) * (Q.state ω (Q.start + N)).1 ≤
        (Q.state ω (Q.start + N)).2.1) ↔
      ((m : ℝ) ≤ eventCount Q.eventTrial N ω ∧
        (acceptedBadRate M A γ + γ) * eventCount Q.eventTrial N ω ≤
          badCount Q.badTrial N ω)
    rw [Q.eventCount_eq, CounterSpec.badCount_eq Q]
  rw [heq]
  exact htail

/-- Corrected zero-slot event. -/
def thresholdAcceptedTrialSlotEvent
    (init : Cfg L K) (s M R : ℕ)
    (A : Fin (M + 1)) (J : Finset (Fin (L + 1))) (N : ℕ) : Set (Ω L K) :=
  let k := Nat.ceil ((init.card : ℝ) / 1000000)
  if 0 < M ∧
      (1 / 40000 : ℝ) ≤ (A.val : ℝ) / M ∧
      2 * k ≤ R then
    acceptedTrialFailureOf
      (thresholdAcceptedCounter init s k M A.val J (1 / 40000))
      (acceptedBadRate M A.val (1 / 40000)) (1 / 40000)
      (R - k) N
  else ∅

theorem thresholdAcceptedTrialSlotEvent_measurable
    (init : Cfg L K) (s M R : ℕ)
    (A : Fin (M + 1)) (J : Finset (Fin (L + 1))) (N : ℕ) :
    MeasurableSet (thresholdAcceptedTrialSlotEvent init s M R A J N) := by
  unfold thresholdAcceptedTrialSlotEvent
  dsimp only
  split_ifs
  · exact acceptedTrialFailureOf_measurable _ _ _ _ _
  · exact MeasurableSpace.measurableSet_empty _

/-- Every corrected zero slot has the same exponential charge as before. -/
theorem recorded_threshold_accepted_trial_slot_tail
    (init : Cfg L K) (hn : 2 ≤ init.card)
    (s M R : ℕ) (A : Fin (M + 1))
    (J : Finset (Fin (L + 1))) (N : ℕ)
    (p : (i : Finset.Iic s) → Draw L K) :
    recordedFuture init s p
      (thresholdAcceptedTrialSlotEvent init s M R A J N) ≤
      ENNReal.ofReal
        (Real.exp (-(init.card : ℝ) / 800000000000000)) := by
  unfold thresholdAcceptedTrialSlotEvent
  dsimp only
  split_ifs with hv
  · rcases hv with ⟨hM, hγA, hR⟩
    have hA : A.val ≤ M := by have := A.isLt; omega
    have htail := recorded_threshold_accepted_trial_tail init hn s
      (Nat.ceil ((init.card : ℝ) / 1000000)) M A.val J
      (1 / 40000) hM hA (by norm_num) hγA p
      (R - Nat.ceil ((init.card : ℝ) / 1000000)) N
    have hm :
        (Nat.ceil ((init.card : ℝ) / 1000000) : ℝ) ≤
          (R - Nat.ceil ((init.card : ℝ) / 1000000) : ℕ) := by
      exact_mod_cast (show Nat.ceil ((init.card : ℝ) / 1000000) ≤
        R - Nat.ceil ((init.card : ℝ) / 1000000) by omega)
    have hcal := frozen_hoeffding_exponent init.card
    have hexp :
        -2 * (1 / 40000 : ℝ) ^ 2 *
            (R - Nat.ceil ((init.card : ℝ) / 1000000) : ℕ) ≤
          -(init.card : ℝ) / 800000000000000 := by
      nlinarith
    exact htail.trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexp))
  · rw [measure_empty]
    exact zero_le

/-- Replace exactly the zero frozen-prefix slot by the corrected trial. -/
def testEventWithThresholdAccepted
    (init : Cfg L K) (s M R : ℕ)
    (C : Fin 3 → Bias L → Prop)
    (J : Fin 3 → Fin (M + 1) → Finset (Fin (L + 1)))
    (N : Fin 3 → Fin (M + 1) → ℕ) :
    ClassTestIndex M → Set (Ω L K)
  | none => EarlyRoleEvent init s M R
      (Nat.ceil ((init.card : ℝ) / 1000000))
  | some (i, A, k) =>
      if k.val = 0 then
        thresholdAcceptedTrialSlotEvent init s M R A (J i A) (N i A)
      else
        LateFrozenPoolOriginalLaw.testEvent init s M R C (some (i, A, k))

@[simp] theorem testEventWithThresholdAccepted_none
    (init : Cfg L K) (s M R : ℕ)
    (C : Fin 3 → Bias L → Prop)
    (J : Fin 3 → Fin (M + 1) → Finset (Fin (L + 1)))
    (N : Fin 3 → Fin (M + 1) → ℕ) :
    testEventWithThresholdAccepted init s M R C J N none =
      EarlyRoleEvent init s M R
        (Nat.ceil ((init.card : ℝ) / 1000000)) := rfl

@[simp] theorem testEventWithThresholdAccepted_zero
    (init : Cfg L K) (s M R : ℕ)
    (C : Fin 3 → Bias L → Prop)
    (J : Fin 3 → Fin (M + 1) → Finset (Fin (L + 1)))
    (N : Fin 3 → Fin (M + 1) → ℕ)
    (i : Fin 3) (A : Fin (M + 1)) :
    testEventWithThresholdAccepted init s M R C J N
        (some (i, A, ⟨0, Nat.zero_lt_succ M⟩)) =
      thresholdAcceptedTrialSlotEvent init s M R A (J i A) (N i A) := by
  simp [testEventWithThresholdAccepted]

 theorem testEventWithThresholdAccepted_positive
    (init : Cfg L K) (s M R : ℕ)
    (C : Fin 3 → Bias L → Prop)
    (J : Fin 3 → Fin (M + 1) → Finset (Fin (L + 1)))
    (N : Fin 3 → Fin (M + 1) → ℕ)
    (i : Fin 3) (A k : Fin (M + 1)) (hk : 0 < k.val) :
    testEventWithThresholdAccepted init s M R C J N (some (i, A, k)) =
      LateFrozenPoolOriginalLaw.testEvent init s M R C (some (i, A, k)) := by
  simp [testEventWithThresholdAccepted, Nat.ne_of_gt hk]

theorem testEventWithThresholdAccepted_measurable
    (init : Cfg L K) (s M R : ℕ)
    (C : Fin 3 → Bias L → Prop)
    (J : Fin 3 → Fin (M + 1) → Finset (Fin (L + 1)))
    (N : Fin 3 → Fin (M + 1) → ℕ)
    (x : ClassTestIndex M) :
    MeasurableSet (testEventWithThresholdAccepted init s M R C J N x) := by
  cases x with
  | none => exact earlyRoleEvent_measurable init s M R _
  | some z =>
      rcases z with ⟨i, A, k⟩
      unfold testEventWithThresholdAccepted
      dsimp only
      split_ifs
      · exact thresholdAcceptedTrialSlotEvent_measurable init s M R A
          (J i A) (N i A)
      · exact LateFrozenPoolOriginalLaw.testEvent_measurable init s M R C _

/-- Per-index tail for the repaired finite family. -/
theorem recorded_testEventWithThresholdAccepted_tail
    (init : Cfg L K) (s M R : ℕ)
    (hd : SeedDensity init.card M R)
    (hlog : (45 : ℝ) ≤ Real.log (init.card : ℝ))
    (C : Fin 3 → Bias L → Prop)
    (J : Fin 3 → Fin (M + 1) → Finset (Fin (L + 1)))
    (N : Fin 3 → Fin (M + 1) → ℕ)
    (p : (i : Finset.Iic s) → Draw L K)
    (x : ClassTestIndex M) :
    recordedFuture init s p
      (testEventWithThresholdAccepted init s M R C J N x) ≤
      ENNReal.ofReal
        (Real.exp (-(init.card : ℝ) / 800000000000000)) := by
  have hlarge := logarithm_population_lower hlog
  have hn : 2 ≤ init.card := by omega
  have hM : 0 < M := by have h := hd.mains_lower; omega
  cases x with
  | none =>
      exact recorded_early_role_tail init s M R hd.mains_lower
        hd.reserves_upper hd.total_le hlog p
  | some z =>
      rcases z with ⟨i, A, k⟩
      by_cases hz : k.val = 0
      · rw [show testEventWithThresholdAccepted init s M R C J N
            (some (i, A, k)) =
          thresholdAcceptedTrialSlotEvent init s M R A (J i A) (N i A) by
            simp [testEventWithThresholdAccepted, hz]]
        exact recorded_threshold_accepted_trial_slot_tail init hn s M R A
          (J i A) (N i A) p
      · rw [testEventWithThresholdAccepted_positive init s M R C J N i A k
          (by omega)]
        unfold LateFrozenPoolOriginalLaw.testEvent
        dsimp only
        split_ifs with hk
        · exact frozen_test_tail init hn init.card s M A.val k.val hM
            (by omega) (by omega) hk (C i) p
        · rw [measure_empty]
          exact zero_le

/-- Finite family with the corrected zero slot. -/
def prerequisiteEventWithThresholdAccepted
    (init : Cfg L K) (s M R : ℕ)
    (C : Fin 3 → Bias L → Prop)
    (J : Fin 3 → Fin (M + 1) → Finset (Fin (L + 1)))
    (N : Fin 3 → Fin (M + 1) → ℕ) : Set (Ω L K) :=
  ⋃ x, testEventWithThresholdAccepted init s M R C J N x

theorem prerequisiteEventWithThresholdAccepted_measurable
    (init : Cfg L K) (s M R : ℕ)
    (C : Fin 3 → Bias L → Prop)
    (J : Fin 3 → Fin (M + 1) → Finset (Fin (L + 1)))
    (N : Fin 3 → Fin (M + 1) → ℕ) :
    MeasurableSet (prerequisiteEventWithThresholdAccepted init s M R C J N) :=
  MeasurableSet.iUnion
    (testEventWithThresholdAccepted_measurable init s M R C J N)

theorem recorded_prerequisites_withThresholdAccepted_tail
    (init : Cfg L K) (s M R : ℕ)
    (hd : SeedDensity init.card M R)
    (hlog : (45 : ℝ) ≤ Real.log (init.card : ℝ))
    (C : Fin 3 → Bias L → Prop)
    (J : Fin 3 → Fin (M + 1) → Finset (Fin (L + 1)))
    (N : Fin 3 → Fin (M + 1) → ℕ)
    (p : (i : Finset.Iic s) → Draw L K) :
    recordedFuture init s p
      (prerequisiteEventWithThresholdAccepted init s M R C J N) ≤
      ENNReal.ofReal ((3 * ((M : ℝ) + 1) ^ 2 + 1) *
        Real.exp (-(init.card : ℝ) / 800000000000000)) := by
  apply class_test_union_bound (recordedFuture init s p) init.card M
    (testEventWithThresholdAccepted init s M R C J N)
  exact recorded_testEventWithThresholdAccepted_tail init s M R hd hlog C J N p

/-- Prefix-selected corrected family. -/
def selectedPrerequisitesWithThresholdAccepted
    (init : InputCfg n) (C : ClassChoice n)
    (J : AcceptedIndexChoice init) (N : AcceptedHorizonChoice init)
    (s : ℕ) (p : InputPrefix n s) : Set (InputLog n) :=
  prerequisiteEventWithThresholdAccepted init s
    (selectedMains init s p) (selectedReserves init s p)
    (C s p) (J s p) (N s p)

/-- Unconditioned original-law failure at the genuine first threshold-four
stopping line. -/
def originalPrerequisiteWithThresholdAcceptedFailure
    (init : InputCfg n) (C : ClassChoice n)
    (J : AcceptedIndexChoice init) (N : AcceptedHorizonChoice init) :
    Set (InputLog n) :=
  {ω | ∃ s : ℕ, firstFourStart init ω = (s : WithTop ℕ) ∧
    ω ∈ selectedFailure s (seedPrefixes init s)
      (selectedPrerequisitesWithThresholdAccepted init C J N s)}

theorem law_prerequisites_withThresholdAccepted_tail
    (init : InputCfg n) (hcard : init.card = n)
    (hn : timePopulationThreshold ≤ n)
    (C : ClassChoice n)
    (J : AcceptedIndexChoice init) (N : AcceptedHorizonChoice init) :
    law init (originalPrerequisiteWithThresholdAcceptedFailure init C J N) ≤
      ENNReal.ofReal (13 * (n : ℝ) ^ 2 *
        Real.exp (-(n : ℝ) / 800000000000000)) := by
  have hlog : (45 : ℝ) ≤ Real.log (init.card : ℝ) := by
    simpa only [hcard] using time_threshold_logarithm hn
  apply law_stopping_selected_bound init (firstFourStart init)
    (firstFourStart_past init)
    (seedPrefixes init) (selectedPrerequisitesWithThresholdAccepted init C J N)
    (fun s p => prerequisiteEventWithThresholdAccepted_measurable init s _ _
      (C s p) (J s p) (N s p))
  intro s p hp
  have hd : SeedDensity init.card (selectedMains init s p)
      (selectedReserves init s p) := hp
  have hM : selectedMains init s p ≤ init.card := by
    have h := hd.total_le
    omega
  have hlocal := recorded_prerequisites_withThresholdAccepted_tail init s _ _
    hd hlog (C s p) (J s p) (N s p) p
  have hpoly := (sampling_finite_factor hM hlog).1
  have hbound := hlocal.trans (ENNReal.ofReal_le_ofReal hpoly)
  simpa only [hcard] using hbound

theorem law_prerequisites_withThresholdAccepted_inverse_power
    (init : InputCfg n) (hcard : init.card = n)
    (hn : timePopulationThreshold ≤ n)
    (C : ClassChoice n)
    (J : AcceptedIndexChoice init) (N : AcceptedHorizonChoice init) :
    law init (originalPrerequisiteWithThresholdAcceptedFailure init C J N) ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-190)) := by
  have hpoly := (sampling_finite_factor (M := n) le_rfl
    (time_threshold_logarithm hn)).2
  exact (law_prerequisites_withThresholdAccepted_tail init hcard hn C J N).trans
    (ENNReal.ofReal_le_ofReal hpoly.le)

private theorem slot_mainCount_le_card
    (f : Fin n → AgentState L K) : mainCount f ≤ n := by
  classical
  have hsub : pool f Main ⊆ (Finset.univ : Finset (Fin n)) :=
    fun _ _ => Finset.mem_univ _
  simpa [mainCount] using Finset.card_le_card hsub

/-- Corrected terminal-time cover, before transport to the fixed horizon. -/
theorem actual_bad_samples_covered_by_early_or_threshold_trial
    {init : InputCfg n} {ω : InputLog n}
    {a s T M R : ℕ}
    (h : Prefix init ω a s T)
    (A : Fin (M + 1))
    (J : Finset (Fin (PhaseThreeModel.Numeric.hourIndex n + 1)))
    (hR : reserveCount (labelsAt init ω s) = R)
    (hvalid : 0 < M ∧
      (1 / 40000 : ℝ) ≤ (A.val : ℝ) / M ∧
      2 * Nat.ceil ((init.card : ℝ) / 1000000) ≤ R)
    (hgate : ∀ u, s ≤ u → u < T →
      ThresholdAcceptedGate
        (Nat.ceil ((init.card : ℝ) / 1000000))
        M A.val J (1 / 40000) (labelsAt init ω u))
    (haccepted : acceptedCount (labelsAt init ω T) = R)
    (hbad :
      (acceptedBadRate M A.val (1 / 40000) + 1 / 40000) * (R : ℝ) +
          Nat.ceil ((init.card : ℝ) / 1000000) ≤
        badSampleCount J (labelsAt init ω T)) :
    ω ∈ EarlyRoleEvent init s M R
        (Nat.ceil ((init.card : ℝ) / 1000000)) ∨
      ω ∈ thresholdAcceptedTrialSlotEvent init s M R A J (T - s) := by
  let k := Nat.ceil ((init.card : ℝ) / 1000000)
  set Q := thresholdAcceptedCounter init s k M A.val J (1 / 40000) with hQ
  by_cases hearly : ω ∈ EarlyRoleEvent init s M R k
  · exact Or.inl hearly
  · right
    have hstart : Q.start = s := rfl
    unfold thresholdAcceptedTrialSlotEvent
    dsimp only
    rw [if_pos hvalid]
    unfold acceptedTrialFailureOf
    by_cases hsT : s < T
    · have hk : 0 < k := by
        have hn : 0 < init.card := by
          have := hvalid.1
          have hm := (hgate s le_rfl hsT).1
          have hmc : mainCount (labelsAt init ω s) ≤ init.card :=
            slot_mainCount_le_card (labelsAt init ω s)
          omega
        apply Nat.ceil_pos.mpr
        positivity
      have hMseed : mainCount (labelsAt init ω s) = M :=
        (hgate s le_rfl hsT).1
      have hcouple :
          acceptedCount (labelsAt init ω T) ≤ (Q.state ω T).1 + k ∧
            badSampleCount J (labelsAt init ω T) ≤ (Q.state ω T).2.1 + k :=
        threshold_actual_counts_le_stopped_add_earlyCap h J (1 / 40000)
          hMseed hR hk hgate hearly T h.observed le_rfl
      have hcountActual : (Q.state ω T).1 ≤
          acceptedCount (labelsAt init ω T) :=
        thresholdAcceptedCounter_count_le_actual h k M A.val J
          (1 / 40000) T h.observed le_rfl
      have hrate :
          0 ≤ acceptedBadRate M A.val (1 / 40000) + 1 / 40000 := by
        have hA : A.val ≤ M := by have := A.isLt; omega
        have hq := acceptedBadRate_nonneg (γ := (1 / 40000 : ℝ))
          hvalid.1 hA (by norm_num)
        norm_num at hq ⊢
        linarith
      have htime : s + (T - s) = T := Nat.add_sub_of_le h.observed
      rw [hstart, htime]
      constructor
      · exact_mod_cast (show R - k ≤ (Q.state ω T).1 by
          rw [haccepted] at hcouple
          omega)
      · have hcountUpper : (Q.state ω T).1 ≤ R := by
          rw [haccepted] at hcountActual
          exact hcountActual
        have hbadLower :
            (acceptedBadRate M A.val (1 / 40000) + 1 / 40000) * (R : ℝ) ≤
              (Q.state ω T).2.1 := by
          have hcoupleBad := hcouple.2
          have hcoupleR : (badSampleCount J (labelsAt init ω T) : ℝ) ≤
              ((Q.state ω T).2.1 : ℝ) + (k : ℝ) := by
            exact_mod_cast hcoupleBad
          linarith
        have hmul := mul_le_mul_of_nonneg_left
          (show ((Q.state ω T).1 : ℝ) ≤ (R : ℝ) by
            exact_mod_cast hcountUpper) hrate
        exact hmul.trans hbadLower
    · have hTs : T = s := le_antisymm (not_lt.mp hsT) h.observed
      have hzero := (prefix_start_counts_zero h).2.1
      have hRzero : R = 0 := by
        rw [← haccepted, hTs]
        exact hzero
      have hkzero : k = 0 := by omega
      have hd : T - s = 0 := by omega
      have hzz :
          (thresholdAcceptedCounter init s
            (Nat.ceil ((init.card : ℝ) / 1000000)) M A.val J
            (1 / 40000)).state ω s = (0, 0, true) :=
        CounterSpec.state_before_start
          (thresholdAcceptedCounter init s
            (Nat.ceil ((init.card : ℝ) / 1000000)) M A.val J
            (1 / 40000)) ω s le_rfl
      have hzzStart :
          (thresholdAcceptedCounter init s
            (Nat.ceil ((init.card : ℝ) / 1000000)) M A.val J
            (1 / 40000)).state ω
          (thresholdAcceptedCounter init s
            (Nat.ceil ((init.card : ℝ) / 1000000)) M A.val J
            (1 / 40000)).start = (0, 0, true) :=
        CounterSpec.state_before_start
          (thresholdAcceptedCounter init s
            (Nat.ceil ((init.card : ℝ) / 1000000)) M A.val J
            (1 / 40000)) ω _ le_rfl
      simp only [Set.mem_setOf_eq, hd, Nat.add_zero, hzz, hzzStart]
      simp [hRzero, hkzero]

/-- The terminal zero-slot failure is retained to the prefix-selected fixed
horizon. -/
theorem thresholdAcceptedTrialSlotEvent_retained
    {init : InputCfg n} {ω : InputLog n}
    {a s T H M R : ℕ}
    (h : Prefix init ω a s (s + H))
    (A : Fin (M + 1))
    (J : Finset (Fin (PhaseThreeModel.Numeric.hourIndex n + 1)))
    (hR : reserveCount (labelsAt init ω s) = R)
    (hvalid : 0 < M ∧
      (1 / 40000 : ℝ) ≤ (A.val : ℝ) / M ∧
      2 * Nat.ceil ((init.card : ℝ) / 1000000) ≤ R)
    (hsT : s ≤ T) (hTH : T ≤ s + H)
    (haccepted : acceptedCount (labelsAt init ω T) = R)
    (hslot : ω ∈
      thresholdAcceptedTrialSlotEvent init s M R A J (T - s)) :
    ω ∈ thresholdAcceptedTrialSlotEvent init s M R A J H := by
  let k := Nat.ceil ((init.card : ℝ) / 1000000)
  have htime : s + (T - s) = T := Nat.add_sub_of_le hsT
  have hcounts :=
    thresholdAcceptedCounter_counts_retained_after_complete
      (M := M) (k := k) (A := A.val) h J (1 / 40000)
      hR hsT hTH le_rfl haccepted
  unfold thresholdAcceptedTrialSlotEvent at hslot ⊢
  dsimp only at hslot ⊢
  rw [if_pos hvalid] at hslot ⊢
  unfold acceptedTrialFailureOf at hslot ⊢
  change
    (((R - k : ℕ) : ℝ) ≤
        ((thresholdAcceptedCounter init s k M A.val J (1 / 40000)).state
          ω (s + (T - s))).1 ∧
      (acceptedBadRate M A.val (1 / 40000) + 1 / 40000) *
          ((thresholdAcceptedCounter init s k M A.val J (1 / 40000)).state
            ω (s + (T - s))).1 ≤
        ((thresholdAcceptedCounter init s k M A.val J (1 / 40000)).state
          ω (s + (T - s))).2.1) at hslot
  change
    (((R - k : ℕ) : ℝ) ≤
        ((thresholdAcceptedCounter init s k M A.val J (1 / 40000)).state
          ω (s + H)).1 ∧
      (acceptedBadRate M A.val (1 / 40000) + 1 / 40000) *
          ((thresholdAcceptedCounter init s k M A.val J (1 / 40000)).state
            ω (s + H)).1 ≤
        ((thresholdAcceptedCounter init s k M A.val J (1 / 40000)).state
          ω (s + H)).2.1)
  rw [htime] at hslot
  rw [hcounts.1, hcounts.2]
  exact hslot

/-- Corrected cover directly at a prefix-selected fixed horizon. -/
theorem actual_bad_samples_covered_by_early_or_threshold_trial_at_horizon
    {init : InputCfg n} {ω : InputLog n}
    {a s T H M R : ℕ}
    (h : Prefix init ω a s (s + H))
    (hsT : s ≤ T)
    (hTH : T ≤ s + H)
    (A : Fin (M + 1))
    (J : Finset (Fin (PhaseThreeModel.Numeric.hourIndex n + 1)))
    (hR : reserveCount (labelsAt init ω s) = R)
    (hvalid : 0 < M ∧
      (1 / 40000 : ℝ) ≤ (A.val : ℝ) / M ∧
      2 * Nat.ceil ((init.card : ℝ) / 1000000) ≤ R)
    (hgate : ∀ u, s ≤ u → u < T →
      ThresholdAcceptedGate
        (Nat.ceil ((init.card : ℝ) / 1000000))
        M A.val J (1 / 40000) (labelsAt init ω u))
    (haccepted : acceptedCount (labelsAt init ω T) = R)
    (hbad :
      (acceptedBadRate M A.val (1 / 40000) + 1 / 40000) * (R : ℝ) +
          Nat.ceil ((init.card : ℝ) / 1000000) ≤
        badSampleCount J (labelsAt init ω T)) :
    ω ∈ EarlyRoleEvent init s M R
        (Nat.ceil ((init.card : ℝ) / 1000000)) ∨
      ω ∈ thresholdAcceptedTrialSlotEvent init s M R A J H := by
  have hshort := prefix_restrict_endpoint h hsT hTH
  rcases actual_bad_samples_covered_by_early_or_threshold_trial
      hshort A J hR hvalid hgate haccepted hbad with hearly | hslot
  · exact Or.inl hearly
  · exact Or.inr (thresholdAcceptedTrialSlotEvent_retained
      h A J hR hvalid hsT hTH haccepted hslot)

/-- Final zero-slot cover in exactly the finite-union form consumed by row two.
The horizon `N i A` is fixed by the `firstFourStart` prefix before this theorem
is applied. -/
theorem threshold_zero_slot_cover
    {init : InputCfg n} {ω : InputLog n}
    {a s T M R : ℕ}
    (C : Fin 3 → Bias (PhaseThreeModel.Numeric.hourIndex n) → Prop)
    (J : Fin 3 → Fin (M + 1) →
      Finset (Fin (PhaseThreeModel.Numeric.hourIndex n + 1)))
    (N : Fin 3 → Fin (M + 1) → ℕ)
    (i : Fin 3) (A : Fin (M + 1))
    (h : Prefix init ω a s (s + N i A))
    (hsT : s ≤ T)
    (hTH : T ≤ s + N i A)
    (hR : reserveCount (labelsAt init ω s) = R)
    (hvalid : 0 < M ∧
      (1 / 40000 : ℝ) ≤ (A.val : ℝ) / M ∧
      2 * Nat.ceil ((init.card : ℝ) / 1000000) ≤ R)
    (hgate : ∀ u, s ≤ u → u < T →
      ThresholdAcceptedGate
        (Nat.ceil ((init.card : ℝ) / 1000000))
        M A.val (J i A) (1 / 40000) (labelsAt init ω u))
    (haccepted : acceptedCount (labelsAt init ω T) = R)
    (hbad :
      (acceptedBadRate M A.val (1 / 40000) + 1 / 40000) * (R : ℝ) +
          Nat.ceil ((init.card : ℝ) / 1000000) ≤
        badSampleCount (J i A) (labelsAt init ω T)) :
    ω ∈ prerequisiteEventWithThresholdAccepted init s M R C J N := by
  rcases actual_bad_samples_covered_by_early_or_threshold_trial_at_horizon
      h hsT hTH A (J i A) hR hvalid hgate haccepted hbad with hearly | hslot
  · apply Set.mem_iUnion.mpr
    refine ⟨none, ?_⟩
    simpa [testEventWithThresholdAccepted] using hearly
  · apply Set.mem_iUnion.mpr
    refine ⟨some (i, A, ⟨0, Nat.zero_lt_succ M⟩), ?_⟩
    simpa [testEventWithThresholdAccepted] using hslot

/-!
THEOREM LIST
* `recorded_threshold_accepted_trial_tail`
* `thresholdAcceptedTrialSlotEvent_measurable`
* `recorded_threshold_accepted_trial_slot_tail`
* `recorded_testEventWithThresholdAccepted_tail`
* `recorded_prerequisites_withThresholdAccepted_tail`
* `law_prerequisites_withThresholdAccepted_tail`
* `law_prerequisites_withThresholdAccepted_inverse_power`
* `actual_bad_samples_covered_by_early_or_threshold_trial`
* `thresholdAcceptedTrialSlotEvent_retained`
* `actual_bad_samples_covered_by_early_or_threshold_trial_at_horizon`
* `threshold_zero_slot_cover`

CLOSES
* Repaired `k = 0` accepted-trial slot with the threshold-aware counter.
* The unchanged exponential and finite-union original-law charges.
* Exact terminal-to-prefix-selected-horizon transport.
* The zero-slot cover in the finite union consumed by row two.

UNFINISHED
* The row-two producer must supply `hgate`, the fixed-horizon legal prefix,
  completion, and the terminal bad-sample inequality.
* The protected-class sentinel boundary `ell + 2 = L` is deliberately absent.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateThresholdAcceptedTrialSlot

end
