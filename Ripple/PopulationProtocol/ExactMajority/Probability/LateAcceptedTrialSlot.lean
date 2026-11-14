-- Ripple/PopulationProtocol/ExactMajority/Probability/LateAcceptedTrialSlot.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateAcceptedCounterCoupling

/-!
# The accepted-trial zero slot

For each class and integer global floor, the zero frozen-prefix index is
replaced by the stopped accepted-trial test.  Positive indices retain the
frozen-pool tests, and `none` retains the one shared early-role test.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateAcceptedTrialSlot

open TimeTheorem PairLog PairLogAuxiliary
open AveragingRecordedExpectation LateSamplingScalar
open LateF6Acceptance LateF6Hazards LateF6OriginalLaw
open LateSamplingCounterTail LateAcceptedTrialTail
open LateAcceptedRectangleHazard LateSamplingClassGates
open LateAcceptedCounterCoupling LateSamplingCalibration
open LateSamplingEarlyRoles LateSamplingSplice
open LateSamplingFirstHit LateFrozenPoolTail LateFrozenPoolOriginalLaw

variable {L K n : ℕ}

/-- Bad-reward ratio supplied by the live global and frozen class floors. -/
def acceptedBadRate (M A : ℕ) (γ : ℝ) : ℝ :=
  1 - (A : ℝ) / M + γ

theorem acceptedBadRate_nonneg {M A : ℕ} {γ : ℝ}
    (hM : 0 < M) (hA : A ≤ M) (hγ : 0 ≤ γ) :
    0 ≤ acceptedBadRate M A γ := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hAr : (A : ℝ) ≤ M := by exact_mod_cast hA
  have hratio : (A : ℝ) / M ≤ 1 := (div_le_one hMr).2 hAr
  unfold acceptedBadRate
  linarith

/-- The rectangle estimate is exactly the hazard premise of the
instantiated stopped counter. -/
theorem acceptedCounter_hazard
    (init : Cfg L K) (hn : 2 ≤ init.card)
    (s k M A : ℕ) (J : Finset (Fin (L + 1))) (γ : ℝ)
    (hM : 0 < M) (hA : A ≤ M)
    (hγ : 0 ≤ γ) (hγA : γ ≤ (A : ℝ) / M) :
    ∀ t p z,
      (acceptedCounter init s k M A J γ).Enabled t p z →
      pairMass init (acceptedCounter init s k M A J γ).bad
          (prefixLabels init t p) ≤
        acceptedBadRate M A γ *
          pairMass init (acceptedCounter init s k M A J γ).event
            (prefixLabels init t p) := by
  intro t p z he
  let f := prefixLabels init t p
  have hgate : AcceptedGate M A J γ f := by
    simpa [f, acceptedCounter] using he.2.2.1
  rcases hgate with ⟨hmains, hglobal, hfloor⟩
  by_cases hk : k ≤ frozenCount f
  · have e1 : pairMass init (lateAcceptedRectangle k) f =
        pairMass init acceptedRectangle f := by
      unfold pairMass
      congr 3
      ext ij
      simp [goodPairs, lateAcceptedRectangle, hk]
    have e2 : pairMass init (lateBadAcceptedRectangle k J) f =
        pairMass init (badAcceptedRectangle (indexClass J)) f := by
      unfold pairMass
      congr 3
      ext ij
      simp [goodPairs, lateBadAcceptedRectangle, hk]
    show pairMass init (lateBadAcceptedRectangle k J) f ≤
      acceptedBadRate M A γ * pairMass init (lateAcceptedRectangle k) f
    rw [e1, e2]
    exact stored_index_bad_pairMass_le init hn J f M A γ hM hA hγ hγA
        hmains hglobal hfloor
  · simp [f, acceptedCounter, lateAcceptedRectangle,
      lateBadAcceptedRectangle, hk, pairMass, goodPairs]

/-- State form of the event used in the zero slot. -/
def acceptedTrialFailure {init : Cfg L K}
    (Q : CounterSpec init)
    (q γ : ℝ) (m N : ℕ) : Set (Ω L K) :=
  {ω | (m : ℝ) ≤ (Q.state ω (Q.start + N)).1 ∧
    (q + γ) * (Q.state ω (Q.start + N)).1 ≤
      (Q.state ω (Q.start + N)).2.1}

-- The preceding displayed type is awkward for inference in Lean.  This
-- equivalent namespace-local declaration is the one used below.
def acceptedTrialFailureOf {init : Cfg L K}
    (Q : CounterSpec init) (q γ : ℝ) (m N : ℕ) : Set (Ω L K) :=
  {ω | (m : ℝ) ≤ (Q.state ω (Q.start + N)).1 ∧
    (q + γ) * (Q.state ω (Q.start + N)).1 ≤
      (Q.state ω (Q.start + N)).2.1}

theorem acceptedTrialFailureOf_measurable {init : Cfg L K}
    (Q : CounterSpec init) (q γ : ℝ) (m N : ℕ) :
    MeasurableSet (acceptedTrialFailureOf Q q γ m N) := by
  let G : ((i : Finset.Iic (Q.start + N)) → Draw L K) → Prop := fun p =>
    let z := Q.prefixState (Q.start + N) p
    (m : ℝ) ≤ z.1 ∧ (q + γ) * z.1 ≤ z.2.1
  have heq : acceptedTrialFailureOf Q q γ m N =
      {ω | G (frestrictLe (Q.start + N) ω)} := by
    ext ω
    rfl
  rw [heq]
  exact (pairLogFiltration L K).le (Q.start + N) _
    (prefix_gate_measurable (Q.start + N) G)

/-- Recorded-future accepted-trial estimate for the actual rectangle counter. -/
theorem recorded_accepted_trial_tail
    (init : Cfg L K) (hn : 2 ≤ init.card)
    (s k M A : ℕ) (J : Finset (Fin (L + 1)))
    (γ : ℝ) (hM : 0 < M) (hA : A ≤ M)
    (hγ : 0 ≤ γ) (hγA : γ ≤ (A : ℝ) / M)
    (p : (i : Finset.Iic s) → Draw L K)
    (m N : ℕ) :
    recordedFuture init s p
      (acceptedTrialFailureOf
        (acceptedCounter init s k M A J γ)
        (acceptedBadRate M A γ) γ m N) ≤
      ENNReal.ofReal (Real.exp (-2 * γ ^ 2 * m)) := by
  let Q := acceptedCounter init s k M A J γ
  have htail := CounterSpec.constant_tail Q hn (acceptedBadRate M A γ) γ
    (acceptedBadRate_nonneg hM hA hγ) hγ
    (acceptedCounter_hazard init hn s k M A J γ hM hA hγ hγA)
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

/-- The actual zero-slot event.  Invalid integer floors or an insufficient
Reserve supply make the slot empty; the later deterministic cover uses only
the valid branch. -/
def acceptedTrialSlotEvent
    (init : Cfg L K) (s M R : ℕ)
    (A : Fin (M + 1)) (J : Finset (Fin (L + 1))) (N : ℕ) : Set (Ω L K) :=
  let k := Nat.ceil ((init.card : ℝ) / 1000000)
  if 0 < M ∧
      (1 / 40000 : ℝ) ≤ (A.val : ℝ) / M ∧
      2 * k ≤ R then
    acceptedTrialFailureOf
      (acceptedCounter init s k M A.val J (1 / 40000))
      (acceptedBadRate M A.val (1 / 40000)) (1 / 40000)
      (R - k) N
  else ∅

theorem acceptedTrialSlotEvent_measurable
    (init : Cfg L K) (s M R : ℕ)
    (A : Fin (M + 1)) (J : Finset (Fin (L + 1))) (N : ℕ) :
    MeasurableSet (acceptedTrialSlotEvent init s M R A J N) := by
  unfold acceptedTrialSlotEvent
  dsimp only
  split_ifs
  · exact acceptedTrialFailureOf_measurable _ _ _ _ _
  · exact MeasurableSpace.measurableSet_empty _

/-- Every valid accepted-trial zero slot has the same base exponential charge
as a frozen-prefix test. -/
theorem recorded_accepted_trial_slot_tail
    (init : Cfg L K) (hn : 2 ≤ init.card)
    (s M R : ℕ) (A : Fin (M + 1))
    (J : Finset (Fin (L + 1))) (N : ℕ)
    (p : (i : Finset.Iic s) → Draw L K) :
    recordedFuture init s p
      (acceptedTrialSlotEvent init s M R A J N) ≤
      ENNReal.ofReal
        (Real.exp (-(init.card : ℝ) / 800000000000000)) := by
  unfold acceptedTrialSlotEvent
  dsimp only
  split_ifs with hv
  · rcases hv with ⟨hM, hγA, hR⟩
    have hA : A.val ≤ M := by have := A.isLt; omega
    have htail := recorded_accepted_trial_tail init hn s
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

/-- Replace exactly the `k.val = 0` frozen-prefix slot by the accepted-trial
slot.  The shared `none` event and every positive frozen-prefix slot are
unchanged. -/
def testEventWithAccepted
    (init : Cfg L K) (s M R : ℕ)
    (C : Fin 3 → Bias L → Prop)
    (J : Fin 3 → Fin (M + 1) → Finset (Fin (L + 1)))
    (N : Fin 3 → Fin (M + 1) → ℕ) :
    ClassTestIndex M → Set (Ω L K)
  | none => EarlyRoleEvent init s M R
      (Nat.ceil ((init.card : ℝ) / 1000000))
  | some (i, A, k) =>
      if k.val = 0 then
        acceptedTrialSlotEvent init s M R A (J i A) (N i A)
      else
        LateFrozenPoolOriginalLaw.testEvent init s M R C (some (i, A, k))

theorem testEventWithAccepted_none
    (init : Cfg L K) (s M R : ℕ)
    (C : Fin 3 → Bias L → Prop)
    (J : Fin 3 → Fin (M + 1) → Finset (Fin (L + 1)))
    (N : Fin 3 → Fin (M + 1) → ℕ) :
    testEventWithAccepted init s M R C J N none =
      EarlyRoleEvent init s M R
        (Nat.ceil ((init.card : ℝ) / 1000000)) := rfl

theorem testEventWithAccepted_zero
    (init : Cfg L K) (s M R : ℕ)
    (C : Fin 3 → Bias L → Prop)
    (J : Fin 3 → Fin (M + 1) → Finset (Fin (L + 1)))
    (N : Fin 3 → Fin (M + 1) → ℕ)
    (i : Fin 3) (A : Fin (M + 1)) :
    testEventWithAccepted init s M R C J N
        (some (i, A, ⟨0, Nat.zero_lt_succ M⟩)) =
      acceptedTrialSlotEvent init s M R A (J i A) (N i A) := by
  simp [testEventWithAccepted]

theorem testEventWithAccepted_positive
    (init : Cfg L K) (s M R : ℕ)
    (C : Fin 3 → Bias L → Prop)
    (J : Fin 3 → Fin (M + 1) → Finset (Fin (L + 1)))
    (N : Fin 3 → Fin (M + 1) → ℕ)
    (i : Fin 3) (A k : Fin (M + 1)) (hk : 0 < k.val) :
    testEventWithAccepted init s M R C J N (some (i, A, k)) =
      LateFrozenPoolOriginalLaw.testEvent init s M R C (some (i, A, k)) := by
  simp [testEventWithAccepted, Nat.ne_of_gt hk]

theorem testEventWithAccepted_measurable
    (init : Cfg L K) (s M R : ℕ)
    (C : Fin 3 → Bias L → Prop)
    (J : Fin 3 → Fin (M + 1) → Finset (Fin (L + 1)))
    (N : Fin 3 → Fin (M + 1) → ℕ)
    (x : ClassTestIndex M) :
    MeasurableSet (testEventWithAccepted init s M R C J N x) := by
  cases x with
  | none => exact earlyRoleEvent_measurable init s M R _
  | some z =>
      rcases z with ⟨i, A, k⟩
      unfold testEventWithAccepted
      dsimp only
      split_ifs
      · exact acceptedTrialSlotEvent_measurable init s M R A (J i A) (N i A)
      · exact LateFrozenPoolOriginalLaw.testEvent_measurable init s M R C _

/-- Per-index estimate after filling the zero slot. -/
theorem recorded_testEventWithAccepted_tail
    (init : Cfg L K) (s M R : ℕ)
    (hd : SeedDensity init.card M R)
    (hlog : (1000000000000 : ℝ) < Real.log (init.card : ℝ))
    (C : Fin 3 → Bias L → Prop)
    (J : Fin 3 → Fin (M + 1) → Finset (Fin (L + 1)))
    (N : Fin 3 → Fin (M + 1) → ℕ)
    (p : (i : Finset.Iic s) → Draw L K)
    (x : ClassTestIndex M) :
    recordedFuture init s p (testEventWithAccepted init s M R C J N x) ≤
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
      · rw [show testEventWithAccepted init s M R C J N (some (i, A, k)) =
          acceptedTrialSlotEvent init s M R A (J i A) (N i A) by
            simp [testEventWithAccepted, hz]]
        exact recorded_accepted_trial_slot_tail init hn s M R A
          (J i A) (N i A) p
      · rw [testEventWithAccepted_positive init s M R C J N i A k
          (by omega)]
        unfold LateFrozenPoolOriginalLaw.testEvent
        dsimp only
        split_ifs with hk
        · exact frozen_test_tail init hn init.card s M A.val k.val hM
            (by omega) (by omega) hk (C i) p
        · rw [measure_empty]
          exact zero_le

/-- The filled family has exactly the same finite prefactor. -/
def prerequisiteEventWithAccepted
    (init : Cfg L K) (s M R : ℕ)
    (C : Fin 3 → Bias L → Prop)
    (J : Fin 3 → Fin (M + 1) → Finset (Fin (L + 1)))
    (N : Fin 3 → Fin (M + 1) → ℕ) : Set (Ω L K) :=
  ⋃ x, testEventWithAccepted init s M R C J N x

theorem prerequisiteEventWithAccepted_measurable
    (init : Cfg L K) (s M R : ℕ)
    (C : Fin 3 → Bias L → Prop)
    (J : Fin 3 → Fin (M + 1) → Finset (Fin (L + 1)))
    (N : Fin 3 → Fin (M + 1) → ℕ) :
    MeasurableSet (prerequisiteEventWithAccepted init s M R C J N) :=
  MeasurableSet.iUnion
    (testEventWithAccepted_measurable init s M R C J N)

theorem recorded_prerequisites_withAccepted_tail
    (init : Cfg L K) (s M R : ℕ)
    (hd : SeedDensity init.card M R)
    (hlog : (1000000000000 : ℝ) < Real.log (init.card : ℝ))
    (C : Fin 3 → Bias L → Prop)
    (J : Fin 3 → Fin (M + 1) → Finset (Fin (L + 1)))
    (N : Fin 3 → Fin (M + 1) → ℕ)
    (p : (i : Finset.Iic s) → Draw L K) :
    recordedFuture init s p
      (prerequisiteEventWithAccepted init s M R C J N) ≤
      ENNReal.ofReal ((3 * ((M : ℝ) + 1) ^ 2 + 1) *
        Real.exp (-(init.card : ℝ) / 800000000000000)) := by
  apply class_test_union_bound (recordedFuture init s p) init.card M
    (testEventWithAccepted init s M R C J N)
  exact recorded_testEventWithAccepted_tail init s M R hd hlog C J N p

variable {n : ℕ}

abbrev AcceptedIndexChoice (init : InputCfg n) :=
  (s : ℕ) → (p : InputPrefix n s) → Fin 3 →
    Fin (selectedMains init s p + 1) →
      Finset (Fin (PhaseThreeModel.Numeric.hourIndex n + 1))

abbrev AcceptedHorizonChoice (init : InputCfg n) :=
  (s : ℕ) → (p : InputPrefix n s) → Fin 3 →
    Fin (selectedMains init s p + 1) → ℕ

def selectedPrerequisitesWithAccepted
    (init : InputCfg n) (C : ClassChoice n)
    (J : AcceptedIndexChoice init) (N : AcceptedHorizonChoice init)
    (s : ℕ) (p : InputPrefix n s) : Set (InputLog n) :=
  prerequisiteEventWithAccepted init s
    (selectedMains init s p) (selectedReserves init s p)
    (C s p) (J s p) (N s p)

/-- Original-law family at the genuine first threshold-4 stopping time. -/
def originalPrerequisiteWithAcceptedFailure
    (init : InputCfg n) (C : ClassChoice n)
    (J : AcceptedIndexChoice init) (N : AcceptedHorizonChoice init) :
    Set (InputLog n) :=
  {ω | ∃ s : ℕ, firstFourStart init ω = (s : WithTop ℕ) ∧
    ω ∈ selectedFailure s (seedPrefixes init s)
      (selectedPrerequisitesWithAccepted init C J N s)}

/-- Original-law charge after filling every accepted-trial zero slot.  Prefix
selection adds no factor for the stopping time, observed counts, floors,
classes, index sets, or horizons. -/
theorem law_prerequisites_withAccepted_tail
    (init : InputCfg n) (hcard : init.card = n)
    (hn : timePopulationThreshold ≤ n)
    (C : ClassChoice n)
    (J : AcceptedIndexChoice init) (N : AcceptedHorizonChoice init) :
    law init (originalPrerequisiteWithAcceptedFailure init C J N) ≤
      ENNReal.ofReal (13 * (n : ℝ) ^ 2 *
        Real.exp (-(n : ℝ) / 800000000000000)) := by
  have hlog : (1000000000000 : ℝ) < Real.log (init.card : ℝ) := by
    simpa only [hcard] using time_threshold_logarithm hn
  apply law_stopping_selected_bound init (firstFourStart init)
    (firstFourStart_past init)
    (seedPrefixes init) (selectedPrerequisitesWithAccepted init C J N)
    (fun s p => prerequisiteEventWithAccepted_measurable init s _ _
      (C s p) (J s p) (N s p))
  intro s p hp
  have hd : SeedDensity init.card (selectedMains init s p)
      (selectedReserves init s p) := hp
  have hM : selectedMains init s p ≤ init.card := by
    have h := hd.total_le
    omega
  have hlocal := recorded_prerequisites_withAccepted_tail init s _ _ hd hlog
    (C s p) (J s p) (N s p) p
  have hpoly := (sampling_finite_factor hM hlog).1
  have hbound := hlocal.trans (ENNReal.ofReal_le_ofReal hpoly)
  simpa only [hcard] using hbound

theorem law_prerequisites_withAccepted_inverse_power
    (init : InputCfg n) (hcard : init.card = n)
    (hn : timePopulationThreshold ≤ n)
    (C : ClassChoice n)
    (J : AcceptedIndexChoice init) (N : AcceptedHorizonChoice init) :
    law init (originalPrerequisiteWithAcceptedFailure init C J N) ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-190)) := by
  have hpoly := (sampling_finite_factor (M := n) le_rfl
    (time_threshold_logarithm hn)).2
  exact (law_prerequisites_withAccepted_tail init hcard hn C J N).trans
    (ENNReal.ofReal_le_ofReal hpoly.le)

private theorem slot_mainCount_le_card (f : Fin n → AgentState L K) :
    mainCount f ≤ n := by
  classical
  have hsub : pool f Main ⊆ (Finset.univ : Finset (Fin n)) :=
    fun _ _ => Finset.mem_univ _
  simpa [mainCount] using Finset.card_le_card hsub

/-- Deterministic cover used by item 3.  Its only nonlocal premise is the
survival of the class/frozen-floor receipt through the observed endpoint. -/
theorem actual_bad_samples_covered_by_early_or_trial
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
      AcceptedGate M A.val J (1 / 40000) (labelsAt init ω u))
    (haccepted : acceptedCount (labelsAt init ω T) = R)
    (hbad :
      (acceptedBadRate M A.val (1 / 40000) + 1 / 40000) * (R : ℝ) +
          Nat.ceil ((init.card : ℝ) / 1000000) ≤
        badSampleCount J (labelsAt init ω T)) :
    ω ∈ EarlyRoleEvent init s M R
        (Nat.ceil ((init.card : ℝ) / 1000000)) ∨
      ω ∈ acceptedTrialSlotEvent init s M R A J (T - s) := by
  let k := Nat.ceil ((init.card : ℝ) / 1000000)
  set Q := acceptedCounter init s k M A.val J (1 / 40000) with hQ
  by_cases hearly : ω ∈ EarlyRoleEvent init s M R k
  · exact Or.inl hearly
  · right
    have hstart : Q.start = s := rfl
    unfold acceptedTrialSlotEvent
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
      have hcouple : acceptedCount (labelsAt init ω T) ≤ (Q.state ω T).1 + k ∧
          badSampleCount J (labelsAt init ω T) ≤ (Q.state ω T).2.1 + k :=
        actual_counts_le_stopped_add_earlyCap h J (1 / 40000)
          hMseed hR hk hgate hearly T h.observed le_rfl
      have hcountActual : (Q.state ω T).1 ≤ acceptedCount (labelsAt init ω T) :=
        acceptedCounter_count_le_actual h k M A.val J
          (1 / 40000) T h.observed le_rfl
      have hrate : 0 ≤ acceptedBadRate M A.val (1 / 40000) + 1 / 40000 := by
        have hA : A.val ≤ M := by have := A.isLt; omega
        have hq := acceptedBadRate_nonneg (γ := (1 / 40000 : ℝ)) hvalid.1 hA (by norm_num)
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
          (show ((Q.state ω T).1 : ℝ) ≤ (R : ℝ) by exact_mod_cast hcountUpper) hrate
        exact hmul.trans hbadLower
    · -- the observed prefix is empty: the counter is still at its initial state
      have hTs : T = s := le_antisymm (not_lt.mp hsT) h.observed
      have hzero := (prefix_start_counts_zero h).2.1
      have hR0 : R = 0 := by
        rw [← haccepted, hTs]
        exact hzero
      have hk0 : k = 0 := by omega
      have hd : T - s = 0 := by omega
      have hzz : (acceptedCounter init s (Nat.ceil ((init.card : ℝ) / 1000000)) M
            A.val J (1 / 40000)).state ω s = (0, 0, true) :=
        CounterSpec.state_before_start
          (acceptedCounter init s (Nat.ceil ((init.card : ℝ) / 1000000)) M
            A.val J (1 / 40000)) ω s le_rfl
      have hzz2 : (acceptedCounter init s (Nat.ceil ((init.card : ℝ) / 1000000)) M
            A.val J (1 / 40000)).state ω
          (acceptedCounter init s (Nat.ceil ((init.card : ℝ) / 1000000)) M
            A.val J (1 / 40000)).start = (0, 0, true) :=
        CounterSpec.state_before_start
          (acceptedCounter init s (Nat.ceil ((init.card : ℝ) / 1000000)) M
            A.val J (1 / 40000)) ω _ le_rfl
      simp only [Set.mem_setOf_eq, hd, Nat.add_zero, hzz, hzz2]
      simp [hR0, hk0]

end Ripple.PopulationProtocol.ExactMajority.LateAcceptedTrialSlot

end
