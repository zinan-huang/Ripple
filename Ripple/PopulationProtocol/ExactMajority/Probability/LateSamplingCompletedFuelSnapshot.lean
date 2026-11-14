-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingCompletedFuelSnapshot.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingCorrectedFuelProducer
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingRowTwoThresholdRepair
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingSnapshotNumerics
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingMassCountTransport

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingCompletedFuelSnapshot

open TimeTheorem PairLog StageEventSpec
open LateF6Hazards LateF6OriginalLaw
open LateSamplingCalibration LateFrozenPoolOriginalLaw
open LateAcceptedRectangleHazard LateAcceptedTrialSlot
open LateSamplingSeedReceipt LateStrengthening LateSamplingClassGates
open LateSamplingRowTwoChoices LateSamplingRowTwoCounterRepair
open LateThresholdAcceptedTrialSlot LateSamplingRowTwoThresholdRepair
open LateSamplingStrongSeedReceipt
open LateSamplingCorrectedFuelProducer hiding InputCfg
open LateSamplingFirstHit LateThresholdAcceptedCounterCoupling LateFrozenPoolTail
open LateSamplingSnapshotNumerics LateSamplingMassCountTransport

variable {n m : ℕ}

/-! ## Completed accepted-sample counts -/

/-- Accepted Reserves whose stored index belongs to `J`. -/
noncomputable def acceptedGoodCount
    (J : Finset (Fin (PhaseThreeModel.Numeric.hourIndex n + 1)))
    (f : Fin m → AgentState (PhaseThreeModel.Numeric.hourIndex n) 256) : ℕ :=
  (pool f (fun a => AcceptedReserve a ∧ a.hour ∈ J)).card

/-- Good and bad accepted samples partition all accepted samples. -/
theorem acceptedGoodCount_add_badSampleCount
    (J : Finset (Fin (PhaseThreeModel.Numeric.hourIndex n + 1)))
    (f : Fin m → AgentState (PhaseThreeModel.Numeric.hourIndex n) 256) :
    acceptedGoodCount J f + badSampleCount J f = acceptedCount f := by
  classical
  simpa only [acceptedGoodCount, badSampleCount, BadSample] using
    (pool_partition f AcceptedReserve (fun a => a.hour ∈ J))

private theorem label_mem_trace
    (init : InputCfg n) (omega : InputLog n) (u : ℕ)
    (i : Fin init.card) :
    labelsAt init omega u i ∈ trace init omega u := by
  rw [← PairLog.labelsAt_config init omega u]
  exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩

private theorem reserve_hour_lt_of_sampled
    {L K : ℕ} {c : Config (AgentState L K)}
    (hsampled : ReserveSampling.ReserveSampled c)
    {a : AgentState L K} (ha : a ∈ c)
    (hrole : a.role = Role.reserve) :
    a.hour.val < L := by
  have hnot : ¬ ReserveSampling.unsampled (L := L) (K := K) a := by
    unfold ReserveSampling.ReserveSampled
      ReserveSampling.unsampledReserveU at hsampled
    exact (Multiset.countP_eq_zero.mp hsampled) a ha
  by_contra hlt
  apply hnot
  refine ⟨hrole, ?_⟩
  have hbound := a.hour.isLt
  omega

private theorem completion_accepts_every_reserve
    {init : InputCfg n} {omega : InputLog n}
    {a four five completed : ℕ} {Snapshot : InputCfg n → Prop}
    (hcompletion : LateSamplingCompletion.CompletionReceipt
      init omega a four five completed Snapshot)
    (i : Fin init.card) :
    AcceptedReserve (labelsAt init omega completed i) ↔
      (labelsAt init omega completed i).role = Role.reserve := by
  constructor
  · exact fun h => h.1
  · intro hrole
    exact ⟨hrole,
      hcompletion.complete.phase_five _
        (label_mem_trace init omega completed i),
      reserve_hour_lt_of_sampled hcompletion.complete.sampled
        (label_mem_trace init omega completed i) hrole⟩

/-- At completion, accepted Reserves are exactly all Reserve labels. -/
theorem completion_acceptedCount_eq_reserveCount
    {init : InputCfg n} {omega : InputLog n}
    {a four five completed : ℕ} {Snapshot : InputCfg n → Prop}
    (hcompletion : LateSamplingCompletion.CompletionReceipt
      init omega a four five completed Snapshot) :
    acceptedCount (labelsAt init omega completed) =
      reserveCount (labelsAt init omega completed) := by
  classical
  change (pool (labelsAt init omega completed) AcceptedReserve).card =
    (pool (labelsAt init omega completed)
      (fun x => reserveRole x.role)).card
  apply congrArg Finset.card
  ext i
  simp only [mem_pool]
  rw [completion_accepts_every_reserve hcompletion i]
  rfl

/-- At completion, the good accepted count is the configuration count of
Reserve agents whose stored index lies in `J`. -/
theorem completion_acceptedGoodCount_eq_reserveSet
    {init : InputCfg n} {omega : InputLog n}
    {a four five completed : ℕ} {Snapshot : InputCfg n → Prop}
    (hcompletion : LateSamplingCompletion.CompletionReceipt
      init omega a four five completed Snapshot)
    (J : Finset (Fin (PhaseThreeModel.Numeric.hourIndex n + 1))) :
    acceptedGoodCount J (labelsAt init omega completed) =
      (trace init omega completed).countP
        (fun x => x.role = Role.reserve ∧ x.hour ∈ J) := by
  classical
  rw [show trace init omega completed = labelCfg (labelsAt init omega completed) from
    (PairLog.labelsAt_config init omega completed).symm,
    AveragingLiveProduct.countP_labelCfg]
  unfold acceptedGoodCount pool
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [completion_accepts_every_reserve hcompletion i]

/-- The completed exact-index good count is literally lower-level fuel. -/
theorem completion_acceptedGoodCount_exact
    {init : InputCfg n} {omega : InputLog n}
    {a four five completed : ℕ} {Snapshot : InputCfg n → Prop}
    (hcompletion : LateSamplingCompletion.CompletionReceipt
      init omega a four five completed Snapshot)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    acceptedGoodCount (exactIndices ell) (labelsAt init omega completed) =
      Phase6FuelLedger.reserveFuel
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        ell (trace init omega completed) := by
  rw [completion_acceptedGoodCount_eq_reserveSet hcompletion]
  unfold Phase6FuelLedger.reserveFuel Phase6FuelLedger.IsFuel
  apply Multiset.countP_congr rfl
  intro x _hx
  apply propext
  constructor
  · rintro ⟨hrole, hhour⟩
    simp only [exactIndices, Finset.mem_singleton] at hhour
    exact ⟨hrole, congrArg Fin.val hhour⟩
  · rintro ⟨hrole, hhour⟩
    refine ⟨hrole, ?_⟩
    simp only [exactIndices, Finset.mem_singleton]
    exact Fin.ext hhour

/-- The completed adjacent-class good count is literally two-level fuel. -/
theorem completion_acceptedGoodCount_adjacent
    {init : InputCfg n} {omega : InputLog n}
    {a four five completed : ℕ} {Snapshot : InputCfg n → Prop}
    (hcompletion : LateSamplingCompletion.CompletionReceipt
      init omega a four five completed Snapshot)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n) :
    acceptedGoodCount (adjacentIndices ell hell)
        (labelsAt init omega completed) =
      Phase6FuelLedger.twoReserveFuel
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        ell (trace init omega completed) := by
  rw [completion_acceptedGoodCount_eq_reserveSet hcompletion]
  unfold Phase6FuelLedger.twoReserveFuel Phase6FuelLedger.IsTwoFuel
  apply Multiset.countP_congr rfl
  intro x _hx
  apply propext
  constructor
  · rintro ⟨hrole, hhour⟩
    simp only [adjacentIndices, Finset.mem_insert,
      Finset.mem_singleton] at hhour
    rcases hhour with hhour | hhour
    · exact ⟨hrole, Or.inl (congrArg Fin.val hhour)⟩
    · have hval := congrArg Fin.val hhour
      exact ⟨hrole, Or.inr (by
        simpa [adjacentIndex, Phase6FuelLedger.highIndex] using hval)⟩
  · rintro ⟨hrole, hhour | hhour⟩
    · refine ⟨hrole, ?_⟩
      simp only [adjacentIndices, Finset.mem_insert,
        Finset.mem_singleton]
      exact Or.inl (Fin.ext hhour)
    · refine ⟨hrole, ?_⟩
      simp only [adjacentIndices, Finset.mem_insert,
        Finset.mem_singleton]
      apply Or.inr
      apply Fin.ext
      simpa [adjacentIndex, Phase6FuelLedger.highIndex] using hhour

/-! ## The one explicit timer input -/

/-- The timer item must provide one legal fixed horizon selected at the genuine
first-four prefix.  The row-two stopped counter is retained to this endpoint. -/
structure FixedRowTwoHorizon
    (init : InputCfg n) (omega : InputLog n)
    (allThree four completed H : ℕ) : Prop where
  path : Prefix init omega allThree four (four + H)
  completed_le : completed ≤ four + H

/-! ## Small deterministic arithmetic from the strong role split -/

private theorem earlyCap_cast_le_reserve_div
    {init : InputCfg n} {M C R : ℕ}
    (hn : timePopulationThreshold ≤ n)
    (hcard : init.card = n)
    (hdensity : StrongSeedDensity n M C R) :
    (Nat.ceil ((init.card : ℝ) / 1000000) : ℝ) ≤ (R : ℝ) / 20000 := by
  have hlog := time_threshold_logarithm hn
  have hnlarge : 1000000 ≤ n := logarithm_population_lower hlog
  have hnlargeR : (1000000 : ℝ) ≤ n := by exact_mod_cast hnlarge
  have hceil := Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ (n : ℝ) / 1000000)
  have hreserve : (6 : ℝ) * n ≤ 25 * R := by
    exact_mod_cast hdensity.reserves_lower
  rw [hcard]
  try clear hn
  nlinarith

private theorem twice_earlyCap_le_reserve
    {init : InputCfg n} {M C R : ℕ}
    (hn : timePopulationThreshold ≤ n)
    (hcard : init.card = n)
    (hdensity : StrongSeedDensity n M C R) :
    2 * Nat.ceil ((init.card : ℝ) / 1000000) ≤ R := by
  have h := earlyCap_cast_le_reserve_div hn hcard hdensity
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hreal :
      (2 : ℝ) * Nat.ceil ((init.card : ℝ) / 1000000) ≤ R := by
    try clear hn
    nlinarith
  exact_mod_cast hreal

private theorem main_positive
    {M C R : ℕ}
    (hn : timePopulationThreshold ≤ n)
    (hdensity : StrongSeedDensity n M C R) : 0 < M := by
  have hnpos : 0 < n := by
    have := (time_population_bounds hn).2
    omega
  have := hdensity.mains_lower
  omega

/-! ## Recognizing the repaired finite-family failure -/

private theorem rowTwoThresholdFailure_of_inner
    {init : InputCfg n} {omega : InputLog n}
    {four M R H : ℕ}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (hfirst : firstFourStart init omega = (four : WithTop ℕ))
    (hM : mainCount (labelsAt init omega four) = M)
    (hR : reserveCount (labelsAt init omega four) = R)
    (hdensity : SeedDensity init.card M R)
    (hinner : omega ∈ prerequisiteEventWithThresholdAccepted init four M R
      (rowTwoClassChoice ell hell four (frestrictLe four omega))
      (fun i _A => classIndices ell hell i)
      (fun _i _A => H)) :
    omega ∈ rowTwoThresholdFailure init ell hell H := by
  unfold rowTwoThresholdFailure
    originalPrerequisiteWithThresholdAcceptedFailure
  subst hM
  subst hR
  refine ⟨four, hfirst, ?_, ?_⟩
  · exact hdensity
  · exact hinner

/-- A post-threshold frozen-floor violation occupies a positive slot of the
repaired family; the zero slot is not involved. -/
private theorem frozen_violation_mem_threshold
    {init : InputCfg n} {omega : InputLog n}
    {allThree four terminal M R A H : ℕ}
    (h : Prefix init omega allThree four terminal)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (i : Fin 3)
    (hM : mainCount (labelsAt init omega four) = M)
    (hR : reserveCount (labelsAt init omega four) = R)
    (hdensity : SeedDensity init.card M R)
    (hA : A ≤ M)
    (hfloor : ∀ u, four ≤ u → u ≤ terminal →
      A ≤ classCount (indexClass (classIndices ell hell i))
        (labelsAt init omega u))
    (hk : Nat.ceil ((init.card : ℝ) / 1000000) ≤
      frozenCount (labelsAt init omega terminal))
    (hbad : ¬ FrozenFloor (indexClass (classIndices ell hell i)) A M
      (1 / 40000) (labelsAt init omega terminal)) :
    omega ∈ rowTwoThresholdFailure init ell hell H := by
  classical
  let k := frozenCount (labelsAt init omega terminal)
  have hmainTerminal : mainCount (labelsAt init omega terminal) = M :=
    (prefix_main_count h h.observed le_rfl).trans hM
  have hkM : k ≤ M := by
    have := frozen_le_main (labelsAt init omega terminal)
    omega
  let Af : Fin (M + 1) := ⟨A, by omega⟩
  let kf : Fin (M + 1) := ⟨k, by omega⟩
  have hzero := prefix_start_counts_zero h
  have hbzero := prefix_start_bad_counts_zero h
    (indexClass (classIndices ell hell i)) ∅
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos (frozenCount (labelsAt init omega terminal)) with h0 | hpos
    · exfalso
      apply hbad
      unfold FrozenFloor
      rw [h0]
      simp
    · exact hpos
  have hfreeze :
      omega ∈ frozenFailure init four M A k
        (indexClass (classIndices ell hell i)) (1 / 40000) := by
    refine ⟨hzero.1, hbzero.1, terminal, h.observed, ?_, rfl, hbad⟩
    intro u hfouru hut
    refine ⟨?_, ?_, hfloor u hfouru hut⟩
    · intro z
      exact h.window u (h.start_order.trans hfouru) hut _
        (label_mem_trace init omega u z)
    · exact (prefix_main_count h hfouru hut).trans hM
  have hinner :
      omega ∈ prerequisiteEventWithThresholdAccepted init four M R
        (rowTwoClassChoice ell hell four (frestrictLe four omega))
        (fun j _B => classIndices ell hell j)
        (fun _j _B => H) := by
    apply Set.mem_iUnion.mpr
    refine ⟨some (i, Af, kf), ?_⟩
    rw [testEventWithThresholdAccepted_positive init four M R
      (rowTwoClassChoice ell hell four (frestrictLe four omega))
      (fun j _B => classIndices ell hell j)
      (fun _j _B => H) i Af kf (by show 0 < k; exact hkpos)]
    unfold LateFrozenPoolOriginalLaw.testEvent
    dsimp only
    rw [if_pos (by simpa [kf, k] using hk)]
    simpa [Af, kf, k, rowTwoClassChoice] using hfreeze
  exact rowTwoThresholdFailure_of_inner ell hell h.four_start
    hM hR hdensity hinner

/-! ## The accepted-trial consequence of the repaired family -/

/-- Every selected global class floor loses at most `.0001 R` at the completed
sample snapshot.  This is the deterministic four-inequality cover specialized
to one class. -/
theorem acceptedGood_floor_of_not_rowTwoThresholdFailure
    {init : InputCfg n} {omega : InputLog n}
    {seed allThree four five completed M C R H : ℕ}
    {Snapshot : InputCfg n → Prop}
    (hn : timePopulationThreshold ≤ n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (i : Fin 3)
    (hstrong : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot)
    (hfixed : FixedRowTwoHorizon init omega allThree four completed H)
    (A : Fin (M + 1))
    (hglobal : ∀ u, four ≤ u → u ≤ completed →
      A.val ≤ classCount (indexClass (classIndices ell hell i))
        (labelsAt init omega u))
    (hratio : (1 / 40000 : ℚ) ≤ (A.val : ℚ) / M)
    (hnot : omega ∉ rowTwoThresholdFailure init ell hell H) :
    ((A.val : ℚ) / M - 1 / 10000) * R ≤
      acceptedGoodCount (classIndices ell hell i)
        (labelsAt init omega completed) := by
  classical
  have hMpos := main_positive hn hstrong.density
  have hdensity : SeedDensity init.card M R := by
    simpa only [hstrong.first_four_main, hstrong.first_four_reserve] using
      hstrong.rowTwoSeedDensity
  have hratioR :
      (1 / 40000 : ℝ) ≤ (A.val : ℝ) / M := by
    have := (Rat.cast_le (K := ℝ)).mpr hratio
    push_cast at this
    exact this
  have hvalid : 0 < M ∧
      (1 / 40000 : ℝ) ≤ (A.val : ℝ) / M ∧
      2 * Nat.ceil ((init.card : ℝ) / 1000000) ≤ R :=
    ⟨hMpos, hratioR,
      twice_earlyCap_le_reserve hn hstrong.population hstrong.density⟩
  let k := Nat.ceil ((init.card : ℝ) / 1000000)
  have hgate : ∀ u, four ≤ u → u < completed →
      ThresholdAcceptedGate k M A.val (classIndices ell hell i)
        (1 / 40000) (labelsAt init omega u) := by
    intro u hfouru hucompleted
    have hule : u ≤ completed := Nat.le_of_lt hucompleted
    have hmains : mainCount (labelsAt init omega u) = M :=
      (prefix_main_count hstrong.completion.observed_path hfouru hule).trans
        hstrong.first_four_main
    have hclass := hglobal u hfouru hule
    by_cases hbefore : frozenCount (labelsAt init omega u) < k
    · exact thresholdGate_before hmains hclass hbefore
    · apply thresholdGate_after hmains hclass
      by_contra hfloor
      have hpathu := prefix_restrict_endpoint
        hstrong.completion.observed_path hfouru hule
      apply hnot
      exact frozen_violation_mem_threshold
        (H := H) hpathu ell hell i
        hstrong.first_four_main hstrong.first_four_reserve
        hdensity (by omega)
        (fun v hfourv hvu => hglobal v hfourv (hvu.trans hule))
        (by omega) hfloor
  have haccepted :
      acceptedCount (labelsAt init omega completed) = R := by
    rw [completion_acceptedCount_eq_reserveCount hstrong.completion,
      hstrong.completed_reserve]
  by_contra hfloor
  have hltQ :
      (acceptedGoodCount (classIndices ell hell i)
          (labelsAt init omega completed) : ℚ) <
        ((A.val : ℚ) / M - 1 / 10000) * R :=
    lt_of_not_ge hfloor
  have hltR := (Rat.cast_lt (K := ℝ)).mpr hltQ
  push_cast at hltR
  have hpartition := acceptedGoodCount_add_badSampleCount
    (classIndices ell hell i) (labelsAt init omega completed)
  rw [haccepted] at hpartition
  have hpartitionR :
      (acceptedGoodCount (classIndices ell hell i)
          (labelsAt init omega completed) : ℝ) +
        badSampleCount (classIndices ell hell i)
          (labelsAt init omega completed) = R := by
    exact_mod_cast hpartition
  have hkR := earlyCap_cast_le_reserve_div
    hn hstrong.population hstrong.density
  have hbad :
      (acceptedBadRate M A.val (1 / 40000) + 1 / 40000) * (R : ℝ) +
          Nat.ceil ((init.card : ℝ) / 1000000) ≤
        badSampleCount (classIndices ell hell i)
          (labelsAt init omega completed) := by
    clear hn
    unfold acceptedBadRate
    norm_num at hltR ⊢
    try clear hn
    nlinarith
  have hinner :
      omega ∈ prerequisiteEventWithThresholdAccepted init four M R
        (rowTwoClassChoice ell hell four (frestrictLe four omega))
        (fun j _B => classIndices ell hell j)
        (fun _j _B => H) := by
    exact threshold_zero_slot_cover
      (C := rowTwoClassChoice ell hell four (frestrictLe four omega))
      (J := fun j _B => classIndices ell hell j)
      (N := fun _j _B => H)
      i A hfixed.path
      hstrong.completion.observed_path.observed hfixed.completed_le
      hstrong.first_four_reserve hvalid hgate haccepted hbad
  exact hnot (rowTwoThresholdFailure_of_inner ell hell
    hstrong.completion.observed_path.four_start
    hstrong.first_four_main hstrong.first_four_reserve hdensity hinner)

/-! ## Three completed sampling inequalities -/

private theorem majorityExact_le_main
    {init : InputCfg n} {omega : InputLog n}
    {seed allThree four five completed M C R : ℕ}
    {Snapshot : InputCfg n → Prop}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (sigma : Sign)
    (hstrong : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot) :
    majorityExact ell sigma (trace init omega completed) ≤ M := by
  have hbridge := exactBand_le_exactClass
    (m := init.card) sigma ell hell (labelsAt init omega completed)
  rw [show labelCfg (labelsAt init omega completed) =
      trace init omega completed from
    PairLog.labelsAt_config init omega completed] at hbridge
  have hclass := class_le_main (indexClass (exactIndices ell))
    (labelsAt init omega completed)
  have hband := hbridge.trans (hclass.trans_eq hstrong.completed_main)
  rw [exactBandCount_eq_biasedMainClassU
    (sigma := sigma) (ell := ell)] at hband
  simpa [majorityExact] using hband

private theorem first_majority_scaled
    {init : InputCfg n} {omega : InputLog n}
    {seed allThree four five completed M C R : ℕ}
    {Snapshot : InputCfg n → Prop}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (sigma : Sign)
    (hstrong : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot)
    (hseed : LateSamplingSeedReceipt init M ell.val sigma
      (trace init omega four))
    (hsmall :
      10000 * scaledShallowPositive sigma ell.val
          (trace init omega four) ≤ 111 * (M : ℚ)) :
    10000 * majorityExact ell sigma (trace init omega completed) ≤ 111 * M := by
  have hband := LateSamplingFirstBranchShape.bandCount_exact_le_scaledShallowPositive
    sigma ell.val (trace init omega completed)
  have hmono := LateSamplingShallowTransport.scaledShallowPositive_seed_mono
    (ell := ell.val) (σ := sigma)
    hstrong.completion.observed_path
    hstrong.completion.observed_path.observed le_rfl
  have hq :
      (10000 : ℚ) *
          bandCount sigma ell.val 0 (trace init omega completed) ≤
        111 * M := by
    nlinarith only [hband, hmono, hsmall]
  have hnat :
      10000 * bandCount sigma ell.val 0 (trace init omega completed) ≤
        111 * M := by
    exact_mod_cast hq
  rw [exactBandCount_eq_biasedMainClassU
    (sigma := sigma) (ell := ell)] at hnat
  simpa [majorityExact] using hnat

private theorem first_union_sample_scaled
    {init : InputCfg n} {omega : InputLog n}
    {seed allThree four five completed M C R H : ℕ}
    {Snapshot : InputCfg n → Prop}
    (hvalidInitial : validInitial init)
    (hn : timePopulationThreshold ≤ n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (hstrong : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot)
    (hseed : LateSamplingSeedReceipt init M ell.val σ
      (trace init omega four))
    (hfixed : FixedRowTwoHorizon init omega allThree four completed H)
    (hsmall :
      10000 * scaledShallowPositive σ ell.val
          (trace init omega four) ≤ 111 * (M : ℚ))
    (hnot : omega ∉ rowTwoThresholdFailure init ell hell H) :
    5697 * R ≤ 10000 * Phase6FuelLedger.twoReserveFuel
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      ell (trace init omega completed) := by
  have hMpos := main_positive hn hstrong.density
  let A0 := Nat.ceil ((5698 / 10000 : ℚ) * M)
  have hA0le : A0 ≤ M := by
    apply Nat.ceil_le.mpr
    try dsimp [A0]
    have hMnonneg : (0 : ℚ) ≤ M := by positivity
    try clear hn
    nlinarith
  let A : Fin (M + 1) := ⟨A0, by omega⟩
  have hglobal : ∀ u, four ≤ u → u ≤ completed →
      A.val ≤ classCount (indexClass (classIndices ell hell adjacentSlot))
        (labelsAt init omega u) := by
    intro u hfouru hucompleted
    have hs := first_branch_global_floor_at hvalidInitial hell
      hstrong.completion.observed_path hseed hfouru hucompleted hsmall
    apply Nat.ceil_le.mpr
    have hsQ : (5698 : ℚ) * M ≤
        10000 * classCount (indexClass (adjacentIndices ell hell))
          (labelsAt init omega u) := by
      exact_mod_cast hs
    simp only [classIndices_adjacent]
    norm_num at hsQ ⊢
    try clear hn
    nlinarith
  have hMcast : (0 : ℚ) < M := by exact_mod_cast hMpos
  have hlower : (5698 / 10000 : ℚ) * M ≤ (A0 : ℚ) := by
    simpa [A0] using Nat.le_ceil ((5698 / 10000 : ℚ) * M)
  have hratio : (1 / 40000 : ℚ) ≤ (A.val : ℚ) / M := by
    clear hn
    apply (le_div_iff₀ hMcast).2
    simp only [A]
    norm_num at hlower ⊢
    try clear hn
    nlinarith
  have hgood := acceptedGood_floor_of_not_rowTwoThresholdFailure
    hn ell hell adjacentSlot hstrong hfixed A hglobal hratio hnot
  simp only [classIndices_adjacent] at hgood
  rw [completion_acceptedGoodCount_adjacent hstrong.completion ell hell] at hgood
  have hratioLower :
      (5698 / 10000 : ℚ) ≤ (A.val : ℚ) / M := by
    apply (le_div_iff₀ hMcast).2
    simpa [A] using hlower
  apply first_alternative_sample_floor
  calc
    ((5698 / 10000 : ℚ) - 1 / 10000) * R ≤
        ((A.val : ℚ) / M - 1 / 10000) * R :=
      mul_le_mul_of_nonneg_right
        (sub_le_sub_right hratioLower _) (by positivity)
    _ ≤ Phase6FuelLedger.twoReserveFuel
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        ell (trace init omega completed) := hgood

private theorem second_union_sample_scaled
    {init : InputCfg n} {omega : InputLog n}
    {seed allThree four five completed M C R H : ℕ}
    {Snapshot : InputCfg n → Prop}
    (hn : timePopulationThreshold ≤ n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (hstrong : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot)
    (hseed : LateSamplingSeedReceipt init M ell.val σ
      (trace init omega four))
    (hfixed : FixedRowTwoHorizon init omega allThree four completed H)
    (hcredit :
      (1939 / 2000 : ℚ) * (M : ℚ) ≤
        AveragingCreditTransitions.totalCredit σ ell.val (ell.val + 1)
          (trace init omega four))
    (hnot : omega ∉ rowTwoThresholdFailure init ell hell H) :
    9389 * R ≤ 10000 * Phase6FuelLedger.twoReserveFuel
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      ell (trace init omega completed) := by
  have hMpos := main_positive hn hstrong.density
  let A0 := Nat.ceil ((939 / 1000 : ℚ) * M)
  have hA0le : A0 ≤ M := by
    apply Nat.ceil_le.mpr
    try dsimp [A0]
    have hMnonneg : (0 : ℚ) ≤ M := by positivity
    try clear hn
    nlinarith
  let A : Fin (M + 1) := ⟨A0, by omega⟩
  have hglobal : ∀ u, four ≤ u → u ≤ completed →
      A.val ≤ classCount (indexClass (classIndices ell hell adjacentSlot))
        (labelsAt init omega u) := by
    intro u hfouru hucompleted
    have hs := credit_branch_global_floor_at hell
      hstrong.completion.observed_path hseed hfouru hucompleted hcredit
    apply Nat.ceil_le.mpr
    have hsQ : (939 : ℚ) * M ≤
        1000 * classCount (indexClass (adjacentIndices ell hell))
          (labelsAt init omega u) := by
      exact_mod_cast hs
    simp only [classIndices_adjacent]
    norm_num at hsQ ⊢
    try clear hn
    nlinarith
  have hMcast : (0 : ℚ) < M := by exact_mod_cast hMpos
  have hlower : (939 / 1000 : ℚ) * M ≤ (A0 : ℚ) := by
    simpa [A0] using Nat.le_ceil ((939 / 1000 : ℚ) * M)
  have hratio : (1 / 40000 : ℚ) ≤ (A.val : ℚ) / M := by
    clear hn
    apply (le_div_iff₀ hMcast).2
    simp only [A]
    norm_num at hlower ⊢
    try clear hn
    nlinarith
  have hgood := acceptedGood_floor_of_not_rowTwoThresholdFailure
    hn ell hell adjacentSlot hstrong hfixed A hglobal hratio hnot
  simp only [classIndices_adjacent] at hgood
  rw [completion_acceptedGoodCount_adjacent hstrong.completion ell hell] at hgood
  have hratioLower :
      (939 / 1000 : ℚ) ≤ (A.val : ℚ) / M := by
    apply (le_div_iff₀ hMcast).2
    simpa [A] using hlower
  apply second_alternative_sample_floor
  calc
    ((939 / 1000 : ℚ) - 1 / 10000) * R ≤
        ((A.val : ℚ) / M - 1 / 10000) * R :=
      mul_le_mul_of_nonneg_right
        (sub_le_sub_right hratioLower _) (by positivity)
    _ ≤ Phase6FuelLedger.twoReserveFuel
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        ell (trace init omega completed) := hgood

private theorem exact_sample_scaled
    {init : InputCfg n} {omega : InputLog n}
    {seed allThree four five completed M C R H : ℕ}
    {Snapshot : InputCfg n → Prop}
    (hn : timePopulationThreshold ≤ n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (sigma : Sign)
    (hstrong : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot)
    (hseed : LateSamplingSeedReceipt init M ell.val sigma
      (trace init omega four))
    (hfixed : FixedRowTwoHorizon init omega allThree four completed H)
    (hnot : omega ∉ rowTwoThresholdFailure init ell hell H) :
    10000 * majorityExact ell sigma (trace init omega completed) * R ≤
      10000 * M * Phase6FuelLedger.reserveFuel
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        ell (trace init omega completed) + 21 * M * R := by
  let E := majorityExact ell sigma (trace init omega completed)
  have hMpos := main_positive hn hstrong.density
  by_cases hsmall : 10000 * E ≤ 21 * M
  · dsimp only [E] at hsmall ⊢
    calc 10000 * majorityExact ell sigma (trace init omega completed) * R ≤
        21 * M * R := Nat.mul_le_mul_right R hsmall
      _ ≤ _ := Nat.le_add_left _ _
  · have hbig : 21 * M < 10000 * E := Nat.lt_of_not_ge hsmall
    have hEle : E ≤ M := by
      simpa [E] using majorityExact_le_main ell hell sigma hstrong
    let A0 := Nat.ceil ((E : ℚ) - (1 / 500 : ℚ) * M)
    have hA0le : A0 ≤ M := by
      apply Nat.ceil_le.mpr
      have hEleQ : (E : ℚ) ≤ M := by exact_mod_cast hEle
      try dsimp [A0]
      try clear hn
      nlinarith
    let A : Fin (M + 1) := ⟨A0, by omega⟩
    have hglobal : ∀ u, four ≤ u → u ≤ completed →
        A.val ≤ classCount (indexClass (classIndices ell hell exactSlot))
          (labelsAt init omega u) := by
      intro u hfouru hucompleted
      have hretro :=
        LateSamplingRetrospectiveExactLevel.retrospective_exact_level_at_completion
          hstrong.completion hseed hfouru hucompleted
      rw [exactBandCount_eq_biasedMainClassU
        (sigma := sigma) (ell := ell)] at hretro
      have hbridge := exactBand_le_exactClass
        (m := init.card) sigma ell hell (labelsAt init omega u)
      rw [show labelCfg (labelsAt init omega u) = trace init omega u from
        PairLog.labelsAt_config init omega u] at hbridge
      have hretroQ : (1000 : ℚ) * E ≤
          1000 * bandCount sigma ell.val 0 (trace init omega u) + 2 * M := by
        simpa [E, majorityExact] using (show
          (1000 : ℚ) *
              Phase5Convergence.biasedMainClassU
                (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
                sigma ell (trace init omega completed) ≤
            1000 * bandCount sigma ell.val 0 (trace init omega u) + 2 * M
          from by exact_mod_cast hretro)
      have hbridgeQ :
          (bandCount sigma ell.val 0 (trace init omega u) : ℚ) ≤
            classCount (indexClass (exactIndices ell))
              (labelsAt init omega u) := by
        exact_mod_cast hbridge
      apply Nat.ceil_le.mpr
      simp only [classIndices_exact]
      try dsimp [A0]
      norm_num at hretroQ ⊢
      try clear hn
      nlinarith
    have hMcast : (0 : ℚ) < M := by exact_mod_cast hMpos
    have hceil : (E : ℚ) - (1 / 500 : ℚ) * M ≤ (A0 : ℚ) := by
      simpa [A0] using Nat.le_ceil ((E : ℚ) - (1 / 500 : ℚ) * M)
    have hratio : (1 / 40000 : ℚ) ≤ (A.val : ℚ) / M := by
      apply (le_div_iff₀ hMcast).2
      have hbigQ : (21 : ℚ) * M < 10000 * E := by exact_mod_cast hbig
      simp only [A]
      norm_num at hbigQ hceil ⊢
      try clear hn
      nlinarith
    have hgood := acceptedGood_floor_of_not_rowTwoThresholdFailure
      hn ell hell exactSlot hstrong hfixed A hglobal hratio hnot
    simp only [classIndices_exact] at hgood
    rw [completion_acceptedGoodCount_exact hstrong.completion ell] at hgood
    have hbase :
        (E : ℚ) / M - 1 / 500 ≤ (A.val : ℚ) / M := by
      apply (le_div_iff₀ hMcast).2
      simp only [A]
      have hMne : (M : ℚ) ≠ 0 := ne_of_gt hMcast
      field_simp [hMne]
      norm_num at hceil ⊢
      try clear hn
      nlinarith
    have htarget :
        ((E : ℚ) / M - 21 / 10000) * R ≤
          Phase6FuelLedger.reserveFuel
            (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
            ell (trace init omega completed) := by
      calc
        ((E : ℚ) / M - 21 / 10000) * R =
            (((E : ℚ) / M - 1 / 500) - 1 / 10000) * R := by ring
        _ ≤ ((A.val : ℚ) / M - 1 / 10000) * R :=
          mul_le_mul_of_nonneg_right
            (sub_le_sub_right hbase _) (by positivity)
        _ ≤ Phase6FuelLedger.reserveFuel
            (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
            ell (trace init omega completed) := hgood
    try dsimp only [E]
    exact exact_level_sample_floor hMpos htarget

/-! ## The completed snapshot and fuel ledger -/

/-- The repaired row-two complement produces exactly the completed
snapshot package of `LateSamplingCorrectedFuelProducer`.  `M` and `R` are then rewritten as the actual completed
label counts in the public result. -/
theorem completedRowTwoFuelSnapshot_of_good_path
    {init : InputCfg n} (hvalidInitial : validInitial init)
    {omega : InputLog n}
    {seed allThree four five completed M C R H : ℕ}
    {Snapshot : InputCfg n → Prop}
    (hn : timePopulationThreshold ≤ n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (sigma : Sign)
    (hstrong : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot)
    (hseed : LateSamplingSeedReceipt init M ell.val sigma
      (trace init omega four))
    (hfixed : FixedRowTwoHorizon init omega allThree four completed H)
    (hnot : omega ∉ rowTwoThresholdFailure init ell hell H) :
    CompletedRowTwoFuelSnapshot ell sigma
      (mainCount (labelsAt init omega completed))
      (reserveCount (labelsAt init omega completed))
      (trace init omega completed) := by
  have hupperR := massAboveScaled_cast_le_at_observed
    hstrong.completion.observed_path hseed
  have hupper :
      500 * Lemma615MassAbove.massAboveScaled
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        ell.val (trace init omega completed) ≤ M := by
    have hcast :
        (500 : ℝ) * Lemma615MassAbove.massAboveScaled
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
          ell.val (trace init omega completed) ≤ M := by
      try clear hn
      nlinarith
    exact_mod_cast hcast
  have hminorR := minorityClassU_cast_le_at_observed ell sigma
    hstrong.completion.observed_path hseed
  have hminor :
      250 * minorityExact ell sigma (trace init omega completed) ≤ M := by
    have hcast :
        (250 : ℝ) * minorityExact ell sigma
          (trace init omega completed) ≤ M := by
      simpa [minorityExact] using (show
        (250 : ℝ) *
          Phase5Convergence.biasedMainClassU
            (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
            (Phase3Post3.minoritySignOfMajority sigma) ell
            (trace init omega completed) ≤ M by
              clear hn; nlinarith)
    exact_mod_cast hcast
  have hsnapshot : CompletedRowTwoFuelSnapshot ell sigma M R
      (trace init omega completed) := by
    refine
      { upper_tail_scaled := hupper
        minority_scaled := hminor
        outcome := ?_ }
    rcases hseed.near_credit with hsmall | hcredit
    · exact RowTwoFuelOutcome.first
        (first_majority_scaled ell sigma hstrong hseed hsmall)
        (first_union_sample_scaled hvalidInitial hn ell hell
          hstrong hseed hfixed hsmall hnot)
    · exact RowTwoFuelOutcome.second
        (exact_sample_scaled hn ell hell sigma hstrong hseed hfixed hnot)
        (second_union_sample_scaled hn ell hell
          hstrong hseed hfixed hcredit hnot)
  simpa only [hstrong.completed_main, hstrong.completed_reserve] using hsnapshot

/-- Local failure union for this item.  The completion complement is retained
in the statement even though an explicit strong receipt already contains the
completion witness. -/
def completedRowTwoFuelFailure
    (init : InputCfg n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (H : ℕ) : Set (InputLog n) :=
  LateSamplingCompletion.completionFailure init n ∪
    rowTwoThresholdFailure init ell hell H

/-- Original-law bound with the literal repaired row-two exponential charge. -/
theorem law_completedRowTwoFuelFailure_tail
    (init : InputCfg n) (hcard : init.card = n)
    (hn : timePopulationThreshold ≤ n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (H : ℕ) :
    law init (completedRowTwoFuelFailure init ell hell H) ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-(6347 / 3125 : ℝ))) +
        ENNReal.ofReal
          (13 * (n : ℝ) ^ 2 *
            Real.exp (-(n : ℝ) / 800000000000000)) := by
  exact (measure_union_le _ _).trans
    (add_le_add
      (LateSamplingCompletion.law_completion_failure_tail init hn)
      (law_rowTwoThresholdFailure_tail init hcard hn ell hell H))

/-- The same local union with the inverse-power row-two envelope. -/
theorem law_completedRowTwoFuelFailure_inverse_power
    (init : InputCfg n) (hcard : init.card = n)
    (hn : timePopulationThreshold ≤ n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (H : ℕ) :
    law init (completedRowTwoFuelFailure init ell hell H) ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-(6347 / 3125 : ℝ))) +
        ENNReal.ofReal (Real.rpow (n : ℝ) (-190)) := by
  exact (measure_union_le _ _).trans
    (add_le_add
      (LateSamplingCompletion.law_completion_failure_tail init hn)
      (law_rowTwoThresholdFailure_inverse_power init hcard hn ell hell H))

/-- Pathwise composition with the strong completed density and the
corrected deterministic consumer. -/
theorem twoLevelFuelLedger_of_completed_good_path
    {init : InputCfg n} (hvalidInitial : validInitial init)
    {omega : InputLog n}
    {seed allThree four five completed M C R H : ℕ}
    {Snapshot : InputCfg n → Prop}
    (hn : timePopulationThreshold ≤ n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (sigma : Sign)
    (hstrong : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot)
    (hseed : LateSamplingSeedReceipt init M ell.val sigma
      (trace init omega four))
    (hfixed : FixedRowTwoHorizon init omega allThree four completed H)
    (hgood : omega ∉ completedRowTwoFuelFailure init ell hell H) :
    Phase6FuelLedger.TwoLevelFuelLedger
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      ell (LatePotential.fuelFloor n) (trace init omega completed) := by
  have _hcompletion :
      omega ∉ LateSamplingCompletion.completionFailure init n :=
    fun h => hgood (Or.inl h)
  have hrow : omega ∉ rowTwoThresholdFailure init ell hell H :=
    fun h => hgood (Or.inr h)
  have hsnapshot := completedRowTwoFuelSnapshot_of_good_path
    hvalidInitial hn ell hell sigma hstrong hseed hfixed hrow
  exact two_level_fuel_ledger_of_completed_snapshot
    ell sigma
    (mainCount (labelsAt init omega completed)) C
    (reserveCount (labelsAt init omega completed))
    (trace init omega completed) hn
    hstrong.completedStrongDensity hsnapshot

/-!
THEOREM LIST
* `acceptedGoodCount_add_badSampleCount`
* `completion_acceptedCount_eq_reserveCount`
* `completion_acceptedGoodCount_exact`
* `completion_acceptedGoodCount_adjacent`
* `FixedRowTwoHorizon`
* `acceptedGood_floor_of_not_rowTwoThresholdFailure`
* `completedRowTwoFuelSnapshot_of_good_path`
* `completedRowTwoFuelFailure`
* `law_completedRowTwoFuelFailure_tail`
* `law_completedRowTwoFuelFailure_inverse_power`
* `twoLevelFuelLedger_of_completed_good_path`

CLOSES
* Exact identification of completed accepted classes with `reserveFuel` and
  `twoReserveFuel`.
* The repaired threshold-aware zero-slot cover for the exact and adjacent
  classes, including the `.0001 R` loss.
* The `.002 + .0001 = .0021` exact-class route without double-spending the
  rounded retrospective allowance.
* All six constants consumed by `CompletedRowTwoFuelSnapshot`.
* Pathwise conversion to `TwoLevelFuelLedger ell (fuelFloor n)` using
  `StrongSeedReceipt.completedStrongDensity`.
* The unconditional original-law union of `completionFailure` and
  `rowTwoThresholdFailure`, in literal and inverse-power forms.

UNFINISHED
* A timer item must construct `FixedRowTwoHorizon`; this is the explicit
  cross-item input already recorded as unfinished by the repaired row-two
  family.
* The N16 `LateSamplingSeedReceipt` and the upstream `AsyncEntry`/strong-receipt
  producers retain their own already charged failure sets.  They are explicit
  hypotheses here and are not silently folded into this local two-set union.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateSamplingCompletedFuelSnapshot

end
