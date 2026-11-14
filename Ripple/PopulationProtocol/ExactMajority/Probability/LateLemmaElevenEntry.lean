-- Ripple/PopulationProtocol/ExactMajority/Probability/LateLemmaElevenEntry.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateBiasedResourceCreditPath
import Ripple.PopulationProtocol.ExactMajority.Probability.LatePhaseSixDrainSelectedLevel
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingSentinelBoundary
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingCompletedFuelSnapshot

/-!
# Lemma 11 entry at the completed small-gap snapshot

This file assembles only the five fields of `LemmaElevenEntry`.  It does not
construct the later Phase-7 or Phase-8 route fields.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateLemmaElevenEntry

open TimeTheorem PairLog StageEventSpec
open LateF6OriginalLaw LateF6Hazards
open LateSamplingCalibration
open LateStrengthening
open LateSamplingSeedReceipt LateSamplingStrongSeedReceipt
open LateSamplingStrongReceiptProducer
open LateSamplingFixedRowTwoHorizon
open LateSamplingCompletedFuelSnapshot
open LateSamplingRowTwoChoices LateSamplingRowTwoThresholdRepair
open LateSamplingSnapshotNumerics
open LateSamplingSentinelBoundary
open LateSamplingMassCountTransport
open LateSamplingShallowTransport
open LateSamplingCorrectedFuelProducer hiding InputCfg
open LatePhaseSixDrainSelectedLevel
open LateBiasedResourceCreditPath
open Phase6BlockSnapshot
open Phase7BandDefs Phase7MajorityBlockLedger
open LateAcceptedRectangleHazard

variable {L K n : ℕ}

/-! ## The retained majority block -/

/-- Excluding the opposite of `tau` is equivalent to selecting sign `tau`.
The strict upper endpoint in `majorityBand3` is the same as the inclusive
width-two endpoint in `bandCount`. -/
private theorem majorityBlockCount_opposite_eq_bandCount
    (tau : Sign) (ell : ℕ) (c : InputCfg n) :
    majorityBlockCount
        (oppositeSign tau) ell c =
      bandCount tau ell 2 c := by
  classical
  unfold majorityBlockCount bandCount
  apply Multiset.countP_congr rfl
  intro a _ha
  apply propext
  rw [majorityBand3, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hmain, s, j, hne, hbias, hlo, hhi⟩
    have hs : s = tau := by
      cases tau <;> cases s <;>
        simp [oppositeSign] at hne ⊢
    subst s
    exact ⟨hmain, j, hbias, hlo, by omega⟩
  · rintro ⟨hmain, j, hbias, hlo, hhi⟩
    refine ⟨hmain, tau, j, ?_, hbias, hlo, by omega⟩
    cases tau <;> simp [oppositeSign]

/-! ## Minority debt from the N16 mass receipt -/

private theorem cast_two_pow_sub_eq_scaled
    (e j : ℕ) (hj : j ≤ e) :
    (((2 : ℕ) ^ (e - j) : ℕ) : ℚ) =
      (2 : ℚ) ^ e * (2 : ℚ) ^ (-(j : ℤ)) := by
  push_cast
  rw [zpow_neg, zpow_natCast]
  have hp : (2 : ℚ) ^ j ≠ 0 := by positivity
  field_simp [hp]
  rw [← pow_add, Nat.sub_add_cancel hj]

private theorem minorityDebtUnit_cast_eq_scaledAtom
    (sigma : Sign) (ell : ℕ) (a : AgentState L K) :
    (minorityDebtUnit (L := L) (K := K) sigma ell a : ℚ) =
      (2 : ℚ) ^ (ell + 4) *
        (if a.role = Role.main then
          match a.bias with
          | Bias.zero => 0
          | Bias.dyadic s j =>
              if s = sigma ∧ j.val ≤ ell + 4 then
                (2 : ℚ) ^ (-(j.val : ℤ))
              else 0
        else 0) := by
  by_cases hm : a.role = Role.main
  · cases hb : a.bias with
    | zero =>
        simp [minorityDebtUnit, hm, hb]
    | dyadic s j =>
        by_cases hsj : s = sigma ∧ j.val ≤ ell + 4
        · have hp := cast_two_pow_sub_eq_scaled
            (ell + 4) j.val hsj.2
          simpa [minorityDebtUnit, hm, hb, hsj] using hp
        · simp [minorityDebtUnit, hm, hb, hsj]
  · simp [minorityDebtUnit, hm]

/-- The Phase-7 integer debt is exactly the N16 same-sign shallow mass at
cutoff `ell + 4`. -/
private theorem minorityDebt_cast_eq_scaledShallowPositive
    (sigma : Sign) (ell : ℕ) (c : InputCfg n) :
    (minorityDebt sigma ell c : ℚ) =
      scaledShallowPositive sigma (ell + 4) c := by
  classical
  induction c using Multiset.induction_on with
  | empty =>
      simp [minorityDebt, scaledShallowPositive]
  | cons a c ih =>
      simp only [minorityDebt, scaledShallowPositive,
        Multiset.map_cons, Multiset.sum_cons, Nat.cast_add] at ih ⊢
      rw [mul_add,
        minorityDebtUnit_cast_eq_scaledAtom sigma ell a,
        ih]
      by_cases hm : a.role = Role.main
      · cases hb : a.bias <;> simp [hm, hb]
      · simp [hm]

/-! ## Sentinel-safe dangerous row -/

/-- The repaired row-two family supplies the `.0769 R` protected-sample row.
At the sentinel boundary, `protectedDangerousRow_of_completion` switches to
its deterministic-zero branch. -/
private theorem protectedDangerousRow_of_entry_receipts
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    {seed allThree four five completed M C R : ℕ}
    {Snapshot : InputCfg n → Prop}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (tau : Sign)
    (hstrong : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot)
    (hseed : LateSamplingSeedReceipt init M ell.val tau
      (trace init omega four))
    (hfixed : FixedRowTwoHorizon init omega allThree four completed
      (LateTimerPrefixScalar.protectionHorizon n))
    (hnotRow : omega ∉ rowTwoThresholdFailure init ell hell
      (LateTimerPrefixScalar.protectionHorizon n)) :
    ProtectedDangerousRow ell R (trace init omega completed) := by
  apply protectedDangerousRow_of_completion
    hstrong.completion ell hell R
  intro hinterior
  have hMpos : 0 < M := by
    have hnlarge : 40 ≤ n := (time_population_bounds hinput.1).2
    have hm := hstrong.density.mains_lower
    omega
  let A0 := Nat.ceil ((9232 / 10000 : ℚ) * M)
  have hA0le : A0 ≤ M := by
    apply Nat.ceil_le.mpr
    dsimp [A0]
    have hMnonneg : (0 : ℚ) ≤ M := by positivity
    nlinarith
  let A : Fin (M + 1) := ⟨A0, by omega⟩
  have hglobal : ∀ u, four ≤ u → u ≤ completed →
      A.val ≤
        classCount (indexClass (classIndices ell hell protectedSlot))
          (labelsAt init omega u) := by
    intro u hfouru hucompleted
    have hs := protected_global_floor_at
      hell hinterior hfixed.path hseed hfouru
      (hucompleted.trans hfixed.completed_le)
    apply Nat.ceil_le.mpr
    have hsQ :
        (9232 : ℚ) * M ≤
          10000 * classCount
            (indexClass (protectedIndices ell hell))
            (labelsAt init omega u) := by
      exact_mod_cast hs
    simp only [classIndices_protected]
    norm_num at hsQ ⊢
    nlinarith
  have hMcast : (0 : ℚ) < M := by exact_mod_cast hMpos
  have hlower :
      (9232 / 10000 : ℚ) * M ≤ (A0 : ℚ) := by
    simpa [A0] using
      (Nat.le_ceil ((9232 / 10000 : ℚ) * M))
  have hratio :
      (1 / 40000 : ℚ) ≤ (A.val : ℚ) / M := by
    apply (le_div_iff₀ hMcast).2
    simp only [A]
    norm_num at hlower ⊢
    nlinarith
  have hgoodAccepted :=
    acceptedGood_floor_of_not_rowTwoThresholdFailure
      hinput.1 ell hell protectedSlot hstrong hfixed A
      hglobal hratio hnotRow
  simp only [classIndices_protected] at hgoodAccepted
  have hcomplete := acceptedGoodCount_add_badSampleCount
    (protectedIndices ell hell) (labelsAt init omega completed)
  rw [completion_acceptedCount_eq_reserveCount hstrong.completion,
    hstrong.completed_reserve] at hcomplete
  have hratioLower :
      (9232 / 10000 : ℚ) ≤ (A.val : ℚ) / M := by
    apply (le_div_iff₀ hMcast).2
    simpa [A] using hlower
  have hprotected :
      ((9232 / 10000 : ℚ) - 1 / 10000) * R ≤
        acceptedGoodCount (protectedIndices ell hell)
          (labelsAt init omega completed) := by
    calc
      ((9232 / 10000 : ℚ) - 1 / 10000) * R ≤
          ((A.val : ℚ) / M - 1 / 10000) * R := by
        exact mul_le_mul_of_nonneg_right
          (sub_le_sub_right hratioLower _) (by positivity)
      _ ≤ acceptedGoodCount (protectedIndices ell hell)
          (labelsAt init omega completed) := hgoodAccepted
  exact dangerous_sample_ceiling hcomplete hprotected

/-! ## Entry assembly from the concrete receipts -/

/-- Deterministic consumer of the completed row-two receipt.  The only failure
input is the already named snapshot-production union. -/
theorem lemmaElevenEntry_of_completed_receipts
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    {seed allThree four five completed M C R : ℕ}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (tau : Sign)
    (hseed : LateSamplingSeedReceipt init M ell.val tau
      (trace init omega four))
    (hstrong : StrongSeedReceipt init omega seed allThree four five completed
      M C R (CompletedRowTwoFuelSnapshot ell tau M R))
    (hnotSnapshot :
      omega ∉ smallRowTwoSnapshotProductionFailure init) :
    LemmaElevenEntry (M := M) (R := R) ell hell
      (oppositeSign tau) tau (trace init omega completed) := by
  have hnotStrong : omega ∉ strongSnapshotProductionFailure init := by
    intro hbad
    apply hnotSnapshot
    exact Or.inr hbad
  have hnotFixed :
      omega ∉ fixedRowTwoHorizonProductionFailure init := by
    intro hbad
    apply hnotStrong
    exact Or.inl hbad
  have hnotAny : omega ∉ anyRowTwoThresholdFailure init := by
    intro hbad
    apply hnotStrong
    exact Or.inr hbad
  have hfixed := fixedRowTwoHorizon_of_not_productionFailure
    hinput ell hell tau hstrong hseed hnotFixed
  have hnotRow := not_rowTwoThresholdFailure_of_not_any
    init ell hell hnotAny
  have hpath := hstrong.completion.observed_path
  have hmainTime :
      timeMainCount (trace init omega completed) = M :=
    (labelMainCount_eq_trace init omega completed).symm.trans
      hstrong.completed_main
  have hmain :
      RoleSplitConcentration.mainCount
        (trace init omega completed) = M := by
    change timeMainCount (trace init omega completed) = M
    exact hmainTime
  have hprotected :
      9232 * M ≤
        10000 * bandCount tau ell.val 2
          (trace init omega completed) :=
    LateSamplingSeedReceipt.protectedBand_at
      hpath hseed hpath.observed le_rfl hmainTime
  have hblock :
      920 * M ≤
        1000 * majorityBlockCount (oppositeSign tau) ell.val
          (trace init omega completed) := by
    rw [majorityBlockCount_opposite_eq_bandCount]
    omega
  have htransport :=
    scaledShallowPositive_seed_mono
      (ell := ell.val + 4) (σ := oppositeSign tau)
      hpath hpath.observed le_rfl
  have hseedMass :=
    scaledShallowPositive_le_scaledSignMass
      (oppositeSign tau) (ell.val + 4) (trace init omega four)
  have hdebtQ :
      (minorityDebt (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
          (oppositeSign tau) ell.val
          (trace init omega completed) : ℚ) ≤
        (2 : ℚ) ^ (ell.val + 4) *
          signMass (oppositeSign tau) (trace init omega four) := by
    rw [minorityDebt_cast_eq_scaledShallowPositive]
    exact htransport.trans hseedMass
  have hpow :
      (2 : ℚ) ^ (ell.val + 4) =
        16 * (2 : ℚ) ^ ell.val := by
    norm_num [pow_add, mul_comm]
  rw [hpow] at hdebtQ
  have hminorQ :
      (1000 : ℚ) *
          minorityDebt (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
            (oppositeSign tau) ell.val
            (trace init omega completed) ≤
        64 * M := by
    nlinarith only [hdebtQ, hseed.toSmallReadout.minority]
  have hminor :
      1000 * minorityDebt (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
          (oppositeSign tau) ell.val
          (trace init omega completed) ≤
        64 * M := by
    exact_mod_cast hminorQ
  have hprotectedRow := protectedDangerousRow_of_entry_receipts
    hinput ell hell tau hstrong hseed hfixed hnotRow
  have hreserve := hstrong.density.reserves_upper
  have hmains := hstrong.density.mains_lower
  have hRM : 769 * R ≤ 500 * M := by omega
  have hdanger :
      1000 * dangerousReserveCount
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
          ell.val (trace init omega completed) ≤
        50 * M := by
    unfold ProtectedDangerousRow at hprotectedRow
    omega
  exact
    { snapshot := hstrong.completion.snapshot
      block := hblock
      main_count := hmain
      minority := hminor
      dangerous := hdanger }

/-- Entry-only small-history producer.  `sigma` is the excluded sign and
`tau` is the N16 winning/snapshot sign.  `M`, `R`, and `completed` are the
literal witnesses returned by `exists_completedFuelLedger_of_smallHistory`. -/
theorem exists_lemmaElevenEntry_of_smallHistory
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    (hsmall : omega ∈ smallHistory init)
    (hgood : omega ∉ smallGapPhaseSixDrainFailure init) :
    ∃ seed allThree four : ℕ,
      ∃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
      ∃ hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n,
      ∃ sigma tau : Sign, ∃ five completed M R : ℕ,
        sigma = oppositeSign tau ∧
          M = timeMainCount (trace init omega seed) ∧
          R = StageEventSpec.reserveCount (trace init omega seed) ∧
          LemmaElevenEntry (M := M) (R := R) ell hell sigma tau
            (trace init omega completed) := by
  have hnotSnapshot :
      omega ∉ smallRowTwoSnapshotProductionFailure init := by
    intro hbad
    apply hgood
    exact Or.inl hbad
  obtain ⟨seed, allThree, four, ell, hell, tau, five, completed,
      _hhistory, hseed, hstrong, _hledger⟩ :=
    exists_completedFuelLedger_of_smallHistory
      hinput hsmall hnotSnapshot
  refine ⟨seed, allThree, four, ell, hell, oppositeSign tau, tau,
    five, completed,
    timeMainCount (trace init omega seed),
    StageEventSpec.reserveCount (trace init omega seed),
    rfl, rfl, rfl, ?_⟩
  exact lemmaElevenEntry_of_completed_receipts
    (M := timeMainCount (trace init omega seed))
    (C := clockCount (trace init omega seed))
    (R := StageEventSpec.reserveCount (trace init omega seed))
    hinput ell hell tau hseed hstrong hnotSnapshot

/-!
THEOREM LIST
* `lemmaElevenEntry_of_completed_receipts`
* `exists_lemmaElevenEntry_of_smallHistory`

CLOSES
* `LemmaElevenEntry.snapshot` from
  `StrongSeedReceipt.completion.snapshot`.
* `LemmaElevenEntry.block` from `LateSamplingSeedReceipt.protectedBand_at`
  and the opposite-sign block/count identity.
* `LemmaElevenEntry.main_count` from `completed_main` and
  `labelMainCount_eq_trace`.
* `LemmaElevenEntry.minority` directly from the N16 minority mass receipt and
  `scaledShallowPositive_seed_mono`; no Phase-3/4 reachability premise is
  introduced.
* `LemmaElevenEntry.dangerous` from the sentinel-safe `.0769 R` row and
  `StrongSeedDensity`; the false `9 * R ≤ 5 * M` premise is not used.

CARRIED PREMISES AND PRODUCERS
* `hinput : GoodInput n init`: caller input; it is the premise of
  `exists_completedFuelLedger_of_smallHistory` and of the existing failure
  bound `law_smallGapPhaseSixDrainFailure`.
* `hsmall : omega ∈ smallHistory init`: caller branch membership.
* `hgood : omega ∉ smallGapPhaseSixDrainFailure init`: the one existing named
  complement.  It yields the snapshot-production complement used here.
* `hseed`, `hstrong`, the selected `ell`, `hell`, `tau`, and the times/counts
  are all produced by `exists_completedFuelLedger_of_smallHistory`.
* No all-log/configuration premise and no additional failure set is carried.

UNFINISHED
* `before_seven`, `after_seven`, `eight_seed`, and the assembly of
  `LemmaElevenPathReceipt` are intentionally absent; they belong to later files.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateLemmaElevenEntry

end
