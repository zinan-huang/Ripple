-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingSentinelBoundary.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingRowTwoThresholdRepair
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingSnapshotNumerics
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6BlockSnapshot

/-!
# N18 row two: the protected-class sentinel boundary

At `ell + 2 = L`, the upper raw bias level is the same `Fin (L+1)` value as
`sampleUnset`.  It is a real Main-bias index, but it is not an F6-eligible
sample index.  Therefore the strict-interior `.9232 M` class-floor argument
must not be reused verbatim.  The consumer-facing protected statement is
stronger and simpler at the boundary: no Reserve hour can be strictly above
`ell + 2 = L`, so the operational dangerous-Reserve count is zero.

This file is deterministic.  It neither changes the finite union nor adds a
probability charge.
-/

noncomputable section

open scoped BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingSentinelBoundary

open TimeTheorem PairLog
open LateF6Acceptance LateF6Hazards
open LateAcceptedRectangleHazard
open LateSamplingRowTwoChoices
open LateSamplingCompletion

variable {L K m n : ℕ}

/-- At the boundary, the nominal third protected index is literally the
Reserve `sampleUnset` sentinel. -/
theorem upperIndex_eq_sampleUnset_of_boundary
    (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (hboundary : ell.val + 2 = L) :
    upperIndex ell hell = (sampleUnset : Fin (L + 1)) := by
  apply Fin.ext
  simpa [upperIndex, sampleUnset] using hboundary

/-- Formal obstruction to the false literal extension of
`protected_global_floor_at`: the upper raw band index belongs to the three
index set, but its bias is excluded by `indexClass` because it is not F6
eligible. -/
theorem sentinel_bias_mem_protected_not_indexClass
    (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (hboundary : ell.val + 2 = L) (sigma : Sign) :
    upperIndex ell hell ∈ protectedIndices ell hell ∧
      ¬ indexClass (protectedIndices ell hell)
        (.dyadic sigma (upperIndex ell hell)) := by
  constructor
  · simp [protectedIndices]
  · simp only [indexClass]
    rintro ⟨_, hlt⟩
    have htop : (upperIndex ell hell).val = L := by
      simpa [upperIndex] using hboundary
    omega

/-- A genuine accepted write can never store the sentinel.  This is the
implemented-protocol version of “no accepted sentinel sample.” -/
theorem accepted_output_ne_sampleUnset
    (r r' : AgentState L K) (haccepted : Accepted r r') :
    r'.hour ≠ (sampleUnset : Fin (L + 1)) := by
  intro heq
  have hval := congrArg Fin.val heq
  have hsentinel : r'.hour.val = L := by
    simpa [sampleUnset] using hval
  have hlt : r'.hour.val < L := haccepted.2.2.2.2
  omega

/-- Hence every stored accepted sample lies at or below the protected top in
the sentinel-boundary case. -/
theorem acceptedReserve_hour_le_protected_top_of_boundary
    (ell : Fin (L + 1)) (hboundary : ell.val + 2 = L)
    (a : AgentState L K) (haccepted : AcceptedReserve a) :
    a.hour.val ≤ ell.val + 2 := by
  have hlt : a.hour.val < L := haccepted.2.2
  omega

/-- On an all-sampled configuration, the nominal upper protected sample class
is empty at the boundary.  In particular, replacing the eligible class by a
class that “includes level `L`” would not create accepted samples. -/
theorem sampledReserveClassU_upperIndex_eq_zero_of_boundary
    (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (hboundary : ell.val + 2 = L)
    (c : Config (AgentState L K))
    (hsampled : ReserveSampling.ReserveSampled c) :
    Phase5Convergence.sampledReserveClassU
      (L := L) (K := K) (upperIndex ell hell) c = 0 := by
  unfold Phase5Convergence.sampledReserveClassU
  apply Multiset.countP_eq_zero.mpr
  intro a ha hclass
  change a.role = Role.reserve ∧
    a.hour.val = (upperIndex ell hell).val at hclass
  rcases hclass with ⟨hrole, hhour⟩
  have hnot : ¬ ReserveSampling.unsampled (L := L) (K := K) a := by
    unfold ReserveSampling.ReserveSampled
      ReserveSampling.unsampledReserveU at hsampled
    exact (Multiset.countP_eq_zero.mp hsampled) a ha
  apply hnot
  refine ⟨hrole, ?_⟩
  calc
    a.hour.val = (upperIndex ell hell).val := hhour
    _ = L := by simpa [upperIndex] using hboundary

/-- Since `indexClass` already enforces index `< L`, adding the raw upper
sentinel index to the protected Finset changes nothing at the boundary. -/
theorem indexClass_protected_eq_adjacent_of_boundary
    (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (hboundary : ell.val + 2 = L) :
    indexClass (protectedIndices ell hell) =
      indexClass (adjacentIndices ell hell) := by
  funext b
  apply propext
  cases b with
  | zero =>
      simp [indexClass]
  | dyadic sigma j =>
      simp only [indexClass]
      constructor
      · rintro ⟨hj, hjlt⟩
        refine ⟨?_, hjlt⟩
        simp only [protectedIndices, Finset.mem_insert,
          Finset.mem_singleton] at hj
        simp only [adjacentIndices, Finset.mem_insert,
          Finset.mem_singleton]
        rcases hj with hj | hj | hj
        · exact Or.inl hj
        · exact Or.inr hj
        · have htop : j.val = L := by
            rw [hj]
            simpa [upperIndex] using hboundary
          omega
      · rintro ⟨hj, hjlt⟩
        refine ⟨?_, hjlt⟩
        simp only [adjacentIndices, Finset.mem_insert,
          Finset.mem_singleton] at hj
        simp only [protectedIndices, Finset.mem_insert,
          Finset.mem_singleton]
        rcases hj with hj | hj
        · exact Or.inl hj
        · exact Or.inr (Or.inl hj)

/-- Count-level form of the preceding collapse.  This records explicitly why
the `.9232 M` protected class floor is not a new third-level floor at the
boundary. -/
theorem classCount_protected_eq_adjacent_of_boundary
    (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (hboundary : ell.val + 2 = L)
    (f : Fin m → AgentState L K) :
    classCount (indexClass (protectedIndices ell hell)) f =
      classCount (indexClass (adjacentIndices ell hell)) f := by
  rw [indexClass_protected_eq_adjacent_of_boundary ell hell hboundary]

private theorem reserve_hour_lt_of_sampled
    {c : Config (AgentState L K)}
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

private theorem label_mem_trace
    (init : InputCfg n) (omega : InputLog n) (u : ℕ)
    (i : Fin init.card) :
    labelsAt init omega u i ∈ trace init omega u := by
  rw [← PairLog.labelsAt_config init omega u]
  exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩

/-- The operational dangerous-Reserve count is identically zero at the
sentinel boundary.  This does not need completion, a class floor, or any
probability event. -/
theorem dangerousReserveCount_eq_zero_of_boundary
    (ell : Fin (L + 1)) (hboundary : ell.val + 2 = L)
    (c : Config (AgentState L K)) :
    Phase6BlockSnapshot.dangerousReserveCount
      (L := L) (K := K) ell.val c = 0 := by
  unfold Phase6BlockSnapshot.dangerousReserveCount
  apply Multiset.countP_eq_zero.mpr
  intro a _ hdanger
  rcases hdanger with ⟨_, hdanger⟩
  have hbound := a.hour.isLt
  omega

/-- In the strict interior, every operationally dangerous completed sample is
among the samples outside the protected three-index Finset.  Samples below
`ell` may also be counted on the right, which is harmless for the upper bound.
This is the bridge from the row-two accepted-sample ceiling to the Phase-6
consumer's dangerous-Reserve observable. -/
theorem completion_dangerousReserveCount_le_badSampleCount
    {init : InputCfg n} {omega : InputLog n}
    {a four five u : ℕ} {Snapshot : InputCfg n → Prop}
    (hcompletion : CompletionReceipt init omega a four five u Snapshot)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n) :
    Phase6BlockSnapshot.dangerousReserveCount
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        ell.val (trace init omega u) ≤
      badSampleCount (protectedIndices ell hell)
        (labelsAt init omega u) := by
  unfold Phase6BlockSnapshot.dangerousReserveCount
  have hc := AveragingLiveProduct.countP_labelCfg
    (labelsAt init omega u)
    (fun a : AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 =>
      a.role = Role.reserve ∧ ell.val + 2 < a.hour.val)
  rw [← show trace init omega u = labelCfg (labelsAt init omega u) from
    (PairLog.labelsAt_config init omega u).symm] at hc
  rw [hc]
  unfold LateF6Hazards.badSampleCount
  apply Finset.card_le_card
  intro i hi
  have hdanger :
      (labelsAt init omega u i).role = Role.reserve ∧
        ell.val + 2 < (labelsAt init omega u i).hour.val := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
  rw [LateF6Hazards.mem_pool]
  change AcceptedReserve (labelsAt init omega u i) ∧
    (labelsAt init omega u i).hour ∉ protectedIndices ell hell
  refine ⟨?_, ?_⟩
  · refine ⟨hdanger.1, ?_, ?_⟩
    · exact hcompletion.complete.phase_five _
        (label_mem_trace init omega u i)
    · exact reserve_hour_lt_of_sampled
        hcompletion.complete.sampled
        (label_mem_trace init omega u i) hdanger.1
  · intro hmem
    simp only [protectedIndices, Finset.mem_insert,
      Finset.mem_singleton] at hmem
    rcases hmem with hmem | hmem | hmem
    · have hval := congrArg Fin.val hmem
      omega
    · have hval := congrArg Fin.val hmem
      simp [adjacentIndex, Phase6FuelLedger.highIndex] at hval
      omega
    · have hval := congrArg Fin.val hmem
      simp [upperIndex] at hval
      omega

/-- Consumer-facing protected row.  It is deliberately stated with the
actual Phase-6 dangerous-Reserve observable, not with the false boundary
extension of `classCount (indexClass protectedIndices)`. -/
def ProtectedDangerousRow
    (ell : Fin (L + 1)) (R : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  10000 * Phase6BlockSnapshot.dangerousReserveCount
      (L := L) (K := K) ell.val c ≤
    769 * R

/-- Boundary branch of the protected row. -/
theorem protectedDangerousRow_boundary
    (ell : Fin (L + 1)) (hboundary : ell.val + 2 = L)
    (R : ℕ) (c : Config (AgentState L K)) :
    ProtectedDangerousRow ell R c := by
  unfold ProtectedDangerousRow
  rw [dangerousReserveCount_eq_zero_of_boundary ell hboundary]
  omega

/-- Exact non-strict-boundary repair used in the construction of
`CompletionProducer.class_floors`.

The strict-interior hypothesis is precisely the `.0769 R` bad-sample ceiling
produced by the repaired finite union.  At equality no such class-floor input
is needed: the dangerous count is deterministically zero. -/
theorem protectedDangerousRow_of_completion
    {init : InputCfg n} {omega : InputLog n}
    {a four five u : ℕ} {Snapshot : InputCfg n → Prop}
    (hcompletion : CompletionReceipt init omega a four five u Snapshot)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (R : ℕ)
    (hinterior :
      ell.val + 2 < PhaseThreeModel.Numeric.hourIndex n →
      10000 * badSampleCount (protectedIndices ell hell)
          (labelsAt init omega u) ≤
        769 * R) :
    ProtectedDangerousRow ell R (trace init omega u) := by
  by_cases hstrict :
      ell.val + 2 < PhaseThreeModel.Numeric.hourIndex n
  · unfold ProtectedDangerousRow
    have hsubset :=
      completion_dangerousReserveCount_le_badSampleCount
        hcompletion ell hell
    have hceiling := hinterior hstrict
    omega
  · have hboundary :
        ell.val + 2 = PhaseThreeModel.Numeric.hourIndex n := by
      omega
    exact protectedDangerousRow_boundary
      (K := 256) ell hboundary R (trace init omega u)

/-!
THEOREM LIST
* `upperIndex_eq_sampleUnset_of_boundary`
* `sentinel_bias_mem_protected_not_indexClass`
* `accepted_output_ne_sampleUnset`
* `acceptedReserve_hour_le_protected_top_of_boundary`
* `sampledReserveClassU_upperIndex_eq_zero_of_boundary`
* `indexClass_protected_eq_adjacent_of_boundary`
* `classCount_protected_eq_adjacent_of_boundary`
* `dangerousReserveCount_eq_zero_of_boundary`
* `completion_dangerousReserveCount_le_badSampleCount`
* `protectedDangerousRow_boundary`
* `protectedDangerousRow_of_completion`

CLOSES
* The sentinel-boundary counterexample is isolated at the exact false
  statement: the raw three-level class is not an eligible accepted class.
* The implemented F6 rule is classified: an accepted sentinel sample is
  impossible; a write of exponent `L` remains unset.
* The protected dangerous-sample row now holds under
  `ell.val + 2 ≤ L`, by strict-interior concentration or deterministic zero at
  equality.
* The result is in the completion-time form used while constructing
  `CompletionProducer.class_floors`.

EXPLICIT INPUTS
* `CompletionReceipt`, to identify the completed Phase-5 sample pool in the
  strict-interior bridge.
* Only in the strict-interior branch, the repaired finite-union ceiling
  `10000 * badSampleCount ... ≤ 769 * R` supplied by the counter tab.
* The equality branch has no stochastic or future-success input.

UNFINISHED
* Assemble this protected row with the exact-level and two adjacent-level rows
  into the full `CompletionProducer.class_floors` producer.
* The threshold-counter re-instantiation remains separate.
* The row-two headline and its later consumer assembly remain separate items.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateSamplingSentinelBoundary

end
