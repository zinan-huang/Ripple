-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingRowTwoChoices.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateAcceptedTrialSlot
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingRetrospectiveExactLevel
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingFirstBranchShape

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingRowTwoChoices

open TimeTheorem PairLog StageEventSpec
open LateF6Hazards LateF6OriginalLaw
open LateSamplingCalibration LateFrozenPoolOriginalLaw
open LateAcceptedRectangleHazard LateAcceptedTrialSlot
open LateSamplingSeedReceipt LateStrengthening LateSamplingClassGates

variable {L K m n : ℕ}

/-- The three rows of the finite `Fin 3` family. -/
def exactSlot : Fin 3 := ⟨0, by decide⟩

def adjacentSlot : Fin 3 := ⟨1, by decide⟩

def protectedSlot : Fin 3 := ⟨2, by decide⟩

/-- The adjacent exponent as a genuine `Fin (L+1)` value. -/
def adjacentIndex
    (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L) : Fin (L + 1) :=
  Phase6FuelLedger.highIndex ell hell

/-- The upper protected exponent.  It may equal the sentinel `L`; that
boundary is handled separately below. -/
def upperIndex
    (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L) : Fin (L + 1) :=
  ⟨ell.val + 2, by omega⟩

noncomputable def exactIndices (ell : Fin (L + 1)) : Finset (Fin (L + 1)) :=
  {ell}

noncomputable def adjacentIndices
    (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L) : Finset (Fin (L + 1)) :=
  {ell, adjacentIndex ell hell}

noncomputable def protectedIndices
    (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L) : Finset (Fin (L + 1)) :=
  {ell, adjacentIndex ell hell, upperIndex ell hell}

/-- Literal specialization of the three `ClassTestIndex` class rows. -/
noncomputable def classIndices
    (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (i : Fin 3) : Finset (Fin (L + 1)) :=
  if i = exactSlot then exactIndices ell
  else if i = adjacentSlot then adjacentIndices ell hell
  else protectedIndices ell hell

@[simp] theorem classIndices_exact
    (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L) :
    classIndices ell hell exactSlot = exactIndices ell := by
  simp [classIndices]

@[simp] theorem classIndices_adjacent
    (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L) :
    classIndices ell hell adjacentSlot = adjacentIndices ell hell := by
  simp [classIndices, exactSlot, adjacentSlot]

@[simp] theorem classIndices_protected
    (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L) :
    classIndices ell hell protectedSlot = protectedIndices ell hell := by
  simp [classIndices, exactSlot, adjacentSlot, protectedSlot]

/-- The class predicate is locked at the genuine threshold-four prefix.  It
contains no future argument. -/
noncomputable def rowTwoClassChoice
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n) :
    ClassChoice n :=
  fun _s _p i => indexClass (classIndices ell hell i)

/-- The accepted-trial index set is the same frozen class, independently of
which integer floor `A` is selected by the finite family. -/
noncomputable def rowTwoIndexChoice
    (init : InputCfg n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n) :
    AcceptedIndexChoice init :=
  fun _s _p i _A => classIndices ell hell i

/-- Placeholder prefix-measurable horizon.  The pathwise producer must prove
that the repaired stopped counter has reached and retained its terminal value
by this horizon. -/
def constantHorizonChoice (init : InputCfg n) (H : ℕ) :
    AcceptedHorizonChoice init :=
  fun _s _p _i _A => H

/-- The finite original-law row-two family at the genuine `firstFourStart`. -/
def rowTwoFailure
    (init : InputCfg n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (H : ℕ) : Set (InputLog n) :=
  originalPrerequisiteWithAcceptedFailure init
    (rowTwoClassChoice ell hell)
    (rowTwoIndexChoice init ell hell)
    (constantHorizonChoice init H)

/-- The requested original-law charge.  This is unconditional and uses the
actual first threshold-four stopping line through
`law_stopping_selected_bound`. -/
theorem law_rowTwoFailure_tail
    (init : InputCfg n) (hcard : init.card = n)
    (hn : timePopulationThreshold ≤ n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (H : ℕ) :
    law init (rowTwoFailure init ell hell H) ≤
      ENNReal.ofReal
        (13 * (n : ℝ) ^ 2 *
          Real.exp (-(n : ℝ) / 800000000000000)) := by
  exact law_prerequisites_withAccepted_tail init hcard hn
    (rowTwoClassChoice ell hell)
    (rowTwoIndexChoice init ell hell)
    (constantHorizonChoice init H)

/-- Inverse-power form of the same single-law estimate. -/
theorem law_rowTwoFailure_inverse_power
    (init : InputCfg n) (hcard : init.card = n)
    (hn : timePopulationThreshold ≤ n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (H : ℕ) :
    law init (rowTwoFailure init ell hell H) ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-190)) := by
  exact law_prerequisites_withAccepted_inverse_power init hcard hn
    (rowTwoClassChoice ell hell)
    (rowTwoIndexChoice init ell hell)
    (constantHorizonChoice init H)

/-! ## Configuration counts versus the frozen class predicates -/

/-- A signed band is contained in any unsigned stored-index class containing
all of its exponent indices. -/
theorem bandCount_labelCfg_le_classCount
    (σ : Sign) (ell width : ℕ)
    (J : Finset (Fin (PhaseThreeModel.Numeric.hourIndex n + 1)))
    (f : Fin m → AgentState (PhaseThreeModel.Numeric.hourIndex n) 256)
    (hJ : ∀ j : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
      ell ≤ j.val → j.val ≤ ell + width → j ∈ J)
    (hstrict : ∀ j : Fin (PhaseThreeModel.Numeric.hourIndex n + 1), j ∈ J →
      j.val < PhaseThreeModel.Numeric.hourIndex n) :
    bandCount σ ell width (PairLog.labelCfg f) ≤
      classCount (indexClass J) f := by
  classical
  unfold StageEventSpec.bandCount
  rw [AveragingLiveProduct.countP_labelCfg]
  unfold LateF6Hazards.classCount LateF6Hazards.pool
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    LateF6Hazards.MainClass, LateF6Hazards.Main] at hi ⊢
  rcases hi with ⟨hrole, j, hbias, hlo, hhi⟩
  refine ⟨hrole, ?_⟩
  rw [hbias]
  simpa [LateAcceptedRectangleHazard.indexClass] using
    (show j ∈ J ∧ j.val < PhaseThreeModel.Numeric.hourIndex n from
      ⟨hJ j hlo hhi, hstrict j (hJ j hlo hhi)⟩)

/-- Exact-level class bridge. -/
theorem exactBand_le_exactClass
    (σ : Sign) (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (f : Fin m → AgentState (PhaseThreeModel.Numeric.hourIndex n) 256) :
    bandCount σ ell.val 0 (PairLog.labelCfg f) ≤
      classCount (indexClass (exactIndices ell)) f := by
  apply bandCount_labelCfg_le_classCount σ ell.val 0
      (exactIndices ell) f
  · intro j hlo hhi
    have hj : j.val = ell.val := by omega
    have hje : j = ell := Fin.ext hj
    simp [exactIndices, hje]
  · intro j hj
    simp only [exactIndices, Finset.mem_singleton] at hj
    subst j
    omega

/-- Width-two class bridge. -/
theorem adjacentBand_le_adjacentClass
    (σ : Sign) (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (f : Fin m → AgentState (PhaseThreeModel.Numeric.hourIndex n) 256) :
    bandCount σ ell.val 1 (PairLog.labelCfg f) ≤
      classCount (indexClass (adjacentIndices ell hell)) f := by
  apply bandCount_labelCfg_le_classCount σ ell.val 1
      (adjacentIndices ell hell) f
  · intro j hlo hhi
    by_cases hj : j.val = ell.val
    · have hje : j = ell := Fin.ext hj
      simp [adjacentIndices, hje]
    · have hjnext : j.val = ell.val + 1 := by omega
      have hje : j = adjacentIndex ell hell := by
        apply Fin.ext
        simpa [adjacentIndex, Phase6FuelLedger.highIndex] using hjnext
      simp [adjacentIndices, hje]
  · intro j hj
    simp only [adjacentIndices, Finset.mem_insert,
      Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · omega
    · simp [adjacentIndex, Phase6FuelLedger.highIndex]
      omega

/-- Width-three class bridge in the strict interior.  The strict inequality is
necessary because `indexClass` excludes the sentinel index `L`. -/
theorem protectedBand_le_protectedClass
    (σ : Sign) (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (hinterior : ell.val + 2 < PhaseThreeModel.Numeric.hourIndex n)
    (f : Fin m → AgentState (PhaseThreeModel.Numeric.hourIndex n) 256) :
    bandCount σ ell.val 2 (PairLog.labelCfg f) ≤
      classCount (indexClass (protectedIndices ell hell)) f := by
  apply bandCount_labelCfg_le_classCount σ ell.val 2
      (protectedIndices ell hell) f
  · intro j hlo hhi
    have hcases :
        j.val = ell.val ∨
          j.val = ell.val + 1 ∨
          j.val = ell.val + 2 := by omega
    rcases hcases with h | h | h
    · have hje : j = ell := Fin.ext h
      simp [protectedIndices, hje]
    · have hje : j = adjacentIndex ell hell := by
        apply Fin.ext
        simpa [adjacentIndex, Phase6FuelLedger.highIndex] using h
      simp [protectedIndices, hje]
    · have hje : j = upperIndex ell hell := by
        apply Fin.ext
        simpa [upperIndex] using h
      simp [protectedIndices, hje]
  · intro j hj
    simp only [protectedIndices, Finset.mem_insert,
      Finset.mem_singleton] at hj
    rcases hj with rfl | hj
    · omega
    · rcases hj with rfl | rfl
      · simp [adjacentIndex, Phase6FuelLedger.highIndex]
        omega
      · simpa [upperIndex] using hinterior

/-! ## Global floors at every actual observed prefix -/

/-- The combined-potential argument, followed by the exact-class bridge.
This is the valid retrospective replacement for the false bare exact-level
monotonicity claim. -/
theorem exact_global_allowance_at_completion
    {init : InputCfg n} {ω : InputLog n}
    {a four five u v M : ℕ} {σ : Sign}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    {Snapshot : InputCfg n → Prop}
    (hcompletion : LateSamplingCompletion.CompletionReceipt
      init ω a four five u Snapshot)
    (hseed : LateSamplingSeedReceipt init M ell.val σ
      (trace init ω four))
    (hfourv : four ≤ v) (hvu : v ≤ u) :
    10000 * bandCount σ ell.val 0 (trace init ω u) ≤
      10000 * classCount (indexClass (exactIndices ell))
          (labelsAt init ω v) +
        21 * M := by
  have hretro :=
    LateSamplingRetrospectiveExactLevel.retrospective_sampling_allowance_at_completion
        hcompletion hseed hfourv hvu
  have hbridge := exactBand_le_exactClass
    (m := init.card) σ ell hell (labelsAt init ω v)
  rw [show PairLog.labelCfg (labelsAt init ω v) = trace init ω v from
    PairLog.labelsAt_config init ω v] at hbridge
  omega

/-- Fixed first branch of `near_credit`: `.5698 M` is a global width-two
class floor at every observed prefix. -/
theorem first_branch_global_floor_at
    {init : InputCfg n} (hvalid : validInitial init)
    {ω : InputLog n} {a four u v M : ℕ} {σ : Sign}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (hpath : Prefix init ω a four u)
    (hseed : LateSamplingSeedReceipt init M ell.val σ
      (trace init ω four))
    (hfourv : four ≤ v) (hvu : v ≤ u)
    (hsmall :
      10000 * scaledShallowPositive σ ell.val (trace init ω four) ≤
        111 * (M : ℚ)) :
    5698 * M ≤
      10000 * classCount (indexClass (adjacentIndices ell hell))
        (labelsAt init ω v) := by
  have hshape := LateSamplingFirstBranchShape.firstBranchShapeData_at
    hvalid hpath hseed hfourv hvu
  have htransport :=
    LateSamplingShallowTransport.scaledShallowPositive_seed_mono
      (ell := ell.val) (σ := σ) hpath hfourv hvu
  have hband :=
    LateSamplingClassReceiptArithmetic.shallow_two_class_at
      hpath hseed hfourv hvu hsmall htransport
      hshape.level_weight hshape.mass_shape hshape.partition
  have hbridge := adjacentBand_le_adjacentClass
    (m := init.card) σ ell hell (labelsAt init ω v)
  rw [show PairLog.labelCfg (labelsAt init ω v) = trace init ω v from
    PairLog.labelsAt_config init ω v] at hbridge
  omega

/-- Fixed credit branch of `near_credit`: `.939 M` is the global width-two
class floor at every observed prefix. -/
theorem credit_branch_global_floor_at
    {init : InputCfg n} {ω : InputLog n}
    {a four u v M : ℕ} {σ : Sign}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (hpath : Prefix init ω a four u)
    (hseed : LateSamplingSeedReceipt init M ell.val σ
      (trace init ω four))
    (hfourv : four ≤ v) (hvu : v ≤ u)
    (hcredit :
      (1939 / 2000 : ℚ) * (M : ℚ) ≤
        AveragingCreditTransitions.totalCredit σ ell.val (ell.val + 1)
          (trace init ω four)) :
    939 * M ≤
      1000 * classCount (indexClass (adjacentIndices ell hell))
        (labelsAt init ω v) := by
  have hcount := LateSamplingFirstBranchShape.mainCount_at_snapshot
    hpath hseed hfourv hvu
  have hband := LateSamplingClassReceiptArithmetic.credit_two_class_at
    hpath hcredit hfourv hvu hcount
  have hbridge := adjacentBand_le_adjacentClass
    (m := init.card) σ ell hell (labelsAt init ω v)
  rw [show PairLog.labelCfg (labelsAt init ω v) = trace init ω v from
    PairLog.labelsAt_config init ω v] at hbridge
  omega

/-- The protected `.9232 M` class floor at every observed prefix, valid in the
strict-interior case. -/
theorem protected_global_floor_at
    {init : InputCfg n} {ω : InputLog n}
    {a four u v M : ℕ} {σ : Sign}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (hinterior : ell.val + 2 < PhaseThreeModel.Numeric.hourIndex n)
    (hpath : Prefix init ω a four u)
    (hseed : LateSamplingSeedReceipt init M ell.val σ
      (trace init ω four))
    (hfourv : four ≤ v) (hvu : v ≤ u) :
    9232 * M ≤
      10000 * classCount (indexClass (protectedIndices ell hell))
        (labelsAt init ω v) := by
  have hcount := LateSamplingFirstBranchShape.mainCount_at_snapshot
    hpath hseed hfourv hvu
  have hband := LateSamplingClassReceiptArithmetic.protected_three_class_at
    hpath hseed hfourv hvu hcount
  have hbridge := protectedBand_le_protectedClass
    (m := init.card) σ ell hell hinterior (labelsAt init ω v)
  rw [show PairLog.labelCfg (labelsAt init ω v) = trace init ω v from
    PairLog.labelsAt_config init ω v] at hbridge
  omega

/-- Direct specialization of the pathwise finite-test cover.  This is the
positive frozen-prefix part; it intentionally concludes membership in the old
frozen family.  Replacing its zero slot by the accepted trial requires the
threshold-aware counter repair in the next file. -/
theorem frozen_violation_mem_original
    {init : InputCfg n} {ω : InputLog n}
    {a four T A : ℕ}
    (h : Prefix init ω a four T)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (i : Fin 3)
    (hd : SeedDensity init.card
      (mainCount (labelsAt init ω four))
      (reserveCount (labelsAt init ω four)))
    (hA : A ≤ mainCount (labelsAt init ω four))
    (hfloor : ∀ v, four ≤ v → v ≤ T →
      A ≤ classCount
        (rowTwoClassChoice ell hell four (frestrictLe four ω) i)
        (labelsAt init ω v))
    (hk : Nat.ceil ((init.card : ℝ) / 1000000) ≤
      frozenCount (labelsAt init ω T))
    (hbad : ¬ FrozenFloor
      (rowTwoClassChoice ell hell four (frestrictLe four ω) i)
      A (mainCount (labelsAt init ω four)) (1 / 40000)
      (labelsAt init ω T)) :
    ω ∈ originalPrerequisiteFailure init (rowTwoClassChoice ell hell) := by
  exact LateFrozenPoolOriginalLaw.prefix_frozen_failure_mem
    h (rowTwoClassChoice ell hell) i hd hA hfloor hk hbad

/-!
THEOREM LIST
* `classIndices_exact`, `classIndices_adjacent`, `classIndices_protected`
* `law_rowTwoFailure_tail`, `law_rowTwoFailure_inverse_power`
* `bandCount_labelCfg_le_classCount`
* `exactBand_le_exactClass`, `adjacentBand_le_adjacentClass`
* `protectedBand_le_protectedClass`
* `exact_global_allowance_at_completion`
* `first_branch_global_floor_at`, `credit_branch_global_floor_at`
* `protected_global_floor_at`
* `frozen_violation_mem_original`

CLOSES
* Literal `ClassTestIndex` specialization for the three requested classes.
* Single-law finite-union charge at the genuine `firstFourStart`.
* Retrospective `.0021 M` exact-level allowance at every earlier prefix.
* Both fixed near-credit branches and the strict-interior protected class floor.
* Positive frozen-prefix violations are recognized by the finite family of the frozen-prefix cover.

UNFINISHED
* Equality boundary `ell.val + 2 = hourIndex n`: the accepted class excludes
  the sentinel and needs a separate deterministic no-sentinel-sample argument.
* The accepted zero-slot pathwise cover: current `acceptedCounter` has the
  false early-gate behavior exhibited above.
* Prefix-selected horizon transport for the zero slot.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateSamplingRowTwoChoices

end
