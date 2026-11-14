-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingFuelFeasibilityAudit.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingMassCountProducer
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRegime

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingFuelFeasibilityAudit

open TimeTheorem
open StageEventSpec

variable {L K n : ℕ}

/-- The weak finite-family density record does not contain the paper's
upper Main bound or lower Reserve bound. -/
theorem weakSeedDensity_counterexample :
    LateFrozenPoolOriginalLaw.SeedDensity 25 15 0 ∧
      (¬ 25 * 15 ≤ 13 * 25) ∧
      (¬ 6 * 25 ≤ 25 * 0) := by
  constructor
  · exact
      { mains_lower := by norm_num
        reserves_upper := by norm_num
        total_le := by norm_num }
  · constructor <;> norm_num

/-- The actual asynchronous seed does contain both paper role bounds. -/
theorem actual_async_seed_paper_density
    {init : InputCfg n} {omega : InputLog n} {S T : ℕ}
    (hentry : AsyncEntry init omega S T) :
    25 * timeMainCount (trace init omega S) ≤ 13 * n ∧
      6 * n ≤ 25 * reserveCount (trace init omega S) := by
  have h := PhaseThreeClockRegime.seed_density init omega hentry
  exact ⟨h.2.1, h.2.2.2.2⟩

/-- Existing finite obstruction: a positive lower sampled class does not
produce a positive `highIndex` sampled class. -/
theorem current_twoClassSampleFloors_counterexample :
    Phase5Convergence.ReserveSampleGood
        (L := 4) (K := 0)
        Phase5To6FuelProducer.OneClassSampleObstruction.lowerIndex
        1 Phase5To6FuelProducer.OneClassSampleObstruction.c ∧
      ¬ Phase5To6FuelProducer.TwoClassSampleFloors
        (L := 4) (K := 0)
        Phase5To6FuelProducer.OneClassSampleObstruction.lowerIndex
        Phase5To6FuelProducer.OneClassSampleObstruction.lowerIndex_two_le
        1 1 Phase5To6FuelProducer.OneClassSampleObstruction.c :=
  Phase5To6FuelProducer.OneClassSampleObstruction.one_class_post_not_two_class

/-- Which of the two dynamically persistent Phase-6 ledgers is selected. -/
inductive FuelBranch where
  | lower
  | adjacent
  deriving DecidableEq

/-- Correct branch-indexed deterministic cap.

The numerical producer proves the `lower` field from
`splitDebt ell ≤ massAboveScaled ell`.  It proves the `adjacent` field from

`unionSplitDebt ell ≤ 2 * massAboveScaled ell + mainAtLevelU ell`,

which has coefficient one on the exact-level count. -/
structure CorrectedLemma72MassCountBounds
    (branch : FuelBranch)
    (ell : Fin (L + 1)) (Kzero cap : ℕ)
    (c : Config (AgentState L K)) : Prop where
  debt_cap :
    match branch with
    | .lower =>
        Kzero + Phase6FuelLedger.splitDebt
          (L := L) (K := K) ell c ≤ cap
    | .adjacent =>
        Kzero + Phase6FuelLedger.unionSplitDebt
          (L := L) (K := K) ell c ≤ cap

/-- Correct matching sample floor.  The adjacent branch uses the union count,
not the class `ell + 1` alone. -/
structure CorrectedTwoClassSampleFloor
    (branch : FuelBranch)
    (ell : Fin (L + 1)) (cap : ℕ)
    (c : Config (AgentState L K)) : Prop where
  sample_cap :
    match branch with
    | .lower =>
        cap ≤ Phase6FuelLedger.reserveFuel
          (L := L) (K := K) ell c
    | .adjacent =>
        cap ≤ Phase6FuelLedger.twoReserveFuel
          (L := L) (K := K) ell c

/-- Package the selected branch and its branch-specific cap.  (A `Prop`
structure cannot carry the data fields `branch`, `cap`; they are bound
existentially.) -/
def CorrectedEntryFuelCertificate
    (ell : Fin (L + 1)) (Kzero : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  ∃ (branch : FuelBranch) (cap : ℕ),
    CorrectedLemma72MassCountBounds
      (L := L) (K := K) branch ell Kzero cap c ∧
    CorrectedTwoClassSampleFloor
      (L := L) (K := K) branch ell cap c

/-- The consumer becomes a direct two-case composition.  No high-only
weakening and no shared unused threshold remain. -/
theorem twoLevelFuelLedger_of_corrected_pair
    (ell : Fin (L + 1)) (Kzero : ℕ)
    (c : Config (AgentState L K))
    (h : CorrectedEntryFuelCertificate
      (L := L) (K := K) ell Kzero c) :
    Phase6FuelLedger.TwoLevelFuelLedger
      (L := L) (K := K) ell Kzero c := by
  unfold Phase6FuelLedger.TwoLevelFuelLedger
  obtain ⟨branch, cap, hmass, hfloor⟩ := h
  cases branch with
  | lower =>
      exact Or.inl (hmass.debt_cap.trans hfloor.sample_cap)
  | adjacent =>
      exact Or.inr (hmass.debt_cap.trans hfloor.sample_cap)

/-!
THEOREM LIST
* `weakSeedDensity_counterexample`
* `actual_async_seed_paper_density`
* `current_twoClassSampleFloors_counterexample`
* `FuelBranch`
* `CorrectedLemma72MassCountBounds`
* `CorrectedTwoClassSampleFloor`
* `CorrectedEntryFuelCertificate`
* `twoLevelFuelLedger_of_corrected_pair`

CLOSES
* Finite refutation of the current high-only `TwoClassSampleFloors` field.
* Separation of weak `SeedDensity` from the actual `RoleSplitGood` seed bounds.
* Correct branch-indexed interface using exact lower debt or exact adjacent
  union debt.
* Correct deterministic conversion to `TwoLevelFuelLedger`.

UNFINISHED
* Formalize the sharp arithmetic lemma
  `unionSplitDebt ell ≤ 2 * massAboveScaled ell + mainAtLevelU ell`.
* Transport the `PhaseThreeClockRegime.seed_density` Main/Reserve bounds from
  the asynchronous seed to the completed snapshot as one compact receipt.
* Build the branch selector from the first alternative and the second
  alternative's crossover `696 / 2375`, including integer rounding.
* Replace the current `CompletionProducer` fields by the branch-indexed
  certificate, or more simply make it produce `TwoLevelFuelLedger` directly.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateSamplingFuelFeasibilityAudit

end
