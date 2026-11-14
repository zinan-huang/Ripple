-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingRowTwoCounterRepair.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingRowTwoChoices

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingRowTwoCounterRepair

open TimeTheorem PairLog PairLogAuxiliary
open LateF6Acceptance LateF6Hazards
open LateSamplingClassGates LateSamplingCounterTail
open LateAcceptedRectangleHazard LateAcceptedCounterCoupling
open LateAcceptedTrialSlot

variable {L K : ℕ}

/-- Correct gate: before the freeze threshold the frozen-ratio receipt is not
required; once the event rectangle can fire, the receipt is required. -/
def ThresholdAcceptedGate
    (k M A : ℕ) (J : Finset (Fin (L + 1))) (γ : ℝ)
    (f : Fin n → AgentState L K) : Prop :=
  mainCount f = M ∧
    A ≤ classCount (indexClass J) f ∧
    (frozenCount f < k ∨ FrozenFloor (indexClass J) A M γ f)

/-- The corrected stopped counter.  The threshold remains in the event and
bad rectangles, while the absorbing gate uses the logically equivalent
pre-threshold disjunction. -/
def thresholdAcceptedCounter
    (init : Cfg L K) (s k M A : ℕ)
    (J : Finset (Fin (L + 1))) (γ : ℝ) : CounterSpec init where
  start := s
  cap := init.card + 1
  debt := init.card
  gate := fun _t p _z =>
    ThresholdAcceptedGate k M A J γ (prefixLabels init _t p)
  event := lateAcceptedRectangle k
  bad := lateBadAcceptedRectangle k J
  bad_subset := by
    intro f i j h
    rcases h with ⟨hk, hbad⟩
    refine ⟨hk, ?_⟩
    unfold badAcceptedRectangle at hbad
    unfold acceptedRectangle
    unfold contact badEligible badFrozenEligible at hbad
    unfold contact
    tauto

/-- Before the threshold, only the persistent global class receipt is needed. -/
theorem thresholdGate_before
    {f : Fin n → AgentState L K}
    {k M A : ℕ} {J : Finset (Fin (L + 1))} {γ : ℝ}
    (hmains : mainCount f = M)
    (hglobal : A ≤ classCount (indexClass J) f)
    (hbefore : frozenCount f < k) :
    ThresholdAcceptedGate k M A J γ f :=
  ⟨hmains, hglobal, Or.inl hbefore⟩

/-- At and after the threshold, the frozen floor supplies the third gate
component. -/
theorem thresholdGate_after
    {f : Fin n → AgentState L K}
    {k M A : ℕ} {J : Finset (Fin (L + 1))} {γ : ℝ}
    (hmains : mainCount f = M)
    (hglobal : A ≤ classCount (indexClass J) f)
    (hfloor : FrozenFloor (indexClass J) A M γ f) :
    ThresholdAcceptedGate k M A J γ f :=
  ⟨hmains, hglobal, Or.inr hfloor⟩

/-- The corrected gate gives exactly the same rectangle hazard used by the
accepted-trial exponential bound.  In the pre-threshold branch both event
rectangles are empty; in the post-threshold branch the frozen floor is
available. -/
theorem thresholdAcceptedCounter_hazard
    (init : Cfg L K) (hn : 2 ≤ init.card)
    (s k M A : ℕ) (J : Finset (Fin (L + 1))) (γ : ℝ)
    (hM : 0 < M) (hA : A ≤ M)
    (hγ : 0 ≤ γ) (hγA : γ ≤ (A : ℝ) / M) :
    ∀ t p z,
      (thresholdAcceptedCounter init s k M A J γ).Enabled t p z →
      pairMass init (thresholdAcceptedCounter init s k M A J γ).bad
          (prefixLabels init t p) ≤
        acceptedBadRate M A γ *
          pairMass init (thresholdAcceptedCounter init s k M A J γ).event
            (prefixLabels init t p) := by
  intro t p z he
  let f := prefixLabels init t p
  have hgate : ThresholdAcceptedGate k M A J γ f := by
    simpa [f, thresholdAcceptedCounter] using he.2.2.1
  rcases hgate with ⟨hmains, hglobal, hthreshold⟩
  by_cases hk : k ≤ frozenCount f
  · have hfloor : FrozenFloor (indexClass J) A M γ f := by
      rcases hthreshold with hbefore | hfloor
      · omega
      · exact hfloor
    have eevent : pairMass init (lateAcceptedRectangle k) f =
        pairMass init acceptedRectangle f := by
      unfold pairMass
      congr 3
      ext ij
      simp [goodPairs, lateAcceptedRectangle, hk]
    have ebad : pairMass init (lateBadAcceptedRectangle k J) f =
        pairMass init (badAcceptedRectangle (indexClass J)) f := by
      unfold pairMass
      congr 3
      ext ij
      simp [goodPairs, lateBadAcceptedRectangle, hk]
    show pairMass init (lateBadAcceptedRectangle k J) f ≤
      acceptedBadRate M A γ * pairMass init (lateAcceptedRectangle k) f
    rw [eevent, ebad]
    exact stored_index_bad_pairMass_le init hn J f M A γ
      hM hA hγ hγA hmains hglobal hfloor
  · simp [f, thresholdAcceptedCounter, lateAcceptedRectangle,
      lateBadAcceptedRectangle, hk, pairMass, goodPairs]

/-!
THEOREM LIST
* `thresholdGate_before`, `thresholdGate_after`
* `thresholdAcceptedCounter_hazard`

CLOSES
* The finite counterexample is repaired at the exact logical point.
* The corrected counter satisfies the hazard premise consumed by
  `CounterSpec.constant_tail`.

UNFINISHED
* Reinstantiate `recorded_accepted_trial_tail`, the zero-slot event, and the
  actual-count coupling with `thresholdAcceptedCounter`.
* Add a terminal-stop or fixed-horizon transport theorem so a horizon chosen
  at `firstFourStart` retains the completed-snapshot counter state.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateSamplingRowTwoCounterRepair

end
