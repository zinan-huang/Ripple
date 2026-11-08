import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6ReadyEscape

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace Phase78ReadyEscape

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-!
The slot-6 file supplies the shared arithmetic helpers

* `Phase6ReadyEscape.survivalFactor_nonneg`;
* `Phase6ReadyEscape.survivalFactor_ofReal_mul_prob_toReal`;

for the MGF/survival-factor side of the ready-escape reductions.  The two
atom conversions below are the structural scheduler reduction for slots 7 and 8:
a kernel bad-ready event is the image of the corresponding bad ready-pair set
under `Protocol.scheduledStep`.
-/

/-! ## A. Local measurable-space instances for scheduled state-pairs -/

local instance instMeasurableSpaceAgentStatePair :
    MeasurableSpace (AgentState L K × AgentState L K) := ⊤

local instance instDiscreteMeasurableSpaceAgentStatePair :
    DiscreteMeasurableSpace (AgentState L K × AgentState L K) :=
  ⟨fun _ => trivial⟩

/-! ## B. Slot 7 bad-pair residual -/

/--
Slot-7 bad ready-pairs for a source configuration `x`.

A pair is bad if scheduling it from `x` produces a configuration outside the
slot-7 ready gate.
-/
def phase7BadReadyPairs
    (n : ℕ) (σ : Sign) (E7 : ℕ)
    (x : Config (AgentState L K)) :
    Set (AgentState L K × AgentState L K) :=
  {p |
    ¬ Phase678ReadySurvival.Phase7DrainReady
      (L := L) (K := K) n σ E7
      (Protocol.scheduledStep (NonuniformMajority L K) x p)}

/--
The minimal slot-7 ready-escape residual.

For every ready source configuration with at least two agents, the scheduler
mass of bad ready-pairs is at most `η`.
-/
structure Phase7BadPairMassBound
    (n : ℕ) (σ : Sign) (E7 : ℕ) (η : ℝ≥0∞) : Prop where
  badPairMass_le :
    ∀ x,
      Phase678ReadySurvival.Phase7DrainReady
        (L := L) (K := K) n σ E7 x →
      ∀ hxcard : 2 ≤ x.card,
        (x.interactionPMF hxcard).toMeasure
          (phase7BadReadyPairs (L := L) (K := K) n σ E7 x)
          ≤ η

/--
Convert the slot-7 bad-pair residual into the public
`Phase7ReadyEscapeBound`.
-/
theorem phase7ReadyEscapeBound_of_badPairMass
    {n : ℕ} {σ : Sign} {E7 : ℕ} {η : ℝ≥0∞}
    (R : Phase7BadPairMassBound
      (L := L) (K := K) n σ E7 η) :
    Phase678ReadySurvival.Phase7ReadyEscapeBound
      (L := L) (K := K) n σ E7 η where
  hesc := by
    intro x hxReady
    change ((NonuniformMajority L K).stepDistOrSelf x).toMeasure
      {y : Config (AgentState L K) |
        ¬ Phase678ReadySurvival.Phase7DrainReady
          (L := L) (K := K) n σ E7 y} ≤ η
    by_cases hxcard : 2 ≤ x.card
    · have hstep :
          (NonuniformMajority L K).stepDistOrSelf x
            = (NonuniformMajority L K).stepDist x hxcard := by
        unfold Protocol.stepDistOrSelf
        rw [dif_pos hxcard]
      have hbad_meas :
          MeasurableSet
            {y : Config (AgentState L K) |
              ¬ Phase678ReadySurvival.Phase7DrainReady
                (L := L) (K := K) n σ E7 y} :=
        DiscreteMeasurableSpace.forall_measurableSet _
      rw [hstep]
      unfold Protocol.stepDist
      rw [PMF.toMeasure_map_apply _ _ _ (Measurable.of_discrete) hbad_meas]
      change
        (x.interactionPMF hxcard).toMeasure
          (phase7BadReadyPairs (L := L) (K := K) n σ E7 x)
          ≤ η
      exact R.badPairMass_le x hxReady hxcard
    · have hpure :
          (NonuniformMajority L K).stepDistOrSelf x = PMF.pure x := by
        unfold Protocol.stepDistOrSelf
        rw [dif_neg hxcard]
      have hbad_meas :
          MeasurableSet
            {y : Config (AgentState L K) |
              ¬ Phase678ReadySurvival.Phase7DrainReady
                (L := L) (K := K) n σ E7 y} :=
        DiscreteMeasurableSpace.forall_measurableSet _
      rw [hpure]
      have hzero :
          (PMF.pure x).toMeasure
            {y : Config (AgentState L K) |
              ¬ Phase678ReadySurvival.Phase7DrainReady
                (L := L) (K := K) n σ E7 y}
            = 0 := by
        rw [PMF.toMeasure_apply_eq_zero_iff _ hbad_meas]
        rw [Set.disjoint_left]
        intro y hy hbad
        rw [PMF.mem_support_pure_iff] at hy
        subst y
        exact hbad hxReady
      rw [hzero]
      exact zero_le'

/--
Slot-7 survival on the strengthened ready gate, packaged from the residual.
-/
noncomputable def phase7ReadySurvival_of_badPairMass
    {n : ℕ} (σ : Sign) (E7 M₀ : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (η : ℝ≥0∞)
    (R : Phase7BadPairMassBound
      (L := L) (K := K) n σ E7 η)
    (tWin7 : ℕ → ℕ)
    (hpt7 : ∀ m ∈ Finset.Icc 1 M₀,
      (DrainEngine.qHat E7 n m) ^ (tWin7 m) ≤
        (DrainCalibration.budgetNN M₀ n : ℝ≥0∞))
    (escapeε : ℝ≥0)
    (hescε : (((∑ m ∈ Finset.Icc 1 M₀, tWin7 m) : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase678ReadySurvival.phase7ReadySurvival
    (L := L) (K := K)
    σ E7 M₀ hn hM1
    η
    (phase7ReadyEscapeBound_of_badPairMass (L := L) (K := K) R)
    tWin7 hpt7 escapeε hescε

/-! ## C. Slot 8 bad-pair residual -/

/--
Slot-8 bad ready-pairs for a source configuration `x`.

A pair is bad if scheduling it from `x` produces a configuration outside the
slot-8 ready gate.
-/
def phase8BadReadyPairs
    (n : ℕ) (σ : Sign) (E8 : ℕ)
    (x : Config (AgentState L K)) :
    Set (AgentState L K × AgentState L K) :=
  {p |
    ¬ Phase678ReadySurvival.Phase8DrainReady
      (L := L) (K := K) n σ E8
      (Protocol.scheduledStep (NonuniformMajority L K) x p)}

/--
The minimal slot-8 ready-escape residual.

For every ready source configuration with at least two agents, the scheduler
mass of bad ready-pairs is at most `η`.
-/
structure Phase8BadPairMassBound
    (n : ℕ) (σ : Sign) (E8 : ℕ) (η : ℝ≥0∞) : Prop where
  badPairMass_le :
    ∀ x,
      Phase678ReadySurvival.Phase8DrainReady
        (L := L) (K := K) n σ E8 x →
      ∀ hxcard : 2 ≤ x.card,
        (x.interactionPMF hxcard).toMeasure
          (phase8BadReadyPairs (L := L) (K := K) n σ E8 x)
          ≤ η

/--
Convert the slot-8 bad-pair residual into the public
`Phase8ReadyEscapeBound`.
-/
theorem phase8ReadyEscapeBound_of_badPairMass
    {n : ℕ} {σ : Sign} {E8 : ℕ} {η : ℝ≥0∞}
    (R : Phase8BadPairMassBound
      (L := L) (K := K) n σ E8 η) :
    Phase678ReadySurvival.Phase8ReadyEscapeBound
      (L := L) (K := K) n σ E8 η where
  hesc := by
    intro x hxReady
    change ((NonuniformMajority L K).stepDistOrSelf x).toMeasure
      {y : Config (AgentState L K) |
        ¬ Phase678ReadySurvival.Phase8DrainReady
          (L := L) (K := K) n σ E8 y} ≤ η
    by_cases hxcard : 2 ≤ x.card
    · have hstep :
          (NonuniformMajority L K).stepDistOrSelf x
            = (NonuniformMajority L K).stepDist x hxcard := by
        unfold Protocol.stepDistOrSelf
        rw [dif_pos hxcard]
      have hbad_meas :
          MeasurableSet
            {y : Config (AgentState L K) |
              ¬ Phase678ReadySurvival.Phase8DrainReady
                (L := L) (K := K) n σ E8 y} :=
        DiscreteMeasurableSpace.forall_measurableSet _
      rw [hstep]
      unfold Protocol.stepDist
      rw [PMF.toMeasure_map_apply _ _ _ (Measurable.of_discrete) hbad_meas]
      change
        (x.interactionPMF hxcard).toMeasure
          (phase8BadReadyPairs (L := L) (K := K) n σ E8 x)
          ≤ η
      exact R.badPairMass_le x hxReady hxcard
    · have hpure :
          (NonuniformMajority L K).stepDistOrSelf x = PMF.pure x := by
        unfold Protocol.stepDistOrSelf
        rw [dif_neg hxcard]
      have hbad_meas :
          MeasurableSet
            {y : Config (AgentState L K) |
              ¬ Phase678ReadySurvival.Phase8DrainReady
                (L := L) (K := K) n σ E8 y} :=
        DiscreteMeasurableSpace.forall_measurableSet _
      rw [hpure]
      have hzero :
          (PMF.pure x).toMeasure
            {y : Config (AgentState L K) |
              ¬ Phase678ReadySurvival.Phase8DrainReady
                (L := L) (K := K) n σ E8 y}
            = 0 := by
        rw [PMF.toMeasure_apply_eq_zero_iff _ hbad_meas]
        rw [Set.disjoint_left]
        intro y hy hbad
        rw [PMF.mem_support_pure_iff] at hy
        subst y
        exact hbad hxReady
      rw [hzero]
      exact zero_le'

/--
Slot-8 survival on the strengthened ready gate, packaged from the residual.
-/
noncomputable def phase8ReadySurvival_of_badPairMass
    {n : ℕ} (σ : Sign) (E8 M₀ : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (η : ℝ≥0∞)
    (R : Phase8BadPairMassBound
      (L := L) (K := K) n σ E8 η)
    (tWin8 : ℕ → ℕ)
    (hpt8 : ∀ m ∈ Finset.Icc 1 M₀,
      (DrainEngine.qHat E8 n m) ^ (tWin8 m) ≤
        (DrainCalibration.budgetNN M₀ n : ℝ≥0∞))
    (escapeε : ℝ≥0)
    (hescε : (((∑ m ∈ Finset.Icc 1 M₀, tWin8 m) : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase678ReadySurvival.phase8ReadySurvival
    (L := L) (K := K)
    σ E8 M₀ hn hM1
    η
    (phase8ReadyEscapeBound_of_badPairMass (L := L) (K := K) R)
    tWin8 hpt8 escapeε hescε

/-! ## D. Trivial residuals for smoke-testing the surfaces -/

/--
Always-valid slot-7 residual with `η = 1`.

This is not the desired paper-scale rectangle bound, but checks the structural
reduction from interaction bad-pairs to the public atom.
-/
theorem phase7BadPairMassBound_one
    (n : ℕ) (σ : Sign) (E7 : ℕ) :
    Phase7BadPairMassBound (L := L) (K := K) n σ E7 (1 : ℝ≥0∞) where
  badPairMass_le := by
    intro x _hxReady hxcard
    haveI : IsProbabilityMeasure ((x.interactionPMF hxcard).toMeasure) :=
      PMF.toMeasure.isProbabilityMeasure _
    exact le_trans (measure_mono (Set.subset_univ _)) prob_le_one

/--
Always-valid slot-8 residual with `η = 1`.

This is not the desired paper-scale rectangle bound, but checks the structural
reduction from interaction bad-pairs to the public atom.
-/
theorem phase8BadPairMassBound_one
    (n : ℕ) (σ : Sign) (E8 : ℕ) :
    Phase8BadPairMassBound (L := L) (K := K) n σ E8 (1 : ℝ≥0∞) where
  badPairMass_le := by
    intro x _hxReady hxcard
    haveI : IsProbabilityMeasure ((x.interactionPMF hxcard).toMeasure) :=
      PMF.toMeasure.isProbabilityMeasure _
    exact le_trans (measure_mono (Set.subset_univ _)) prob_le_one

#print axioms phase7ReadyEscapeBound_of_badPairMass
#print axioms phase7ReadySurvival_of_badPairMass
#print axioms phase8ReadyEscapeBound_of_badPairMass
#print axioms phase8ReadySurvival_of_badPairMass
#print axioms phase7BadPairMassBound_one
#print axioms phase8BadPairMassBound_one

end Phase78ReadyEscape

end Ripple.PopulationProtocol.ExactMajority
