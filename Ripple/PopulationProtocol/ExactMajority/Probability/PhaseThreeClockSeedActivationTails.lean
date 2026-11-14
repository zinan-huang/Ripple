-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockSeedActivationTails.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockActivationTails
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockActivationSeed
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockFirstPositiveSplice

/-!
# Activation and first-positive creation on genuine first-seed fibres

The seed premise is the original observed seedPrefix. The activation
probability is unconditional on future safety. Exact Phase 3 and first-front
creation are packaged with a phase-cap observation at the activation
deadline; the cap is part of the failure event, never a future conditioning
hypothesis on the original prefix.

This file does not prove the early-mark estimates or produce the cap event.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockSeedActivationTails

open TimeTheorem PairLog PhaseThreeClockProducer PhaseThreeClockSeedTails
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw
  PhaseThreeClockActivationLaw PhaseThreeClockActivationTails
  PhaseThreeClockActivationSeed PhaseThreeClockFirstPositive
  PhaseThreeClockFirstPositiveSplice

variable {n : ℕ}

/-- Threshold activation at the calibrated deadline, with the observed
first-seed prefix and all actual transition premises discharged. -/
theorem seed_activation_prefix_tail (init : InputCfg n) (hc : 2 ≤ init.card)
    (s : ℕ) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ activationFailure init s
      (PhaseThreeClockActivationTails.activationHorizon init.card)) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 5) * law init E := by
  apply activation_prefix_calibrated init hc s E hE
  intro ω hω
  exact positive_activation_at_seedPrefix init ω s (hseed hω)

theorem seed_activation_fibre_tail (init : InputCfg n) (hc : 2 ≤ init.card)
    (s : ℕ) :
    law init (seedPrefix init s ∩ activationFailure init s
      (PhaseThreeClockActivationTails.activationHorizon init.card)) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 5) *
        law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply (seed_activation_prefix_tail init hc s (seedPrefix init s)
    (seedPrefix_measurable init s) (fun _ hω => hω)).trans
  exact mul_le_mul_left' (measure_mono
    (show seedPrefix init s ⊆ {ω | seedTime init 3 ω = (s : WithTop ℕ)} from
      fun _ hω => hω.1)) _

/-- At the activation deadline U, all current phases are at most three,
but either threshold activation has not finished or the level-one front
is still zero after its additional logarithmic creation interval. -/
def activationCreationFailure (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  let U := s + PhaseThreeClockActivationTails.activationHorizon init.card
  {ω | (∀ i, (virtualLabels init ω U i).phase.val ≤ 3) ∧
    (PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω U) < init.card ∨
      frontCount (virtualLabels init ω (U + firstPositiveHorizon init.card)) 1 = 0)}

theorem activationCreationFailure_measurable (init : InputCfg n) (s : ℕ) :
    MeasurableSet[pairLogFiltration _ _
      (s + PhaseThreeClockActivationTails.activationHorizon init.card +
        firstPositiveHorizon init.card)] (activationCreationFailure init s) := by
  let U := s + PhaseThreeClockActivationTails.activationHorizon init.card
  have hcap : MeasurableSet[pairLogFiltration _ _ U]
      {ω | ∀ i, (virtualLabels init ω U i).phase.val ≤ 3} :=
    (show MeasurableSet {f : Fin init.card →
        AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 |
          ∀ i, (f i).phase.val ≤ 3} from
      (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init U)
  have hact : MeasurableSet[pairLogFiltration _ _ U]
      {ω | PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω U) < init.card} :=
    activationFailure_measurable init s
      (PhaseThreeClockActivationTails.activationHorizon init.card)
  have hle : U ≤ U + firstPositiveHorizon init.card := by omega
  exact (((pairLogFiltration _ _).mono hle) _ hcap).inter
    ((((pairLogFiltration _ _).mono hle) _ hact).union
      (zero_front_measurable init (U + firstPositiveHorizon init.card)))

theorem seed_activation_creation_prefix_measurable (init : InputCfg n)
    (s : ℕ) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ s] E) :
    MeasurableSet[pairLogFiltration _ _
      (s + PhaseThreeClockActivationTails.activationHorizon init.card +
        firstPositiveHorizon init.card)]
      (E ∩ activationCreationFailure init s) :=
  (((pairLogFiltration _ _).mono (by omega :
    s ≤ s + PhaseThreeClockActivationTails.activationHorizon init.card +
      firstPositiveHorizon init.card)) _ hE).inter
    (activationCreationFailure_measurable init s)

/-- The actual seed produces activation and then the first positive front,
up to the explicitly displayed phase-cap alternative. All prefix factors
are on the original law; no future success is conditioned upon. -/
theorem seed_activation_creation_prefix_tail (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 9 ≤ n) (s : ℕ)
    (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ activationCreationFailure init s) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 5 + 1 / (init.card : ℝ) ^ 10) *
        law init E := by
  let U := s + PhaseThreeClockActivationTails.activationHorizon init.card
  let G : Set (InputLog n) := E ∩ {ω | DenseHomogeneousStart init ω U}
  let B : Set (InputLog n) :=
    {ω | (firstPositiveHorizon init.card : WithTop ℕ) < firstPositiveTime init U ω}
  have hsU : s ≤ U := by dsimp only [U]; omega
  have hG : MeasurableSet[pairLogFiltration _ _ U] G :=
    (((pairLogFiltration _ _).mono hsU) _ hE).inter
      (denseHomogeneousStart_measurable init U)
  have hcreation :
      law init (G ∩ B) ≤
        ENNReal.ofReal (1 / (init.card : ℝ) ^ 10) * law init G :=
    first_positive_dense_prefix_tail init hc U G hG (fun _ hω => hω.2)
  have hcover : E ∩ activationCreationFailure init s ⊆
      (E ∩ activationFailure init s
        (PhaseThreeClockActivationTails.activationHorizon init.card)) ∪ (G ∩ B) := by
    rintro ω ⟨he, hcap, hfail⟩
    rcases hfail with hact | hzero
    · exact Or.inl ⟨he, hact⟩
    · by_cases hact : PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω U) < init.card
      · exact Or.inl ⟨he, hact⟩
      · have hfull : PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω U) = init.card :=
          le_antisymm (activeCount_le_card _) (Nat.le_of_not_gt hact)
        have hdense : DenseHomogeneousStart init ω U :=
          dense_start_data_of_seedPrefix_full_activation init hn ω s U
            (hseed he) hsU hfull hcap
        exact Or.inr ⟨⟨he, hdense⟩,
          (firstPositiveTime_gt_iff_front_zero init U
            (firstPositiveHorizon init.card) ω hdense.1).2 hzero⟩
  calc
    law init (E ∩ activationCreationFailure init s) ≤
        law init ((E ∩ activationFailure init s
          (PhaseThreeClockActivationTails.activationHorizon init.card)) ∪ (G ∩ B)) :=
      measure_mono hcover
    _ ≤ law init (E ∩ activationFailure init s
          (PhaseThreeClockActivationTails.activationHorizon init.card)) +
        law init (G ∩ B) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (1 / (init.card : ℝ) ^ 5) * law init E +
        ENNReal.ofReal (1 / (init.card : ℝ) ^ 10) * law init G :=
      add_le_add (seed_activation_prefix_tail init hc s E hE hseed) hcreation
    _ ≤ ENNReal.ofReal (1 / (init.card : ℝ) ^ 5) * law init E +
        ENNReal.ofReal (1 / (init.card : ℝ) ^ 10) * law init E :=
      add_le_add le_rfl (mul_le_mul_left'
        (measure_mono (show G ⊆ E from fun _ hω => hω.1)) _)
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), add_mul]

theorem seed_activation_creation_fibre_tail (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 9 ≤ n) (s : ℕ) :
    law init (seedPrefix init s ∩ activationCreationFailure init s) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 5 + 1 / (init.card : ℝ) ^ 10) *
        law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply (seed_activation_creation_prefix_tail init hc hn s (seedPrefix init s)
    (seedPrefix_measurable init s) (fun _ hω => hω)).trans
  exact mul_le_mul_left' (measure_mono
    (show seedPrefix init s ⊆ {ω | seedTime init 3 ω = (s : WithTop ℕ)} from
      fun _ hω => hω.1)) _


/-- The entry history already present inside clockBadAfter discharges the
endpoint cap pathwise. It is used only for event inclusion, not as an
observed prefix or a conditioned law. -/
theorem asyncEntry_creation_failure_subset (init : InputCfg n) (s : ℕ) :
    {ω | (∃ T, StageEventSpec.AsyncEntry init ω s T) ∧
      (PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω
          (s + PhaseThreeClockActivationTails.activationHorizon init.card)) < init.card ∨
        frontCount (virtualLabels init ω
          (s + PhaseThreeClockActivationTails.activationHorizon init.card +
            firstPositiveHorizon init.card)) 1 = 0)} ⊆
      activationCreationFailure init s := by
  rintro ω ⟨⟨T, hentry⟩, hfail⟩
  refine ⟨?_, hfail⟩
  intro i
  exact ((PhaseThreeClockEmbeddingBridge.virtualLabels_clockEnvironment_of_asyncEntry
    init ω s T hentry
      (s + PhaseThreeClockActivationTails.activationHorizon init.card)
      (by omega)).phase_range i).2


/-- Failure of the genuine first positive front measured from the seed,
with the phase cap observed at the intermediate activation deadline. -/
def seedFirstPositiveFailure (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  {ω | (∀ i, (virtualLabels init ω
      (s + PhaseThreeClockActivationTails.activationHorizon init.card) i).phase.val ≤ 3) ∧
    ((PhaseThreeClockActivationTails.activationHorizon init.card +
      firstPositiveHorizon init.card : ℕ) : WithTop ℕ) < firstPositiveTime init s ω}

theorem seedFirstPositiveFailure_measurable (init : InputCfg n) (s : ℕ) :
    MeasurableSet[pairLogFiltration _ _
      (s + (PhaseThreeClockActivationTails.activationHorizon init.card +
        firstPositiveHorizon init.card))] (seedFirstPositiveFailure init s) := by
  let U := s + PhaseThreeClockActivationTails.activationHorizon init.card
  have hcap : MeasurableSet[pairLogFiltration _ _ U]
      {ω | ∀ i, (virtualLabels init ω U i).phase.val ≤ 3} :=
    (show MeasurableSet {f : Fin init.card →
        AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 |
          ∀ i, (f i).phase.val ≤ 3} from
      (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init U)
  have hle : U ≤ s + (PhaseThreeClockActivationTails.activationHorizon init.card +
      firstPositiveHorizon init.card) := by dsimp only [U]; omega
  exact (((pairLogFiltration _ _).mono hle) _ hcap).inter
    ((firstPositiveTime_isStoppingTime init s).measurableSet_gt
      (PhaseThreeClockActivationTails.activationHorizon init.card +
        firstPositiveHorizon init.card))

theorem seed_first_positive_failure_subset (init : InputCfg n) (s : ℕ) :
    seedFirstPositiveFailure init s ⊆ activationCreationFailure init s := by
  rintro ω ⟨hcap, htime⟩
  refine ⟨hcap, Or.inr ?_⟩
  simpa only [Nat.add_assoc] using front_zero_of_lt_firstPositiveTime init s
    (PhaseThreeClockActivationTails.activationHorizon init.card +
      firstPositiveHorizon init.card) ω htime

/-- The first-positive passage can be measured from the original seed,
even when a positive front is created before full activation. -/
theorem seed_first_positive_from_seed_prefix_tail (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 9 ≤ n) (s : ℕ)
    (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ seedFirstPositiveFailure init s) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 5 + 1 / (init.card : ℝ) ^ 10) *
        law init E :=
  (measure_mono (Set.inter_subset_inter (subset_refl E)
    (seed_first_positive_failure_subset init s))).trans
      (seed_activation_creation_prefix_tail init hc hn s E hE hseed)

theorem asyncEntry_first_positive_from_seed_subset (init : InputCfg n) (s : ℕ) :
    {ω | (∃ T, StageEventSpec.AsyncEntry init ω s T) ∧
      ((PhaseThreeClockActivationTails.activationHorizon init.card +
        firstPositiveHorizon init.card : ℕ) : WithTop ℕ) < firstPositiveTime init s ω} ⊆
      seedFirstPositiveFailure init s := by
  rintro ω ⟨⟨T, hentry⟩, htime⟩
  refine ⟨?_, htime⟩
  intro i
  exact ((PhaseThreeClockEmbeddingBridge.virtualLabels_clockEnvironment_of_asyncEntry
    init ω s T hentry
      (s + PhaseThreeClockActivationTails.activationHorizon init.card)
      (by omega)).phase_range i).2

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockSeedActivationTails

end
