-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockSeedTails.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockStoppedPassage
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockThinning

/-!
# Local clock tails on genuine first-seed and observed-passage prefixes

This file retains the actual first Phase-3 seed and its SeedProfile. A
passage estimate starts at a deterministic observation u at or after that
seed, and explicitly intersects with PassageWindow at u. Thus its starting
front is observed to be positive and sparse; the estimate is not presented
as a positive-front passage starting at the fresh zero-height seed.

The physical Clock mask for contact thinning is still observed at the seed.
All measures are the original pair-log law. These estimates neither produce
the first positive front nor supply ClockHistory, the full local error
budget, or the producer's hlocal.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockSeedTails

open TimeTheorem PairLog PhaseThreeClockProducer PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockStoppedPassage PhaseThreeClockThinning

variable {n : ℕ}

def seedPrefix (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
    StageEventSpec.SeedProfile n init (trace init ω s)}

def seedMaskPrefix (init : InputCfg n) (s : ℕ)
    (C : Finset (Fin init.card)) : Set (InputLog n) :=
  seedPrefix init s ∩ {ω | clockSet (labelsAt init ω s) = C}

theorem seedPrefix_measurable (init : InputCfg n) (s : ℕ) :
    MeasurableSet[pairLogFiltration _ _ s] (seedPrefix init s) := by
  have hprofile : MeasurableSet[pairLogFiltration _ _ s]
      {ω | StageEventSpec.SeedProfile n init (trace init ω s)} :=
    (show MeasurableSet {c : InputCfg n | StageEventSpec.SeedProfile n init c} from
      (Set.to_countable _).measurableSet).preimage (measurable_trace_at init s)
  exact (seedTime_pastTime init 3 s).inter hprofile

theorem seedMaskPrefix_measurable (init : InputCfg n) (s : ℕ)
    (C : Finset (Fin init.card)) :
    MeasurableSet[pairLogFiltration _ _ s] (seedMaskPrefix init s C) := by
  have hlab : Measurable[pairLogFiltration _ _ s] (fun ω => labelsAt init ω s) :=
    (measurable_prefixLabels init s).comp (measurable_pairLog_prefix _ _ s)
  have hmask : MeasurableSet[pairLogFiltration _ _ s]
      {ω | clockSet (labelsAt init ω s) = C} :=
    (show MeasurableSet {f : Fin init.card →
        AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 | clockSet f = C} from
      (Set.to_countable _).measurableSet).preimage hlab
  exact (seedPrefix_measurable init s).inter hmask

/-- The seed information together with a positive sparse front observed at u.
The seed time s and the passage start u are separate deterministic times. -/
def seedPassagePrefix (init : InputCfg n) (ℓ b s u : ℕ) : Set (InputLog n) :=
  seedPrefix init s ∩
    {ω | PassageWindow (virtualLabels init ω u) ℓ b}

theorem seedPassagePrefix_measurable (init : InputCfg n)
    (ℓ b s u : ℕ) (hsu : s ≤ u) :
    MeasurableSet[pairLogFiltration _ _ u] (seedPassagePrefix init ℓ b s u) := by
  have hseed : MeasurableSet[pairLogFiltration _ _ u] (seedPrefix init s) :=
    ((pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).mono hsu) _
      (seedPrefix_measurable init s)
  have hwindow : MeasurableSet[pairLogFiltration _ _ u]
      {ω | PassageWindow (virtualLabels init ω u) ℓ b} :=
    (show MeasurableSet {f : Fin init.card →
        AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 | PassageWindow f ℓ b} from
      (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init u)
  exact hseed.inter hwindow

/-- Killed sparse-window passage from an observed positive front at u,
while retaining the original probability of the seed/passage prefix. -/
theorem seed_passage_prefix_tail (init : InputCfg n) (hc : 2 ≤ init.card)
    (ℓ b s u N : ℕ) (hsu : s ≤ u) (hℓ : 1 ≤ ℓ)
    (hcap : ℓ ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    law init (seedPassagePrefix init ℓ b s u ∩
        {ω | (N : WithTop ℕ) < passageStop init ℓ b u ω}) ≤
      ENNReal.ofReal
        (Real.exp ((b : ℝ) * Real.log 2 - (N : ℝ) / (6 * (init.card : ℝ)))) *
          law init (seedPassagePrefix init ℓ b s u) :=
  gated_passage_prefix_tail init hc ℓ b u N hℓ hcap
    (seedPassagePrefix init ℓ b s u) (seedPassagePrefix_measurable init ℓ b s u hsu)

/-- The observed-start passage bound with precisely the first-seed fibre
mass appearing in hlocal. No eventual good event is conditioned upon. -/
theorem seed_passage_fibre_tail (init : InputCfg n) (hc : 2 ≤ init.card)
    (ℓ b s u N : ℕ) (hsu : s ≤ u) (hℓ : 1 ≤ ℓ)
    (hcap : ℓ ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    law init (seedPassagePrefix init ℓ b s u ∩
        {ω | (N : WithTop ℕ) < passageStop init ℓ b u ω}) ≤
      ENNReal.ofReal
        (Real.exp ((b : ℝ) * Real.log 2 - (N : ℝ) / (6 * (init.card : ℝ)))) *
          law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply (seed_passage_prefix_tail init hc ℓ b s u N hsu hℓ hcap).trans
  have hsub : seedPassagePrefix init ℓ b s u ⊆
      {ω | seedTime init 3 ω = (s : WithTop ℕ)} :=
    fun _ hω => hω.1.1
  exact mul_le_mul_left' (measure_mono hsub) _

/-- An observed positive sparse window has almost surely finite exit.
The exit may be a guard failure; target crossing is not asserted. -/
theorem seed_passage_infinite_null (init : InputCfg n) (hc : 2 ≤ init.card)
    (ℓ b s u : ℕ) (_hsu : s ≤ u) (hℓ : 1 ≤ ℓ)
    (hcap : ℓ ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    law init (seedPassagePrefix init ℓ b s u ∩
      {ω | passageStop init ℓ b u ω = ⊤}) = 0 :=
  passageStop_eq_top_prefix_null init hc ℓ b u hℓ hcap (seedPassagePrefix init ℓ b s u)

/-- The upper contact tail with the Clock labels frozen at the actual seed. -/
theorem seed_clockContacts_upper_tail (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (s N : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hmean : clockMaskRate init.card C.card * (N : ℝ) ≤ 3 * r / 4) :
    law init (seedMaskPrefix init s C ∩
        {ω | r ≤ (StageEventSpec.clockContacts init ω s s (s + N) : ℝ)}) ≤
      ENNReal.ofReal (Real.exp (-r / 36)) * law init (seedMaskPrefix init s C) :=
  prefix_stageEvent_clockContacts_upper_tail_ennreal init hc C s s N
    (seedMaskPrefix init s C) (seedMaskPrefix_measurable init s C)
    (fun _ hω => hω.2) r hr hmean

/-- The lower contact tail on the same genuine observed seed/mask event. -/
theorem seed_clockContacts_lower_tail (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (s N : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hmean : 2 * r ≤ clockMaskRate init.card C.card * (N : ℝ)) :
    law init (seedMaskPrefix init s C ∩
        {ω | (StageEventSpec.clockContacts init ω s s (s + N) : ℝ) < r}) ≤
      ENNReal.ofReal (Real.exp (-r / 4)) * law init (seedMaskPrefix init s C) :=
  prefix_stageEvent_clockContacts_lower_tail_ennreal init hc C s s N
    (seedMaskPrefix init s C) (seedMaskPrefix_measurable init s C)
    (fun _ hω => hω.2) r hr hmean

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockSeedTails

end
