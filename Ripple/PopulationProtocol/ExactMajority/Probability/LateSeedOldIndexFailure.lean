-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSeedOldIndexFailure.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedTerminalOldObserved
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedReceiptProducerTail

/-!
# The terminal old-index failure charged by the N16 receipt producer

A selector fibre contains only information available at its fixed block start:
the genuine safe seed, the selected terminal level, the observed earlier
endpoint, and whatever earlier-success certificate the later cover uses.
The current terminal old-block failure is intersected afterwards.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateStrengthening

open TimeTheorem PairLog PhaseOneDrain StageEventSpec PhaseThreeClockProducer
open AveragingSparseEntry AveragingObservedHourTails
open AveragingCanonicalBlocks AveragingSeededDelay

variable {n : ℕ}

/-- Interface supplied by the later deterministic cover.

`firstCase ω = some i` means that the earlier tests have selected case `i`.
It must not inspect the current terminal failure or future successful history.
The `Option` value makes distinct selected fibres disjoint. -/
structure TerminalOldBlockSelector
    (init : InputCfg n) (ι : Type*) where
  firstCase : InputLog n → Option ι
  seedStart : ι → ℕ
  blockStart : ι → ℕ
  terminalLevel : ι → ℕ
  adapted : ∀ i,
    MeasurableSet[
      pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256
        (blockStart i)]
      {ω | firstCase ω = some i}
  seed_le_start : ∀ i, seedStart i ≤ blockStart i
  terminal_ready : ∀ i, terminalCutoff n < terminalLevel i
  safe_seed : ∀ i ω,
    firstCase ω = some i →
      SafeSparseSeed init ω (seedStart i)

/-- The adapted fibre selecting one candidate terminal family. -/
def terminalOldIndexCase
    {init : InputCfg n} {ι : Type*}
    (selector : TerminalOldBlockSelector init ι) (i : ι) :
    Set (InputLog n) :=
  {ω | selector.firstCase ω = some i}

/-- The canonical terminal old-block failure for one selected case. -/
def terminalOldFailureAt
    {init : InputCfg n} {ι : Type*}
    (selector : TerminalOldBlockSelector init ι) (i : ι) :
    Set (InputLog n) :=
  observedTerminalOldFailure init
    (selector.seedStart i) (selector.blockStart i)
    (selector.terminalLevel i - terminalCutoff n)
    (oldBlockStarts init (seedTime init 3)
      (selector.terminalLevel i - terminalCutoff n)
      (terminalCutoff n))
    (hourWarmStart init (seedTime init 3)
      (selector.terminalLevel i))

/-- The concrete `oldIndexFailure` passed to
`LateSeedReceiptProducerTail.late_sampling_seed_receipt_safe_estimate`. -/
def oldIndexFailure
    {init : InputCfg n} {ι : Type*}
    (selector : TerminalOldBlockSelector init ι) :
    Set (InputLog n) :=
  ⋃ i, terminalOldIndexCase selector i ∩
    terminalOldFailureAt selector i

theorem mem_oldIndexFailure_iff
    {init : InputCfg n} {ι : Type*}
    (selector : TerminalOldBlockSelector init ι) (ω : InputLog n) :
    ω ∈ oldIndexFailure selector ↔
      ∃ i,
        selector.firstCase ω = some i ∧
        ω ∈ terminalOldFailureAt selector i := by
  simp only [oldIndexFailure, Set.mem_iUnion, Set.mem_inter_iff,
    terminalOldIndexCase, Set.mem_setOf_eq]

/-- Distinct first-case prefix fibres are disjoint before any probability
estimate is applied. -/
theorem terminalOldIndexCase_pairwise
    {init : InputCfg n} {ι : Type*}
    (selector : TerminalOldBlockSelector init ι) :
    Pairwise (fun i j : ι =>
      Disjoint (terminalOldIndexCase selector i)
        (terminalOldIndexCase selector j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro ω hi hj
  apply hij
  change selector.firstCase ω = some i at hi
  change selector.firstCase ω = some j at hj
  exact Option.some.inj (hi.symm.trans hj)

/-- One adapted selector fibre pays the sharp terminal coefficient times its
own prefix mass. -/
theorem terminalOldIndexCase_tail
    {ι : Type*} (init : InputCfg n)
    (hn : timePopulationThreshold ≤ n)
    (selector : TerminalOldBlockSelector init ι) (i : ι) :
    law init
        (terminalOldIndexCase selector i ∩
          terminalOldFailureAt selector i) ≤
      ENNReal.ofReal
          (Real.rpow (n : ℝ) (-(207 / 100 : ℝ))) *
        law init (terminalOldIndexCase selector i) := by
  let r := selector.terminalLevel i - terminalCutoff n
  have hr : 1 ≤ r := by
    dsimp [r]
    have hready := selector.terminal_ready i
    omega
  have hmeas :
      MeasurableSet[
        pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256
          (selector.blockStart i)]
        (terminalOldIndexCase selector i) := by
    simpa only [terminalOldIndexCase] using selector.adapted i
  have hseed :
      ∀ ω ∈ terminalOldIndexCase selector i,
        SeedProfile n init
          (trace init ω (selector.seedStart i)) := by
    intro ω hω
    change selector.firstCase ω = some i at hω
    exact (selector.safe_seed i ω hω).2.1
  have htail :=
    observed_terminal_old_prefix_tail init hn
      (selector.seedStart i) (selector.blockStart i)
      (selector.seed_le_start i) r hr
      (oldBlockStarts init (seedTime init 3) r (terminalCutoff n))
      (fun j =>
        oldBlockStarts_pastTime init (seedTime init 3)
          (seedTime_pastTime init 3) r (terminalCutoff n) j)
      (hourWarmStart init (seedTime init 3)
        (selector.terminalLevel i))
      (hourWarmStart_pastTime init (seedTime init 3)
        (seedTime_pastTime init 3) (selector.terminalLevel i))
      (terminalOldIndexCase selector i) hmeas hseed
  simpa only [terminalOldFailureAt, r] using htail

/-- The requested `hold`: the complete first-case terminal old-block family is
charged once, under `law init`, at exactly the budget used by
`LateSeedReceiptProducerTail`. -/
theorem oldIndexFailure_hold
    {ι : Type*} [Countable ι]
    (init : InputCfg n) (hn : timePopulationThreshold ≤ n)
    (selector : TerminalOldBlockSelector init ι) :
    law init (oldIndexFailure selector) ≤
      ENNReal.ofReal
        (Real.rpow (n : ℝ) (-(207 / 100 : ℝ))) := by
  classical
  let ε :=
    ENNReal.ofReal (Real.rpow (n : ℝ) (-(207 / 100 : ℝ)))
  let P : ι → Set (InputLog n) :=
    terminalOldIndexCase selector
  let B : ι → Set (InputLog n) :=
    terminalOldFailureAt selector
  have hPadapted (i : ι) :
      MeasurableSet[
        pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256
          (selector.blockStart i)]
        (P i) := by
    simpa only [P, terminalOldIndexCase] using selector.adapted i
  have hP (i : ι) : MeasurableSet (P i) :=
    (pairLogFiltration _ _).le (selector.blockStart i) _
      (hPadapted i)
  have hdisj :
      Pairwise (fun i j : ι => Disjoint (P i) (P j)) := by
    simpa only [P] using terminalOldIndexCase_pairwise selector
  have hlocal (i : ι) :
      law init (P i ∩ B i) ≤ ε * law init (P i) := by
    simpa only [P, B, ε] using
      terminalOldIndexCase_tail init hn selector i
  change law init (⋃ i, P i ∩ B i) ≤ ε
  calc
    law init (⋃ i, P i ∩ B i) ≤
        ∑' i, law init (P i ∩ B i) :=
      measure_iUnion_le _
    _ ≤ ∑' i, ε * law init (P i) :=
      ENNReal.tsum_le_tsum hlocal
    _ = ε * law init (⋃ i, P i) := by
      rw [ENNReal.tsum_mul_left, ← measure_iUnion hdisj hP]
    _ ≤ ε * law init Set.univ :=
      mul_le_mul_left' (measure_mono (Set.subset_univ _)) ε
    _ = ε := by
      rw [measure_univ, mul_one]

/-- The exact safe-receipt theorem with the old-index argument instantiated.
Only the deterministic cover and the two other test families remain as
external inputs. -/
theorem late_sampling_seed_receipt_safe_estimate_with_terminal_old_index
    {ι : Type*} [Countable ι]
    (init : InputCfg n) (hn : timePopulationThreshold ≤ n)
    (selector : TerminalOldBlockSelector init ι)
    (protectedTestFailure nearTestFailure : Set (InputLog n))
    (hcover :
      lateSamplingSeedProducerSafeFailure init ⊆
        protectedTestFailure ∪
          (nearTestFailure ∪ oldIndexFailure selector))
    (hprotected :
      law init protectedTestFailure ≤
        ENNReal.ofReal (1 / (n : ℝ) ^ 4))
    (hnear :
      law init nearTestFailure ≤
        ENNReal.ofReal (1 / (n : ℝ) ^ 4)) :
    law init (lateSamplingSeedProducerSafeFailure init) ≤
      ENNReal.ofReal
        (2 / (n : ℝ) ^ 4 +
          Real.rpow (n : ℝ) (-(207 / 100 : ℝ))) := by
  exact
    late_sampling_seed_receipt_safe_estimate init
      protectedTestFailure nearTestFailure
      (oldIndexFailure selector) hcover hprotected hnear
      (oldIndexFailure_hold init hn selector)

end Ripple.PopulationProtocol.ExactMajority.LateStrengthening

end
