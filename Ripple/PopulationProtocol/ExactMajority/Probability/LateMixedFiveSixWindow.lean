-- Ripple/PopulationProtocol/ExactMajority/Probability/LateMixedFiveSixWindow.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateMixedFuel

/-!
# Deterministic mixed Phase-5/6 window

This file isolates the pathwise half of the timer/epidemic race used by N18
row 4.  No probability estimate is made here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateMixedFiveSixWindow

open TimeTheorem PairLog
open LateSamplingCompletion LateMixedFuel

variable {n : ℕ}

/-- The first actual configuration containing an agent in Phase 7 or above.
Starting from the completed Phase-5 configuration, this is the first possible
Phase-6 timer exit; using `someGE 7` also catches any later-phase overshoot. -/
def firstPhaseSevenStart (init : InputCfg n) :
    InputLog n → WithTop ℕ :=
  TraceDrain.exitTime init (StageEventSpec.someGE (n := n) 7)

theorem firstPhaseSevenStart_isStoppingTime (init : InputCfg n) :
    IsStoppingTime
      (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256)
      (firstPhaseSevenStart init) :=
  TraceDrain.exitTime_isStoppingTime init
    (StageEventSpec.someGE (n := n) 7)

theorem firstPhaseSevenStart_past (init : InputCfg n) :
    PhaseOneDrain.PairLogPastTime (firstPhaseSevenStart init) :=
  PhaseOneDrainStopping.exitTime_pairLogPastTime init
    (StageEventSpec.someGE (n := n) 7)

theorem firstPhaseSevenStart_eq_iff
    (init : InputCfg n) (ω : InputLog n) (t : ℕ) :
    firstPhaseSevenStart init ω = (t : WithTop ℕ) ↔
      StageEventSpec.firstHit
        (StageEventSpec.someGE (n := n) 7) (trace init ω) t := by
  simpa only [firstPhaseSevenStart] using
    (PhaseOneDrainStopping.exitTime_eq_iff_firstHit init
      (StageEventSpec.someGE (n := n) 7) ω t)

/-- Explicit pair-log event saying that the homogeneous Phase-6 epidemic hit
occurs after the completed snapshot and strictly before any Phase-7 entry. -/
def noTimerExitBeforeHomogeneousSix
    (init : InputCfg n) (u : ℕ) : Set (InputLog n) :=
  {ω |
    (u : WithTop ℕ) ≤ homogeneousSixStart init ω ∧
      homogeneousSixStart init ω < firstPhaseSevenStart init ω}

@[simp] theorem mem_noTimerExitBeforeHomogeneousSix_iff
    (init : InputCfg n) (ω : InputLog n) (u : ℕ) :
    ω ∈ noTimerExitBeforeHomogeneousSix init u ↔
      (u : WithTop ℕ) ≤ homogeneousSixStart init ω ∧
        homogeneousSixStart init ω < firstPhaseSevenStart init ω :=
  Iff.rfl

/-- The two deterministic hypotheses requested by the row-four reduction. -/
def MixedWindowCondition
    (init : InputCfg n) (ω : InputLog n) (u : ℕ) : Prop :=
  LateMixedFuelLedger.MixedFiveSixWin n (trace init ω u) ∧
    ω ∈ noTimerExitBeforeHomogeneousSix init u

/-- Failure of the mixed-window condition on the genuine completion fibre.
There is no failure contribution here when the completion stopping time is
infinite; that case belongs to `completionFailure`. -/
def mixedFailure (init : InputCfg n) : Set (InputLog n) :=
  {ω | ∃ u : ℕ,
    completionTime init n ω = (u : WithTop ℕ) ∧
      ¬ MixedWindowCondition init ω u}

@[simp] theorem mem_mixedFailure_iff
    (init : InputCfg n) (ω : InputLog n) :
    ω ∈ mixedFailure init ↔
      ∃ u : ℕ, completionTime init n ω = (u : WithTop ℕ) ∧
        ¬ MixedWindowCondition init ω u :=
  Iff.rfl

/-- A completion receipt supplies the stronger initial condition “every agent
is exactly in Phase 5,” together with the required population size. -/
theorem completionReceipt_mixedFiveSixAt
    {init : InputCfg n} {ω : InputLog n}
    {a four five u : ℕ} {Snapshot : InputCfg n → Prop}
    (h : CompletionReceipt init ω a four five u Snapshot) :
    LateMixedFuelLedger.MixedFiveSixWin n (trace init ω u) := by
  refine ⟨h.complete.population, ?_⟩
  intro b hb
  exact Or.inl (h.complete.phase_five b hb)

/-- Before the first `someGE 7` hit every present agent has phase below 7. -/
theorem phase_lt_seven_before_firstPhaseSevenStart
    (init : InputCfg n) (ω : InputLog n) (k : ℕ)
    (hk : (k : WithTop ℕ) < firstPhaseSevenStart init ω) :
    ∀ b ∈ trace init ω k, b.phase.val < 7 := by
  have hnone :=
    TraceDrain.not_of_lt_exitTime init
      (StageEventSpec.someGE (n := n) 7) ω k
      (by simpa only [firstPhaseSevenStart] using hk)
  intro b hb
  by_contra hlt
  exact hnone k le_rfl ⟨b, hb, by omega⟩

/-- Core pathwise reduction.  Phase monotonicity propagates the lower bound 5;
the strict timer/epidemic race supplies the upper bound `< 7`; hence every
source configuration before the homogeneous-six hit is exactly mixed 5/6. -/
theorem mixedFiveSixPrefix_of_condition
    {init : InputCfg n} {ω : InputLog n} {u : ℕ}
    (h : MixedWindowCondition init ω u) :
    ∃ v, MixedFiveSixPrefix init ω u v := by
  change
    LateMixedFuelLedger.MixedFiveSixWin n (trace init ω u) ∧
      ω ∈ noTimerExitBeforeHomogeneousSix init u at h
  rcases h with ⟨hstart, hrace⟩
  rcases hstart with ⟨hcardStart, hphaseStart⟩
  rw [mem_noTimerExitBeforeHomogeneousSix_iff] at hrace
  rcases hrace with ⟨huSix, hsixSeven⟩
  have hsixFinite : homogeneousSixStart init ω ≠ ⊤ :=
    ne_top_of_lt hsixSeven
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hsixFinite
  have hsix : homogeneousSixStart init ω = (v : WithTop ℕ) :=
    hv.symm
  have huvTop : (u : WithTop ℕ) ≤ (v : WithTop ℕ) := by
    rw [← hsix]
    exact huSix
  have huv : u ≤ v := WithTop.coe_le_coe.mp huvTop
  have hvSeven : (v : WithTop ℕ) < firstPhaseSevenStart init ω := by
    rw [← hsix]
    exact hsixSeven
  have hlowerStart :
      ∀ b ∈ trace init ω u, 5 ≤ b.phase.val := by
    intro b hb
    rcases hphaseStart b hb with hfive | hsix' <;> omega
  refine ⟨v, ?_⟩
  refine
    { six_start := hsix
      completion_le := huv
      source_window := ?_ }
  intro k huk hkv
  have hreach := TimeTheorem.trace_reachable init ω huk
  have hcard : (trace init ω k).card = n :=
    (Protocol.reachable_card_eq hreach).trans hcardStart
  have hlower :=
    PhaseOneDrainStopping.phase_lower_reachable
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      5 (trace init ω u) (trace init ω k) hreach hlowerStart
  have hkSeven : (k : WithTop ℕ) < firstPhaseSevenStart init ω :=
    (WithTop.coe_lt_coe.mpr hkv).trans hvSeven
  have hupper :=
    phase_lt_seven_before_firstPhaseSevenStart init ω k hkSeven
  refine ⟨hcard, ?_⟩
  intro b hb
  have hlo := hlower b hb
  have hhi := hupper b hb
  omega

/-- Receipt-facing formulation of the requested two-input reduction. -/
theorem mixedFiveSixPrefix_of_completion_and_timerRace
    {init : InputCfg n} {ω : InputLog n}
    {a four five u : ℕ} {Snapshot : InputCfg n → Prop}
    (hcompletion : CompletionReceipt init ω a four five u Snapshot)
    (hrace : ω ∈ noTimerExitBeforeHomogeneousSix init u) :
    ∃ v, MixedFiveSixPrefix init ω u v := by
  apply mixedFiveSixPrefix_of_condition
  exact ⟨completionReceipt_mixedFiveSixAt hcompletion, hrace⟩

/-- Exact `hmixed` producer consumed by
`LateMixedFuel.law_compatibleFuelFailure_tail`. -/
theorem mixedFiveSixPrefix_of_not_mixedFailure
    {init : InputCfg n} {ω : InputLog n}
    {a four five u : ℕ} {Snapshot : InputCfg n → Prop}
    (hnot : ω ∉ mixedFailure init)
    (hcompletion : CompletionReceipt init ω a four five u Snapshot) :
    ∃ v, MixedFiveSixPrefix init ω u v := by
  apply mixedFiveSixPrefix_of_condition
  by_contra hbad
  apply hnot
  rw [mem_mixedFailure_iff]
  exact ⟨u, hcompletion.completed_at, hbad⟩

/-- `hmixed` of `LateMixedFuel.law_compatibleFuelFailure_tail`, verbatim, for
`mixedFailure := mixedFailure init`. -/
theorem hmixed_of_mixedFailure
    (init : InputCfg n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (σ : Sign) (M : ℝ) (Rlo Rhi : ℕ) :
    ∀ ω a four five u,
      ω ∉ mixedFailure init →
      LateSamplingCompletion.CompletionReceipt
          init ω a four five u
            (EntryFuelCertificate n ell hell σ M Rlo Rhi) →
      ∃ v, MixedFiveSixPrefix init ω u v :=
  fun _ _ _ _ _ hnot hcompletion =>
    mixedFiveSixPrefix_of_not_mixedFailure hnot hcompletion

/-!
THEOREM LIST
* `firstPhaseSevenStart_isStoppingTime`
* `firstPhaseSevenStart_past`
* `firstPhaseSevenStart_eq_iff`
* `completionReceipt_mixedFiveSixAt`
* `phase_lt_seven_before_firstPhaseSevenStart`
* `mixedFiveSixPrefix_of_condition`
* `mixedFiveSixPrefix_of_completion_and_timerRace`
* `mixedFiveSixPrefix_of_not_mixedFailure`
* `hmixed_of_mixedFailure`

CLOSES
* The deterministic half of the timer/epidemic mixed Phase-5/6 window.
* An explicit first-Phase-7 versus homogeneous-Phase-6 race event.
* `mixedFailure` as the complement of conditions (i) and (ii) on the genuine
  completion fibre.
* The exact `hmixed` implication consumed by
  `LateMixedFuel.law_compatibleFuelFailure_tail`.

EXPLICIT INPUTS
* A `CompletionReceipt`, supplied by row 3.
* Membership in the complement of `mixedFailure`; equivalently, the strict
  timer/epidemic race event.  Its law tail is not proved here.

UNFINISHED
* Prove the original-law tail for `mixedFailure` from the existing epidemic
  completion and Phase-6 timer-survival estimates.
* Package any measurability lemma needed by that probabilistic producer.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateMixedFiveSixWindow

end
