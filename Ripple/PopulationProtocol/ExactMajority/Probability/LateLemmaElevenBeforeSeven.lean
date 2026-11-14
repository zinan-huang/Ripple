-- Ripple/PopulationProtocol/ExactMajority/Probability/LateLemmaElevenBeforeSeven.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateLemmaElevenEntry

/-!
# Lemma 11 route through the first Phase-7 configuration

Current-main declarations used below:

* `LateBiasedResourceCreditPath.PhaseFiveSixCreditStep` has fields
  `source_reachable`, `source_window`, `sampled`, and `step`.
* `LateBiasedResourceCreditPath.PhaseFiveSixCreditReachable` is
  `Relation.ReflTransGen (PhaseFiveSixCreditStep init n)`.
* `LateBiasedResourceCreditPath.LemmaElevenPathReceipt.before_seven` asks for
  exactly the route proved by `phaseFiveSixCreditReachable_beforeSeven`.
* `LateLemmaElevenEntry.lemmaElevenEntry_of_completed_receipts` supplies the
  entry record used by the final small-history wrapper.

The sampling-completion time and homogeneous-Phase-6 time are intentionally
kept distinct.  Before the homogeneous time, `MixedFiveSixPrefix.source_window`
supplies the source window.  From that time until the first Phase-7 hit,
phase monotonicity gives the lower bound six and first-hit minimality gives the
strict upper bound seven.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateLemmaElevenBeforeSeven

open TimeTheorem StageEventSpec
open LateStrengthening
open LateMixedFuel LateMixedFuelLedger LateMixedFiveSixWindow
open LateSamplingCompletion LateSamplingStrongSeedReceipt
open LateSamplingStrongReceiptProducer
open LatePhaseSixDrainSelectedLevel
open LateBiasedResourceCreditPhaseSix
open LateBiasedResourceCreditPath
open LateLemmaElevenEntry

variable {L K n : ℕ}

private theorem trace_reachable_from_initial
    (init : InputCfg n) (omega : InputLog n) (t : ℕ) :
    (NonuniformMajority
      (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
        init (trace init omega t) := by
  simpa only [TimeTheorem.trace_zero] using
    (TimeTheorem.trace_reachable init omega
      (s := 0) (t := t) (Nat.zero_le t))

/-- Every source time from sampling completion up to, but not including, the
first Phase-7 configuration is in the exact mixed Phase-5/6 window.

For times before `homogeneous`, this is a field of `MixedFiveSixPrefix`.
After `homogeneous`, all agents have already reached Phase 6, and none has
reached Phase 7 by first-hit minimality. -/
theorem mixedFiveSixWin_before_firstSeven
    {init : InputCfg n} {omega : InputLog n}
    {completed homogeneous seven k : ℕ}
    (hcomplete : SamplingComplete n (trace init omega completed))
    (hmixed : MixedFiveSixPrefix init omega completed homogeneous)
    (hseven : firstPhaseSevenStart init omega = (seven : WithTop ℕ))
    (hcompleted : completed ≤ k) (hkseven : k < seven) :
    MixedFiveSixWin n (trace init omega k) := by
  by_cases hkHomogeneous : k < homogeneous
  · exact hmixed.source_window k hcompleted hkHomogeneous
  · have hhomogeneous : homogeneous ≤ k := Nat.le_of_not_gt hkHomogeneous
    have hreachCompleted :=
      TimeTheorem.trace_reachable init omega hcompleted
    have hcard : (trace init omega k).card = n :=
      (Protocol.reachable_card_eq hreachCompleted).trans
        hcomplete.population
    have hreachHomogeneous :=
      TimeTheorem.trace_reachable init omega hhomogeneous
    have hlower :
        ∀ a ∈ trace init omega k, 6 ≤ a.phase.val :=
      PhaseOneDrainStopping.phase_lower_reachable
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        6 (trace init omega homogeneous) (trace init omega k)
        hreachHomogeneous
        (fun a ha => by rw [hmixed.endpoint_phase_six a ha])
    have hkTop :
        (k : WithTop ℕ) < firstPhaseSevenStart init omega := by
      rw [hseven]
      exact WithTop.coe_lt_coe.mpr hkseven
    have hupper :
        ∀ a ∈ trace init omega k, a.phase.val < 7 :=
      phase_lt_seven_before_firstPhaseSevenStart
        init omega k hkTop
    refine ⟨hcard, ?_⟩
    intro a ha
    right
    have h1 := hlower a ha
    have h2 := hupper a ha
    omega

/-- Extend a route by one actual draw.  An applicable scheduled pair gives one
`PhaseFiveSixCreditStep`; a missing or inapplicable draw leaves the
configuration unchanged.  The same source hypotheses preserve the sample
lock for the next induction step. -/
private theorem phaseFiveSixCreditReachable_applyDraw
    {init start c : Config (AgentState L K)} {n : ℕ}
    (hroute : PhaseFiveSixCreditReachable init n start c)
    (hreached : ReachablePhaseSixWindow init c)
    (hwindow : MixedFiveSixWin (L := L) (K := K) n c)
    (hsampled : ReserveSampling.ReserveSampled (L := L) (K := K) c)
    (draw : Draw L K) :
    PhaseFiveSixCreditReachable init n start (applyDraw c draw) ∧
      ReserveSampling.ReserveSampled (L := L) (K := K)
        (applyDraw c draw) := by
  cases draw with
  | none =>
      exact ⟨hroute, hsampled⟩
  | some pair =>
      change
        PhaseFiveSixCreditReachable init n start
            (Protocol.stepOrSelf (NonuniformMajority L K)
              c pair.1.1 pair.2.1) ∧
          ReserveSampling.ReserveSampled (L := L) (K := K)
            (Protocol.stepOrSelf (NonuniformMajority L K)
              c pair.1.1 pair.2.1)
      by_cases happ : Protocol.Applicable c pair.1.1 pair.2.1
      · have hstep :
            PhaseFiveSixCreditStep init n c
              (Protocol.stepOrSelf (NonuniformMajority L K)
                c pair.1.1 pair.2.1) :=
          { source_reachable := hreached
            source_window := hwindow
            sampled := hsampled
            step := Protocol.stepRel_stepOrSelf_of_applicable
              (P := NonuniformMajority L K) happ }
        exact
          ⟨Relation.ReflTransGen.tail hroute hstep,
            reserveSampled_stepOrSelf_of_mixed
              (L := L) (K := K) n c hwindow hsampled
              pair.1.1 pair.2.1⟩
      · rw [Protocol.stepOrSelf_eq_self_of_not_applicable
          (P := NonuniformMajority L K) happ]
        exact ⟨hroute, hsampled⟩

/-- Simultaneously build the exact route and retain the sample lock at its
endpoint.  Retaining the lock is the induction invariant needed for the next
source step; it is not an extra premise of the public result. -/
theorem phaseFiveSixCreditReachable_and_sampled_beforeSeven
    {init : InputCfg n} {omega : InputLog n}
    {completed homogeneous seven : ℕ}
    (hcomplete : SamplingComplete n (trace init omega completed))
    (hmixed : MixedFiveSixPrefix init omega completed homogeneous)
    (hseven : firstPhaseSevenStart init omega = (seven : WithTop ℕ))
    (t : ℕ) (hcompleted : completed ≤ t) (htseven : t ≤ seven) :
    PhaseFiveSixCreditReachable init n
        (trace init omega completed) (trace init omega t) ∧
      ReserveSampling.ReserveSampled
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        (trace init omega t) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hcompleted
  revert htseven
  induction q with
  | zero =>
      intro _
      simp only [Nat.add_zero]
      exact ⟨Relation.ReflTransGen.refl, hcomplete.sampled⟩
  | succ q ih =>
      intro hnextSeven
      have hsourceSeven : completed + q < seven := by omega
      have hprevious := ih (by omega) (by omega)
      have hwindow :
          MixedFiveSixWin n (trace init omega (completed + q)) :=
        mixedFiveSixWin_before_firstSeven
          hcomplete hmixed hseven (by omega) hsourceSeven
      have hreached :
          ReachablePhaseSixWindow init
            (trace init omega (completed + q)) :=
        ReachablePhaseSixWindow.of_mixedFiveSix
          (trace_reachable_from_initial init omega (completed + q))
          hwindow
      rw [show completed + Nat.succ q = (completed + q) + 1 by omega,
        TimeTheorem.trace_succ]
      exact phaseFiveSixCreditReachable_applyDraw
        hprevious.1 hreached hwindow hprevious.2
        (omega ((completed + q) + 1))

/-- Exact type of `LemmaElevenPathReceipt.before_seven`. -/
theorem phaseFiveSixCreditReachable_beforeSeven
    {init : InputCfg n} {omega : InputLog n}
    {completed homogeneous seven : ℕ}
    (hcomplete : SamplingComplete n (trace init omega completed))
    (hmixed : MixedFiveSixPrefix init omega completed homogeneous)
    (hseven : firstPhaseSevenStart init omega = (seven : WithTop ℕ)) :
    ∀ t, completed ≤ t → t ≤ seven →
      PhaseFiveSixCreditReachable init n
        (trace init omega completed) (trace init omega t) := by
  intro t hcompleted htseven
  exact
    (phaseFiveSixCreditReachable_and_sampled_beforeSeven
      hcomplete hmixed hseven t hcompleted htseven).1

/-- Receipt-facing adapter.  This has precisely the deterministic data already
available with the completed snapshot; it introduces no event or all-log
premise. -/
theorem lemmaElevenBeforeSeven_of_strongReceipt
    {init : InputCfg n} {omega : InputLog n}
    {seed allThree four five completed homogeneous seven M C R : ℕ}
    {Snapshot : InputCfg n → Prop}
    (hstrong : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot)
    (hmixed : MixedFiveSixPrefix init omega completed homogeneous)
    (hseven : firstPhaseSevenStart init omega = (seven : WithTop ℕ)) :
    ∀ t, completed ≤ t → t ≤ seven →
      PhaseFiveSixCreditReachable init n
        (trace init omega completed) (trace init omega t) :=
  phaseFiveSixCreditReachable_beforeSeven
    hstrong.completion.complete hmixed hseven

/-- Small-history producer for the `LemmaElevenEntry` record together with the exact
`before_seven` field.  The only complement is the already named
`smallGapPhaseSixDrainFailure`; no additional failure set is introduced. -/
theorem exists_lemmaElevenBeforeSeven_of_smallHistory
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    (hsmall : omega ∈ smallHistory init)
    (hgood : omega ∉ smallGapPhaseSixDrainFailure init)
    (seven : ℕ)
    (hseven : firstPhaseSevenStart init omega = (seven : WithTop ℕ)) :
    ∃ seed allThree four : ℕ,
      ∃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
      ∃ hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n,
      ∃ sigma tau : Sign, ∃ five completed homogeneous M R : ℕ,
        sigma = oppositeSign tau ∧
          M = timeMainCount (trace init omega seed) ∧
          R = StageEventSpec.reserveCount (trace init omega seed) ∧
          MixedFiveSixPrefix init omega completed homogeneous ∧
          LemmaElevenEntry (M := M) (R := R) ell hell sigma tau
            (trace init omega completed) ∧
          (∀ t, completed ≤ t → t ≤ seven →
            PhaseFiveSixCreditReachable init n
              (trace init omega completed) (trace init omega t)) := by
  have hnotSnapshot :
      omega ∉ smallRowTwoSnapshotProductionFailure init := by
    intro hbad
    exact hgood (Or.inl hbad)
  have hnotMixed : omega ∉ mixedFailure init := by
    intro hbad
    exact hgood (Or.inr (Or.inl hbad))
  obtain ⟨seed, allThree, four, ell, hell, tau, five, completed,
      _hhistory, hseed, hstrong, _hledger⟩ :=
    exists_completedFuelLedger_of_smallHistory
      hinput hsmall hnotSnapshot
  obtain ⟨homogeneous, hmixed⟩ :=
    mixedFiveSixPrefix_of_not_mixedFailure
      hnotMixed hstrong.completion
  have hentry :
      LemmaElevenEntry
        (M := timeMainCount (trace init omega seed))
        (R := StageEventSpec.reserveCount (trace init omega seed))
        ell hell (oppositeSign tau) tau
        (trace init omega completed) :=
    lemmaElevenEntry_of_completed_receipts
      (M := timeMainCount (trace init omega seed))
      (C := StageEventSpec.clockCount (trace init omega seed))
      (R := StageEventSpec.reserveCount (trace init omega seed))
      hinput ell hell tau hseed hstrong hnotSnapshot
  have hbefore :=
    lemmaElevenBeforeSeven_of_strongReceipt
      hstrong hmixed hseven
  exact
    ⟨seed, allThree, four, ell, hell, oppositeSign tau, tau,
      five, completed, homogeneous,
      timeMainCount (trace init omega seed),
      StageEventSpec.reserveCount (trace init omega seed),
      rfl, rfl, rfl, hmixed, hentry, hbefore⟩

/-!
THEOREM LIST
* `mixedFiveSixWin_before_firstSeven`
* `phaseFiveSixCreditReachable_and_sampled_beforeSeven`
* `phaseFiveSixCreditReachable_beforeSeven`
* `lemmaElevenBeforeSeven_of_strongReceipt`
* `exists_lemmaElevenBeforeSeven_of_smallHistory`

CLOSES
* The exact `LemmaElevenPathReceipt.before_seven` relation from sampling
  completion through the first Phase-7 configuration.
* Locked `(5,5)`, mixed `(5,6)/(6,5)`, and homogeneous `(6,6)` source steps.
* Identity draws and inapplicable scheduled pairs without inventing a fake
  `StepRel` edge.
* Sample-lock preservation as the path induction invariant.
* Small-history wiring using the `LemmaElevenEntry` adapter and the
  existing `smallGapPhaseSixDrainFailure` complement.

CARRIED PREMISES AND PRODUCERS
* `hinput : GoodInput n init`: caller input; used by
  `exists_completedFuelLedger_of_smallHistory` and the `LemmaElevenEntry` adapter.
* `hsmall : omega ∈ smallHistory init`: caller branch membership.
* `hgood : omega ∉ smallGapPhaseSixDrainFailure init`: existing named
  complement.  Its first summand gives the completed snapshot receipt; its
  mixed-window summand gives `MixedFiveSixPrefix`.
* `hseven : firstPhaseSevenStart init omega = (seven : WithTop ℕ)`: the
  concrete first-Phase-7 time used by the eventual path receipt.  Its
  first-hit minimality is the only upper-phase input.
* `hstrong.completion.complete`: produced by
  `exists_completedFuelLedger_of_smallHistory`; supplies population, Phase-5
  homogeneity, and the initial sample lock.
* `hmixed`: produced by `mixedFiveSixPrefix_of_not_mixedFailure`; supplies the
  mixed source window and homogeneous-Phase-6 endpoint.
* No premise is quantified over all logs or arbitrary configurations.

UNFINISHED
* `after_seven`, `eight_seed`, and the final constructor of
  `LemmaElevenPathReceipt` are intentionally absent.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateLemmaElevenBeforeSeven

end
