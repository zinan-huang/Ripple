-- Ripple/PopulationProtocol/ExactMajority/Probability/LateLemmaElevenAfterSeven.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateLemmaElevenFiniteTimes

/-!
# Lemma 11: the source-guarded route from Phase 7 to the first Phase-8 seed

Declarations of `LateLemmaElevenFiniteTimes` used here (restated for convenience):

* `SevenFiniteReceipt init omega completed homogeneous seven` has fields
  `mixed : MixedFiveSixPrefix init omega completed homogeneous`,
  `seven_time`, `seven_seed : firstPhaseSeed init 7 seven omega`,
  `completed_le`, and `all_three_lt`.
* `EightSeedReceipt init omega seven homogeneous eight` has fields
  `homogeneous_time`, `homogeneous_le_spread`,
  `eight_seed : firstPhaseSeed init 8 eight omega`,
  `seven_le_eight`, and `eight_le_horizon`.
* `exists_eightSeed_of_finiteSeven` constructs the latter receipt outside
  `phaseSevenHomogeneousFailure` and `phaseSevenUpperTimerFailure`.

The surface used here is:

* `PhaseSixSevenCreditStep init c d`, with fields
  `source_reachable : ReachablePhaseSixWindow init c`,
  `source_window : Phase6To7Window c`, and the actual protocol `step`;
* `PhaseSixSevenCreditReachable init c d =
    Relation.ReflTransGen (PhaseSixSevenCreditStep init) c d`.

No homogeneous-Phase-7 premise is used by the route after the exact first
Phase-8 seed has been supplied.  The target at time `eight` may contain Phase
8; only every source time `< eight` must remain in the 6/7 window.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateLemmaElevenAfterSeven

open TimeTheorem
open LateMixedFuel
open Phase6BlockSnapshot
open LateBiasedResourceCreditPhaseSix
open LateBiasedResourceCreditPhaseSeven
open LateLemmaElevenFiniteTimes

variable {L K n : ℕ}

private theorem trace_reachable_from_initial
    (init : InputCfg n) (omega : InputLog n) (t : ℕ) :
    (NonuniformMajority
      (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
        init (trace init omega t) := by
  simpa only [TimeTheorem.trace_zero] using
    (TimeTheorem.trace_reachable init omega
      (s := 0) (t := t) (Nat.zero_le t))

/-- The homogeneous Phase-6 time stored in `SevenFiniteReceipt` is strictly
before the genuine first Phase-7 seed.  This fact was used in the
constructor of `LateLemmaElevenFiniteTimes` but was not stored as a separate field; it follows from the
receipt itself.

If the first Phase-7 seed were before the homogeneous-six time, the
`MixedFiveSixPrefix.source_window` field would say its seed agent is still in
Phase 5 or 6.  Equality contradicts the homogeneous-six endpoint directly. -/
theorem homogeneousSix_lt_firstSeven
    {init : InputCfg n} {omega : InputLog n}
    {completed homogeneous seven : ℕ}
    (h : SevenFiniteReceipt init omega completed homogeneous seven) :
    homogeneous < seven := by
  by_contra hnot
  have hle : seven ≤ homogeneous := Nat.le_of_not_gt hnot
  by_cases heq : seven = homogeneous
  · subst homogeneous
    obtain ⟨a, ha, hseven⟩ := h.seven_seed.1
    have hsix := h.mixed.endpoint_phase_six a ha
    omega
  · have hlt : seven < homogeneous := lt_of_le_of_ne hle heq
    have hwindow := h.mixed.source_window seven h.completed_le hlt
    obtain ⟨a, ha, hseven⟩ := h.seven_seed.1
    rcases hwindow.2 a ha with hfive | hsix <;> omega

/-- Every actual source configuration from `seven` up to but excluding
`eight` is exactly in the mixed Phase-6/7 seam.

The lower bound is phase monotonicity from the exact homogeneous Phase-6
configuration.  The strict upper bound is the minimality clause of the exact
first Phase-8 seed. -/
theorem phaseSixToSevenWindow_before_firstEight
    {init : InputCfg n} {omega : InputLog n}
    {completed sixHomogeneous seven sevenHomogeneous eight k : ℕ}
    (hseven :
      SevenFiniteReceipt init omega completed sixHomogeneous seven)
    (height :
      EightSeedReceipt init omega seven sevenHomogeneous eight)
    (hsevenK : seven ≤ k) (hkEight : k < eight) :
    Phase6To7Window
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      (trace init omega k) := by
  have hsixSeven : sixHomogeneous < seven :=
    homogeneousSix_lt_firstSeven hseven
  have hsixK : sixHomogeneous ≤ k :=
    hsixSeven.le.trans hsevenK
  have hreach := TimeTheorem.trace_reachable init omega hsixK
  have hlower :
      ∀ a ∈ trace init omega k, 6 ≤ a.phase.val :=
    PhaseOneDrainStopping.phase_lower_reachable
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      6 (trace init omega sixHomogeneous) (trace init omega k)
      hreach
      (fun a ha => by rw [hseven.mixed.endpoint_phase_six a ha])
  intro a ha
  have hlo := hlower a ha
  have hhi := height.eight_seed.2 k hkEight a ha
  omega

/-- Reachability metadata needed by `PhaseSixSevenCreditStep` at every source
strictly before the first Phase-8 seed. -/
theorem reachablePhaseSixWindow_before_firstEight
    {init : InputCfg n} {omega : InputLog n}
    {completed sixHomogeneous seven sevenHomogeneous eight k : ℕ}
    (hseven :
      SevenFiniteReceipt init omega completed sixHomogeneous seven)
    (height :
      EightSeedReceipt init omega seven sevenHomogeneous eight)
    (hsevenK : seven ≤ k) (hkEight : k < eight) :
    ReachablePhaseSixWindow init (trace init omega k) := by
  exact ReachablePhaseSixWindow.of_phaseSixToSeven
    (trace_reachable_from_initial init omega k)
    (phaseSixToSevenWindow_before_firstEight
      hseven height hsevenK hkEight)

/-- Extend the source-guarded route by one recorded draw.  `none` and an
inapplicable scheduled pair leave the configuration unchanged; only an actual
applicable pair contributes a relation edge. -/
private theorem phaseSixSevenCreditReachable_applyDraw
    {init start c : Config (AgentState L K)}
    (hroute : PhaseSixSevenCreditReachable init start c)
    (hreached : ReachablePhaseSixWindow init c)
    (hwindow : Phase6To7Window (L := L) (K := K) c)
    (draw : Draw L K) :
    PhaseSixSevenCreditReachable init start (applyDraw c draw) := by
  cases draw with
  | none =>
      exact hroute
  | some pair =>
      change
        PhaseSixSevenCreditReachable init start
          (Protocol.stepOrSelf (NonuniformMajority L K)
            c pair.1.1 pair.2.1)
      by_cases happ : Protocol.Applicable c pair.1.1 pair.2.1
      · have hstep :
            PhaseSixSevenCreditStep init c
              (Protocol.stepOrSelf (NonuniformMajority L K)
                c pair.1.1 pair.2.1) :=
          { source_reachable := hreached
            source_window := hwindow
            step := Protocol.stepRel_stepOrSelf_of_applicable
              (P := NonuniformMajority L K) happ }
        exact Relation.ReflTransGen.tail hroute hstep
      · rw [Protocol.stepOrSelf_eq_self_of_not_applicable
          (P := NonuniformMajority L K) happ]
        exact hroute

/-- Exact type of `LemmaElevenPathReceipt.after_seven`.

At `t = eight`, the induction adds the edge whose source is `eight - 1`.
That source is still below Phase 8 by `height.eight_seed.2`; the target is
intentionally not required to satisfy `ReachablePhaseSixWindow`. -/
theorem phaseSixSevenCreditReachable_afterSeven
    {init : InputCfg n} {omega : InputLog n}
    {completed sixHomogeneous seven sevenHomogeneous eight : ℕ}
    (hseven :
      SevenFiniteReceipt init omega completed sixHomogeneous seven)
    (height :
      EightSeedReceipt init omega seven sevenHomogeneous eight) :
    ∀ t, seven ≤ t → t ≤ eight →
      PhaseSixSevenCreditReachable init
        (trace init omega seven) (trace init omega t) := by
  intro t hsevenT htEight
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hsevenT
  revert htEight
  induction q with
  | zero =>
      intro _
      simp only [Nat.add_zero]
      exact Relation.ReflTransGen.refl
  | succ q ih =>
      intro hnextEight
      have hsourceEight : seven + q < eight := by omega
      have hprevious := ih (by omega) (by omega)
      have hwindow :
          Phase6To7Window
            (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
            (trace init omega (seven + q)) :=
        phaseSixToSevenWindow_before_firstEight
          hseven height (by omega) hsourceEight
      have hreached :
          ReachablePhaseSixWindow init
            (trace init omega (seven + q)) :=
        reachablePhaseSixWindow_before_firstEight
          hseven height (by omega) hsourceEight
      rw [show seven + Nat.succ q = (seven + q) + 1 by omega,
        TimeTheorem.trace_succ]
      exact phaseSixSevenCreditReachable_applyDraw
        hprevious hreached hwindow
        (omega ((seven + q) + 1))

/-- Failure-facing adapter.  At this stage only the two Phase-7 exclusions are
needed: `LateLemmaElevenFiniteTimes` uses them to construct an exact `EightSeedReceipt`; the route is
then deterministic.  The earlier `phaseSixUpperTimerFailure` has already been
spent in producing `hseven`, and `phaseSevenSpreadFailure` is already included
in `phaseSevenHomogeneousFailure`. -/
theorem exists_eightSeed_and_afterSeven
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    {completed sixHomogeneous seven : ℕ}
    (hseven :
      SevenFiniteReceipt init omega completed sixHomogeneous seven)
    (hhomogeneousGood :
      omega ∉ phaseSevenHomogeneousFailure init)
    (hupperGood :
      omega ∉ phaseSevenUpperTimerFailure init) :
    ∃ sevenHomogeneous eight : ℕ,
      EightSeedReceipt init omega seven sevenHomogeneous eight ∧
        (∀ t, seven ≤ t → t ≤ eight →
          PhaseSixSevenCreditReachable init
            (trace init omega seven) (trace init omega t)) := by
  obtain ⟨sevenHomogeneous, eight, height⟩ :=
    exists_eightSeed_of_finiteSeven
      hinput hseven.seven_seed hseven.all_three_lt
      hhomogeneousGood hupperGood
  exact ⟨sevenHomogeneous, eight, height,
    phaseSixSevenCreditReachable_afterSeven hseven height⟩

/-!
THEOREM LIST
* `homogeneousSix_lt_firstSeven`
* `phaseSixToSevenWindow_before_firstEight`
* `reachablePhaseSixWindow_before_firstEight`
* `phaseSixSevenCreditReachable_afterSeven`
* `exists_eightSeed_and_afterSeven`

CLOSES
* The exact `LemmaElevenPathReceipt.after_seven` field, including the final
  target at the first Phase-8 seed.
* Every nontrivial recorded transition has an actual
  `PhaseSixSevenCreditStep`; identity and inapplicable draws introduce no fake
  protocol edge.
* The source lower bound six comes from the homogeneous Phase-6 receipt of `LateLemmaElevenFiniteTimes`;
  the source upper bound seven comes from exact first-Phase-8 minimality.
* No new failure event, measurability lemma, or law charge is introduced.

FAILURE ACCOUNTING
* `phaseSixUpperTimerFailure`: needed upstream to construct
  `SevenFiniteReceipt`; `LateLemmaElevenFiniteTimes` proves
  `law_phaseSixUpperTimerFailure ≤ ENNReal.ofReal (1 / n^5)`.
* `phaseSevenSpreadFailure`: not separately required here; it is included in
  `phaseSevenHomogeneousFailure`.
* `phaseSevenHomogeneousFailure`: needed upstream for the exact homogeneous
  Phase-7 state and to exclude an early Phase-8 seed during spreading;
  `LateLemmaElevenFiniteTimes` proves the spread bound plus the guarded `n^(-103/50)` timer charge.
* `phaseSevenUpperTimerFailure`: needed upstream to make the first Phase-8
  seed finite; `LateLemmaElevenFiniteTimes` proves its `n^(-5)` bound.

CARRIED PREMISES AND PRODUCERS
* `hseven : SevenFiniteReceipt`: produced by
  `exists_lemmaElevenEntry_and_finiteSeven`; no all-log premise.
* `height : EightSeedReceipt`: produced by
  `exists_eightSeed_of_finiteSeven`; its exact `eight_seed` field supplies all
  strict upper-phase bounds used here.
* `hseven.mixed`: produced from the mixed-window condition; its exact
  homogeneous Phase-6 endpoint supplies the lower-phase bound.
* Trace reachability and one-step recursion are available in `TimeTheorem`.
* No premise is quantified over all logs or arbitrary configurations.

UNFINISHED
* The final constructor combining `LateLemmaElevenEntry`, `LateLemmaElevenBeforeSeven`,
  `LateLemmaElevenFiniteTimes` and this `after_seven` theorem into
  `LemmaElevenPathReceipt` is intentionally outside this file.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateLemmaElevenAfterSeven

end
