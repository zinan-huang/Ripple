-- Ripple/PopulationProtocol/ExactMajority/Probability/LateLemmaThirteenRoute.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateLemmaThirteenDeterministic

/-!
# Lemma 13: original-law mixed 7/8 route

Imported from `LateLemmaThirteenDeterministic`:

* `PhaseSevenEightCreditReachable`, the source-guarded actual-step relation;
* `latePhaseEightCredit_floor_of_reachable`, the transported `.544 M` floor;
* `lemmaThirteen_availability_of_route`, which turns that floor and a
  homogeneous Phase-8 window into the `.26112 n` availability conclusion.

This file supplies their missing original-law route.  No premise below ranges
over all logs or arbitrary configurations.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateLemmaThirteenRoute

open TimeTheorem PairLog TraceDrain StageEventSpec
open PhaseOneDrain PhaseOneDrainStopping
open LateStrengthening
open LateBiasedResourceCreditPath
open LateBiasedResourceCreditPhaseSeven
open LateLemmaElevenFiniteTimes
open LateLemmaElevenAssembly
open LateLemmaTwelveSmallGap
open LateTimerProtectionOriginalLaw
open LateTimerProtectionGuarded
open LateTimerPrefixScalar
open LateTimerRouteProof
open LateTimerUpperOriginalLaw
open LateLemmaThirteenDeterministic
open LateF6OriginalLaw

variable {L K n M R : ℕ}

/-! ## New original-law failure sets -/

/-- Threshold 8 has not covered the population in three logarithmic units from
its genuine first seed. -/
def phaseEightSpreadFailure (init : InputCfg n) : Set (InputLog n) :=
  {omega | ∃ eight : ℕ,
    firstPhaseSeed init 8 eight omega ∧
      ¬ ∀ a ∈ trace init omega (eight + logWindow n 3),
        8 ≤ a.phase.val}

/-- Phase 9 appears inside the p=8 protected timer window. -/
def phaseEightProtectionFailure (init : InputCfg n) : Set (InputLog n) :=
  timerProtectionFailureGuarded init 8

/-- Exactly the two new exclusions needed for a finite homogeneous Phase-8
start and the eight-unit Phase-8 work interval. -/
def phaseEightHomogeneousFailure (init : InputCfg n) : Set (InputLog n) :=
  phaseEightSpreadFailure init ∪ phaseEightProtectionFailure init

noncomputable def phaseEightHomogeneousCharge (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
      (Real.exp 3 * Real.rpow (n : ℝ) (1 - (3 : ℝ))) +
    ENNReal.ofReal
      (Real.rpow (n : ℝ) (-(103 / 50 : ℝ)))

/-- The final Phase-8 work time. -/
def phaseEightWorkEnd (n homogeneousEight : ℕ) : ℕ :=
  homogeneousEight + logWindow n 8

/-! ### Measurability -/

theorem measurableSet_phaseEightSpreadFailure
    (init : InputCfg n) :
    MeasurableSet (phaseEightSpreadFailure init) := by
  rw [show phaseEightSpreadFailure init =
      ⋃ eight : ℕ,
        {omega | firstPhaseSeed init 8 eight omega} ∩
        {omega | ¬ ∀ a ∈ trace init omega
          (eight + logWindow n 3), 8 ≤ a.phase.val} by
    ext omega
    simp [phaseEightSpreadFailure]]
  apply MeasurableSet.iUnion
  intro eight
  apply (((pairLogFiltration
    (PhaseThreeModel.Numeric.hourIndex n) 256).le eight) _
      (firstPhaseSeed_measurableSet init 8 eight)).inter
  exact (Set.to_countable
    {c : InputCfg n | ¬ ∀ a ∈ c, 8 ≤ a.phase.val}).measurableSet.preimage
      ((measurable_trace_at init (eight + logWindow n 3)).mono
        ((pairLogFiltration
          (PhaseThreeModel.Numeric.hourIndex n) 256).le
            (eight + logWindow n 3)) le_rfl)

theorem measurableSet_phaseEightProtectionFailure
    (init : InputCfg n) :
    MeasurableSet (phaseEightProtectionFailure init) := by
  simpa only [phaseEightProtectionFailure] using
    measurableSet_timerProtectionFailureGuarded init 8

theorem measurableSet_phaseEightHomogeneousFailure
    (init : InputCfg n) :
    MeasurableSet (phaseEightHomogeneousFailure init) :=
  (measurableSet_phaseEightSpreadFailure init).union
    (measurableSet_phaseEightProtectionFailure init)

/-! ### Unconditional original-law bounds -/

theorem law_phaseEightSpreadFailure
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (phaseEightSpreadFailure init) ≤
      ENNReal.ofReal
        (Real.exp 3 * Real.rpow (n : ℝ) (1 - (3 : ℝ))) := by
  simpa [phaseEightSpreadFailure] using
    (ThresholdEpidemic.threshold_spread_sharp_tail
      init hinput (⟨8, by norm_num⟩ : Fin 11)
      (by norm_num) 3 (by norm_num))

theorem law_phaseEightProtectionFailure
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (phaseEightProtectionFailure init) ≤
      ENNReal.ofReal
        (Real.rpow (n : ℝ) (-(103 / 50 : ℝ))) := by
  simpa only [phaseEightProtectionFailure] using
    law_timerProtectionFailureGuarded_tail_of_goodInput
      init hinput 8 (by unfold LateTimedPhase; omega)

theorem law_phaseEightHomogeneousFailure
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (phaseEightHomogeneousFailure init) ≤
      phaseEightHomogeneousCharge n := by
  unfold phaseEightHomogeneousFailure phaseEightHomogeneousCharge
  exact (measure_union_le _ _).trans
    (add_le_add
      (law_phaseEightSpreadFailure init hinput)
      (law_phaseEightProtectionFailure init hinput))

/-! ## The 3+8 work interval fits inside timer protection -/

/-- Including both ceiling errors, eleven work units fit strictly inside the
`26.5 n log n` p=8 protection window. -/
theorem phaseEightWork_lt_protection
    {n : ℕ} (hn : timePopulationThreshold ≤ n) :
    logWindow n 3 + logWindow n 8 < protectionHorizon n := by
  obtain ⟨hnpos, hnlog⟩ :=
    ScalarTails.time_population_scalar_bounds hn
  have hlog0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hnOne : (1 : ℝ) ≤ n := by
    have h := Real.add_one_le_exp (Real.log (n : ℝ))
    rw [Real.exp_log hnpos] at h
    linarith
  let z : ℝ := (n : ℝ) * Real.log (n : ℝ)
  have hz : (100 : ℝ) ≤ z := by
    have hmul : (1 : ℝ) * 100 ≤
        (n : ℝ) * Real.log (n : ℝ) :=
      mul_le_mul hnOne hnlog (by norm_num) (by positivity)
    simpa [z] using hmul
  have hthree : (logWindow n 3 : ℝ) < 3 * z + 1 := by
    unfold logWindow
    convert Nat.ceil_lt_add_one
      (show 0 ≤ (3 : ℝ) * (n : ℝ) * Real.log (n : ℝ) by positivity)
      using 1 <;> dsimp [z] <;> ring
  have height : (logWindow n 8 : ℝ) < 8 * z + 1 := by
    unfold logWindow
    convert Nat.ceil_lt_add_one
      (show 0 ≤ (8 : ℝ) * (n : ℝ) * Real.log (n : ℝ) by positivity)
      using 1 <;> dsimp [z] <;> ring
  have hprotect : (53 / 2 : ℝ) * z ≤
      (protectionHorizon n : ℝ) := by
    unfold protectionHorizon
    convert Nat.le_ceil
      ((53 / 2 : ℝ) * (n : ℝ) * Real.log (n : ℝ))
      using 1 <;> dsimp [z] <;> ring
  have hreal :
      ((logWindow n 3 + logWindow n 8 : ℕ) : ℝ) <
        (protectionHorizon n : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast hreal

/-! ## Finite homogeneous Phase 8 and protected work interval -/

private theorem phaseSeedTime_eq_firstSeed
    (init : InputCfg n) (omega : InputLog n) (p seed : ℕ)
    (hseed : firstPhaseSeed init p seed omega) :
    phaseSeedTime init p omega = (seed : WithTop ℕ) := by
  apply (phaseSeedTime_eq_iff init p omega seed).2
  constructor
  · rcases hseed.1 with ⟨a, ha, hp⟩
    exact ⟨a, ha, hp.ge⟩
  · intro u hu hsome
    rcases hsome with ⟨a, ha, hge⟩
    exact (Nat.not_le_of_gt (hseed.2 u hu a ha)) hge

private theorem trace_card_eq_population
    {init : InputCfg n} {omega : InputLog n}
    (hcard : init.card = n) (t : ℕ) :
    (trace init omega t).card = n := by
  have hreach :
      (NonuniformMajority
        (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
        init (trace init omega t) := by
    simpa only [TimeTheorem.trace_zero] using
      (trace_reachable init omega
        (s := 0) (t := t) (Nat.zero_le t))
  exact (Protocol.reachable_card_eq hreach).trans hcard

/-- Recover the discarded all-three ordering from the same producer union.
The auxiliary producer call only identifies the unique first-seven time; all
Lemma-12 payload witnesses remain those in `hroute`. -/
private theorem allThreeStart_lt_eight_of_route
    {init : InputCfg n} {omega : InputLog n}
    {completed seven homogeneousSeven eight M R : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign}
    (hroute : LemmaTwelveRouteReceipt (M := M) (R := R)
      init omega completed seven homogeneousSeven eight ell hell sigma tau)
    (hgoodTwelve : omega ∉ lemmaTwelveFailure init) :
    allThreeStart init omega < (eight : WithTop ℕ) := by
  have hgoodEleven : omega ∉ lemmaElevenFailure init := by
    intro hbad
    exact hgoodTwelve (Or.inl hbad)
  have hphaseSixUpper : omega ∉ phaseSixUpperTimerFailure init := by
    intro hbad
    apply hgoodEleven
    exact lemmaElevenProducerFailure_subset_failure init
      (Or.inr (Or.inl hbad))
  obtain ⟨seedOther, allThreeOther, fourOther, ellOther, hellOther,
      sigmaOther, tauOther, fiveOther, completedOther, homogeneousOther,
      sevenOther, mainOther, reserveOther, signOther, mainEqOther,
      reserveEqOther, entryOther, hsevenOther⟩ :=
    exists_lemmaElevenEntry_and_finiteSeven
      hroute.path.good_input hroute.path.small_history
      hroute.path.selected_good hphaseSixUpper
  have hsevenTop : (sevenOther : WithTop ℕ) = (seven : WithTop ℕ) :=
    hsevenOther.seven_time.symm.trans hroute.path.seven_time
  have hsevenEq : sevenOther = seven := WithTop.coe_injective hsevenTop
  subst sevenOther
  exact hsevenOther.all_three_lt.trans_le
    (WithTop.coe_le_coe.mpr hroute.path.order.2)

/-- Timing payload for the Phase-8 work block. -/
structure PhaseEightFiniteReceipt
    (init : InputCfg n) (omega : InputLog n)
    (eight homogeneousEight : ℕ) : Prop where
  homogeneous_time :
    homogeneousLatePhaseStart init 8 omega =
      (homogeneousEight : WithTop ℕ)
  eight_le_homogeneous : eight ≤ homogeneousEight
  homogeneous_le_spread :
    homogeneousEight ≤ eight + logWindow n 3
  work_before_nine :
    (phaseEightWorkEnd n homogeneousEight : WithTop ℕ) <
      phaseSeedTime init 9 omega

namespace PhaseEightFiniteReceipt

/-- No agent has reached Phase 9 at any time through the work endpoint. -/
theorem no_phaseNine
    {init : InputCfg n} {omega : InputLog n}
    {eight homogeneousEight t : ℕ}
    (h : PhaseEightFiniteReceipt init omega eight homogeneousEight)
    (ht : t ≤ phaseEightWorkEnd n homogeneousEight) :
    ∀ a ∈ trace init omega t, a.phase.val < 9 := by
  have hbefore : (t : WithTop ℕ) < phaseSeedTime init 9 omega :=
    (WithTop.coe_le_coe.mpr ht).trans_lt h.work_before_nine
  have hnone := TraceDrain.not_of_lt_exitTime init
    (someGE (n := n) 9) omega t
    (by simpa only [phaseSeedTime] using hbefore)
  intro a ha
  by_contra hbad
  exact hnone t le_rfl ⟨a, ha, by omega⟩

end PhaseEightFiniteReceipt

/-- Threshold-8 spread plus the guarded p=8 timer produce the genuine first
homogeneous Phase-8 time and protect the complete eight-unit work block. -/
theorem exists_phaseEightFiniteReceipt
    {init : InputCfg n} {omega : InputLog n}
    {completed seven homogeneousSeven eight M R : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign}
    (hroute : LemmaTwelveRouteReceipt (M := M) (R := R)
      init omega completed seven homogeneousSeven eight ell hell sigma tau)
    (hallThree : allThreeStart init omega < (eight : WithTop ℕ))
    (hgood : omega ∉ phaseEightHomogeneousFailure init) :
    ∃ homogeneousEight : ℕ,
      PhaseEightFiniteReceipt init omega eight homogeneousEight := by
  have hnotSpread : omega ∉ phaseEightSpreadFailure init := by
    intro hbad
    exact hgood (Or.inl hbad)
  have hnotProtection : omega ∉ phaseEightProtectionFailure init := by
    intro hbad
    exact hgood (Or.inr hbad)
  have heightTime :
      phaseSeedTime init 8 omega = (eight : WithTop ℕ) :=
    phaseSeedTime_eq_firstSeed init omega 8 eight hroute.path.eight_seed
  have htimer :
      ((eight + protectionHorizon n : ℕ) : WithTop ℕ) <
        phaseSeedTime init 9 omega := by
    by_contra hbad
    apply hnotProtection
    exact ⟨eight, heightTime, hallThree, le_of_not_gt hbad⟩
  have hfit := phaseEightWork_lt_protection hroute.path.good_input.1
  have hspreadLe : logWindow n 3 ≤ protectionHorizon n := by omega
  have hgeEight :
      ∀ a ∈ trace init omega (eight + logWindow n 3),
        8 ≤ a.phase.val := by
    by_contra hbad
    exact hnotSpread ⟨eight, hroute.path.eight_seed, hbad⟩
  have hltNine :
      ∀ a ∈ trace init omega (eight + logWindow n 3),
        a.phase.val < 9 := by
    intro a ha
    by_contra hbad
    have hhit : someGE (n := n) 9
        (trace init omega (eight + logWindow n 3)) :=
      ⟨a, ha, by omega⟩
    have hleSpread : phaseSeedTime init 9 omega ≤
        ((eight + logWindow n 3 : ℕ) : WithTop ℕ) := by
      simpa only [phaseSeedTime] using
        (TraceDrain.exitTime_le_iff init (someGE (n := n) 9) omega
          (eight + logWindow n 3)).2
          ⟨eight + logWindow n 3, le_rfl, hhit⟩
    have hleProtection : phaseSeedTime init 9 omega ≤
        ((eight + protectionHorizon n : ℕ) : WithTop ℕ) :=
      hleSpread.trans (WithTop.coe_le_coe.mpr
        (show eight + logWindow n 3 ≤ eight + protectionHorizon n by omega))
    exact (not_lt_of_ge hleProtection) htimer
  have hpureSpread :
      allPhaseExactly 8
        (trace init omega (eight + logWindow n 3)) := by
    intro a ha
    have hlo := hgeEight a ha
    have hhi := hltNine a ha
    omega
  have hhomogeneousTop :
      homogeneousLatePhaseStart init 8 omega ≤
        ((eight + logWindow n 3 : ℕ) : WithTop ℕ) := by
    simpa only [homogeneousLatePhaseStart] using
      (TraceDrain.exitTime_le_iff init (allPhaseExactly 8) omega
        (eight + logWindow n 3)).2
        ⟨eight + logWindow n 3, le_rfl, hpureSpread⟩
  have hhomogeneousFinite :
      homogeneousLatePhaseStart init 8 omega ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hhomogeneousTop
  obtain ⟨homogeneousEight, hhomogeneousRev⟩ :=
    WithTop.ne_top_iff_exists.mp hhomogeneousFinite
  have hhomogeneousTime :
      homogeneousLatePhaseStart init 8 omega =
        (homogeneousEight : WithTop ℕ) :=
    hhomogeneousRev.symm
  have hhomogeneousLe :
      homogeneousEight ≤ eight + logWindow n 3 := by
    have hh := hhomogeneousTop
    rw [hhomogeneousTime] at hh
    exact WithTop.coe_le_coe.mp hh
  have hpureHomogeneous :
      allPhaseExactly 8 (trace init omega homogeneousEight) :=
    ((homogeneousLatePhaseStart_eq_iff
      init 8 homogeneousEight omega).mp hhomogeneousTime).1
  have hcard : (trace init omega homogeneousEight).card = n :=
    trace_card_eq_population hroute.path.good_input.2.2 homogeneousEight
  have hpositive : 0 < (trace init omega homogeneousEight).card := by
    rw [hcard]
    have hnlarge := (time_population_bounds hroute.path.good_input.1).2
    omega
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp hpositive
  have hsomeEight : someGE (n := n) 8
      (trace init omega homogeneousEight) :=
    ⟨a, ha, by rw [hpureHomogeneous a ha]⟩
  have hseedLe : phaseSeedTime init 8 omega ≤
      (homogeneousEight : WithTop ℕ) := by
    simpa only [phaseSeedTime] using
      (TraceDrain.exitTime_le_iff init (someGE (n := n) 8) omega
        homogeneousEight).2
        ⟨homogeneousEight, le_rfl, hsomeEight⟩
  have heightHomogeneous : eight ≤ homogeneousEight := by
    rw [heightTime] at hseedLe
    exact WithTop.coe_le_coe.mp hseedLe
  have hworkNat :
      phaseEightWorkEnd n homogeneousEight <
        eight + protectionHorizon n := by
    unfold phaseEightWorkEnd
    omega
  have hworkBefore :
      (phaseEightWorkEnd n homogeneousEight : WithTop ℕ) <
        phaseSeedTime init 9 omega :=
    (WithTop.coe_lt_coe.mpr hworkNat).trans htimer
  exact ⟨homogeneousEight,
    { homogeneous_time := hhomogeneousTime
      eight_le_homogeneous := heightHomogeneous
      homogeneous_le_spread := hhomogeneousLe
      work_before_nine := hworkBefore }⟩

/-! ## The concrete mixed 7/8 route -/

private theorem trace_reachable_from_initial
    (init : InputCfg n) (omega : InputLog n) (t : ℕ) :
    (NonuniformMajority
      (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
        init (trace init omega t) := by
  simpa only [TimeTheorem.trace_zero] using
    (trace_reachable init omega
      (s := 0) (t := t) (Nat.zero_le t))

/-- Every source from the first Phase-8 seed through the work interval lies
in phases 7 or 8. -/
private theorem phaseSevenEightWindow_before_work
    {init : InputCfg n} {omega : InputLog n}
    {completed seven homogeneousSeven eight homogeneousEight M R k : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign}
    (hroute : LemmaTwelveRouteReceipt (M := M) (R := R)
      init omega completed seven homogeneousSeven eight ell hell sigma tau)
    (htiming : PhaseEightFiniteReceipt init omega eight homogeneousEight)
    (heightK : eight ≤ k)
    (hkWork : k < phaseEightWorkEnd n homogeneousEight) :
    PhaseSevenEightWindow (trace init omega k) := by
  have hdeadline := phaseSevenDeadline_lt_eight hroute
  have hhomogeneousK : homogeneousSeven ≤ k := by omega
  have hpureSeven :
      allPhaseExactly 7 (trace init omega homogeneousSeven) :=
    ((homogeneousLatePhaseStart_eq_iff
      init 7 homogeneousSeven omega).mp
        hroute.height.homogeneous_time).1
  have hreach := trace_reachable init omega hhomogeneousK
  have hlower :=
    PhaseOneDrainStopping.phase_lower_reachable
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      7 (trace init omega homogeneousSeven) (trace init omega k)
      hreach (fun a ha => by rw [hpureSeven a ha])
  intro a ha
  have hlo := hlower a ha
  have hhi := htiming.no_phaseNine (Nat.le_of_lt hkWork) a ha
  omega

/-- Extend the source-guarded route by one recorded draw. -/
private theorem phaseSevenEightCreditReachable_applyDraw
    {init start c : Config (AgentState L K)}
    (hroute : PhaseSevenEightCreditReachable init start c)
    (hreached : (NonuniformMajority L K).Reachable init c)
    (hwindow : PhaseSevenEightWindow c)
    (draw : Draw L K) :
    PhaseSevenEightCreditReachable init start (applyDraw c draw) := by
  cases draw with
  | none => exact hroute
  | some pair =>
      change PhaseSevenEightCreditReachable init start
        (Protocol.stepOrSelf (NonuniformMajority L K)
          c pair.1.1 pair.2.1)
      by_cases happ : Protocol.Applicable c pair.1.1 pair.2.1
      · have hstep : PhaseSevenEightCreditStep init c
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

/-- The actual relation from the exact first Phase-8 seed to every time
through the protected eight-unit work endpoint. -/
theorem phaseSevenEightCreditReachable_afterEight
    {init : InputCfg n} {omega : InputLog n}
    {completed seven homogeneousSeven eight homogeneousEight M R : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign}
    (hroute : LemmaTwelveRouteReceipt (M := M) (R := R)
      init omega completed seven homogeneousSeven eight ell hell sigma tau)
    (htiming : PhaseEightFiniteReceipt init omega eight homogeneousEight) :
    ∀ t, eight ≤ t → t ≤ phaseEightWorkEnd n homogeneousEight →
      PhaseSevenEightCreditReachable init
        (trace init omega eight) (trace init omega t) := by
  intro t heightT htWork
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le heightT
  revert htWork
  induction q with
  | zero =>
      intro _
      simp only [Nat.add_zero]
      exact Relation.ReflTransGen.refl
  | succ q ih =>
      intro hnextWork
      have hsourceWork : eight + q < phaseEightWorkEnd n homogeneousEight := by
        omega
      have hprevious := ih (by omega) (by omega)
      have hwindow := phaseSevenEightWindow_before_work
        hroute htiming (by omega) hsourceWork
      have hreached := trace_reachable_from_initial
        init omega (eight + q)
      rw [show eight + Nat.succ q = (eight + q) + 1 by omega,
        TimeTheorem.trace_succ]
      exact phaseSevenEightCreditReachable_applyDraw
        hprevious hreached hwindow (omega ((eight + q) + 1))

/-- Every time from the first homogeneous Phase-8 state through the work end
is a genuine full-population homogeneous Phase-8 window. -/
theorem phaseEightWin_during_work
    {init : InputCfg n} {omega : InputLog n}
    {completed seven homogeneousSeven eight homogeneousEight M R t : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign}
    (hroute : LemmaTwelveRouteReceipt (M := M) (R := R)
      init omega completed seven homogeneousSeven eight ell hell sigma tau)
    (htiming : PhaseEightFiniteReceipt init omega eight homogeneousEight)
    (hhomogeneous : homogeneousEight ≤ t)
    (htWork : t ≤ phaseEightWorkEnd n homogeneousEight) :
    PhaseOnlyWindows.Phase8Win
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      n (trace init omega t) := by
  have hpure : allPhaseExactly 8
      (trace init omega homogeneousEight) :=
    ((homogeneousLatePhaseStart_eq_iff
      init 8 homogeneousEight omega).mp htiming.homogeneous_time).1
  have hreach := trace_reachable init omega hhomogeneous
  have hlower :=
    PhaseOneDrainStopping.phase_lower_reachable
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      8 (trace init omega homogeneousEight) (trace init omega t)
      hreach (fun a ha => by rw [hpure a ha])
  refine ⟨trace_card_eq_population hroute.path.good_input.2.2 t, ?_⟩
  intro a ha
  have hlo := hlower a ha
  have hhi := htiming.no_phaseNine htWork a ha
  omega

/-! ## Threaded route receipt and deterministic conclusions -/

structure LemmaThirteenRouteReceipt {n M R : ℕ}
    (init : InputCfg n) (omega : InputLog n)
    (completed seven homogeneousSeven eight homogeneousEight : ℕ)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (sigma tau : Sign) : Prop where
  twelve : LemmaTwelveRouteReceipt (M := M) (R := R)
    init omega completed seven homogeneousSeven eight ell hell sigma tau
  deep : AllMinorityIndicesAbove sigma ell (trace init omega eight)
  timing : PhaseEightFiniteReceipt init omega eight homogeneousEight
  route :
    ∀ t, eight ≤ t → t ≤ phaseEightWorkEnd n homogeneousEight →
      PhaseSevenEightCreditReachable init
        (trace init omega eight) (trace init omega t)

/-- At every homogeneous Phase-8 time in the work interval, equations (55)
and (56) hold in the exact integer scalings used by `LateLemmaThirteenDeterministic`. -/
theorem lemmaThirteenRouteReceipt_bounds_at
    {init : InputCfg n} {omega : InputLog n}
    {completed seven homogeneousSeven eight homogeneousEight M R t : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign}
    (h : LemmaThirteenRouteReceipt (M := M) (R := R)
      init omega completed seven homogeneousSeven eight homogeneousEight
      ell hell sigma tau)
    (hhomogeneous : homogeneousEight ≤ t)
    (htWork : t ≤ phaseEightWorkEnd n homogeneousEight) :
    NoShallowMain ell (trace init omega t) ∧
      AllMinorityIndicesAbove sigma ell (trace init omega t) ∧
      (544 : ℤ) * (M : ℤ) ≤
        1000 * latePhaseEightCredit sigma ell hell (trace init omega t) ∧
      Phase7Convergence.minorityU sigma (trace init omega t) ≤
        availableMajorityCount sigma (trace init omega t) ∧
      26112 * n ≤
        100000 * (availableMajorityCount sigma (trace init omega t) -
          Phase7Convergence.minorityU sigma (trace init omega t)) := by
  have hreach := h.route t
    (h.timing.eight_le_homogeneous.trans hhomogeneous) htWork
  have hEight := phaseEightWin_during_work
    h.twelve h.timing hhomogeneous htWork
  exact lemmaThirteen_availability_of_route
    h.twelve h.deep hreach hEight

/-! ## Charged public producer -/

noncomputable def lemmaThirteenRouteFailure
    (init : InputCfg n) : Set (InputLog n) :=
  lemmaTwelveFailure init ∪ phaseEightHomogeneousFailure init

noncomputable def lemmaThirteenRouteFailureCharge (n : ℕ) : ℝ≥0∞ :=
  lemmaTwelveFailureCharge n + phaseEightHomogeneousCharge n

theorem measurableSet_lemmaThirteenRouteFailure
    (init : InputCfg n) :
    MeasurableSet (lemmaThirteenRouteFailure init) := by
  unfold lemmaThirteenRouteFailure
  exact (measurableSet_lemmaTwelveFailure init).union
    (measurableSet_phaseEightHomogeneousFailure init)

theorem law_lemmaThirteenRouteFailure
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (lemmaThirteenRouteFailure init) ≤
      lemmaThirteenRouteFailureCharge n := by
  unfold lemmaThirteenRouteFailure lemmaThirteenRouteFailureCharge
  exact (measure_union_le _ _).trans
    (add_le_add
      (law_lemmaTwelveFailure init hinput)
      (law_phaseEightHomogeneousFailure init hinput))

/-- One threaded choice of all Lemma-12 and Phase-8 timing witnesses. -/
theorem exists_lemmaThirteenRouteReceipt_of_smallHistory
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    (hsmall : omega ∈ smallHistory init)
    (hgood : omega ∉ lemmaThirteenRouteFailure init) :
    ∃ completed seven homogeneousSeven eight homogeneousEight : ℕ,
      ∃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
      ∃ hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n,
      ∃ sigma tau : Sign, ∃ M R : ℕ,
        LemmaThirteenRouteReceipt (M := M) (R := R)
          init omega completed seven homogeneousSeven eight homogeneousEight
          ell hell sigma tau := by
  have hgoodTwelve : omega ∉ lemmaTwelveFailure init := by
    intro hbad
    exact hgood (Or.inl hbad)
  have hgoodEight : omega ∉ phaseEightHomogeneousFailure init := by
    intro hbad
    exact hgood (Or.inr hbad)
  have hgoodEleven : omega ∉ lemmaElevenFailure init := by
    intro hbad
    exact hgoodTwelve (Or.inl hbad)
  have hgoodBands : omega ∉ phaseSevenWitnessFailure init := by
    intro hbad
    exact hgoodTwelve (Or.inr hbad)
  obtain ⟨completed, seven, homogeneousSeven, eight,
      ell, hell, sigma, tau, M, R, hroute⟩ :=
    exists_lemmaTwelveRouteReceipt_of_smallHistory
      hinput hsmall hgoodEleven
  obtain ⟨_hclear, hdeep⟩ :=
    phaseSevenBands_clear_at_firstEight hroute hgoodBands
  have hallThree :=
    allThreeStart_lt_eight_of_route hroute hgoodTwelve
  obtain ⟨homogeneousEight, htiming⟩ :=
    exists_phaseEightFiniteReceipt hroute hallThree hgoodEight
  have hafter := phaseSevenEightCreditReachable_afterEight
    hroute htiming
  refine ⟨completed, seven, homogeneousSeven, eight, homogeneousEight,
    ell, hell, sigma, tau, M, R, ?_⟩
  exact
    { twelve := hroute
      deep := hdeep
      timing := htiming
      route := hafter }

/-!
THEOREM LIST
* `phaseEightSpreadFailure`, `phaseEightProtectionFailure`,
  `phaseEightHomogeneousFailure`, `phaseEightHomogeneousCharge`
* `measurableSet_phaseEightSpreadFailure`
* `measurableSet_phaseEightProtectionFailure`
* `measurableSet_phaseEightHomogeneousFailure`
* `law_phaseEightSpreadFailure`
* `law_phaseEightProtectionFailure`
* `law_phaseEightHomogeneousFailure`
* `phaseEightWork_lt_protection`
* `PhaseEightFiniteReceipt`, `PhaseEightFiniteReceipt.no_phaseNine`
* `exists_phaseEightFiniteReceipt`
* `phaseSevenEightCreditReachable_afterEight`
* `phaseEightWin_during_work`
* `LemmaThirteenRouteReceipt`
* `lemmaThirteenRouteReceipt_bounds_at`
* `lemmaThirteenRouteFailure`, `lemmaThirteenRouteFailureCharge`
* `measurableSet_lemmaThirteenRouteFailure`
* `law_lemmaThirteenRouteFailure`
* `exists_lemmaThirteenRouteReceipt_of_smallHistory`

CLOSES ITEM 1
* Outside `phaseEightSpreadFailure`, threshold 8 covers by
  `eight + ceil(3 n log n)`.
* Outside `phaseEightProtectionFailure`, the first Phase-9 seed is later than
  `eight + protectionHorizon n`.
* The ceiling-safe inequality `ceil(3 n log n) + ceil(8 n log n) <
  protectionHorizon n` puts the complete work endpoint strictly before Phase 9.
* The genuine first homogeneous Phase-8 time is finite and has the requested
  upper bound.  The endpoint itself is included in the no-Phase-9 statement.

CLOSES ITEM 2
* Every source from `eight` through the work endpoint is reachable and lies in
  exact phase 7 or 8; identity and inapplicable draws add no fake relation edge.
* `PhaseSevenEightCreditReachable` is constructed for every requested time.
* Every time from `homogeneousEight` through the work endpoint is a genuine
  `Phase8Win`, so `LateLemmaThirteenDeterministic` yields both `J_8 >= .544 M` and
  `A_avail - B_minus >= .26112 n` there.

CLOSES ITEM 3
* `LemmaThirteenRouteReceipt` retains one threaded Lemma-12 witness choice,
  the same first Phase-8 seed, the same `ell`, signs, `M`, and `R`, together
  with the finite homogeneous endpoint and full route.
* `lemmaThirteenRouteFailure` is measurable and has unconditional law at most
  `lemmaTwelveFailureCharge n + phaseEightHomogeneousCharge n` under
  `GoodInput`.

CARRIED PREMISES AND PRODUCERS
* `GoodInput` and membership in `smallHistory` are the only caller premises.
* `LemmaTwelveRouteReceipt` is produced by
  `exists_lemmaTwelveRouteReceipt_of_smallHistory` outside the already charged
  `lemmaElevenFailure` component of `lemmaTwelveFailure`.
* `AllMinorityIndicesAbove` for the same witness tuple is produced by
  `phaseSevenBands_clear_at_firstEight` outside the already charged
  `phaseSevenWitnessFailure` component.
* `allThreeStart < eight` is recovered from
  `exists_lemmaElevenEntry_and_finiteSeven`; uniqueness of the first-seven
  time identifies its `seven` with the one already stored in the route.
* Threshold-8 spread is `ThresholdEpidemic.threshold_spread_sharp_tail`.
* p=8 timer protection is
  `law_timerProtectionFailureGuarded_tail_of_goodInput`.
* Trace reachability, phase monotonicity, and one-step recursion are available in
  `TimeTheorem` and `PhaseOneDrainStopping`.
* No premise is quantified over all logs or arbitrary configurations.

UNFINISHED
* The scheduler hazard and multiplicative minority-drain estimate (57),
  including the final `n^(-3.17792)` law bound, remain open.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateLemmaThirteenRoute

end
