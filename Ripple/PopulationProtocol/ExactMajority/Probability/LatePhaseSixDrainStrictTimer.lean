-- Ripple/PopulationProtocol/ExactMajority/Probability/LatePhaseSixDrainStrictTimer.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LatePhaseSixDrainPaperTimeline
import Ripple.PopulationProtocol.ExactMajority.Probability.LateTimerRouteProof
import Ripple.PopulationProtocol.ExactMajority.Probability.LateTimerProtectionGuarded

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal NNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LatePhaseSixDrainStrictTimer

open TimeTheorem PairLog TraceDrain StageEventSpec
open LateTimerPrefixScalar LateTimerProtectionOriginalLaw
open LatePhaseSixDrainPaperNumerics LatePhaseSixDrainFirstBarrierPaper
open LatePhaseSixDrainPaperTimeline
open LateMixedFuel LateMixedFiveSixWindow
open LateSamplingStrongSeedReceipt LateSamplingSeedReceipt

variable {n : ℕ}

private theorem phaseSeedTime_eq_of_firstPhaseSeed'
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

/-- Pathwise strictness of the guard.  At `allThree` every agent has phase
exactly `3`, so no phase-`6` agent exists there; a genuine first phase-`6`
seed at `seedSix ≥ allThree` is therefore strictly later. -/
theorem phaseSixPaperStart_allThree_lt_seedSix
    {init : InputCfg n} {omega : InputLog n}
    {allThree four completed homogeneous seedSix M C R : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)} {sigma : Sign}
    (h : PhaseSixPaperStart init omega allThree four completed homogeneous
      seedSix M C R ell sigma) :
    allThree < seedSix := by
  rcases lt_or_eq_of_le h.guard with hlt | heq
  · exact hlt
  · exfalso
    subst heq
    obtain ⟨a, ha, hsix⟩ := h.six_seed.1
    have hthree := h.path.all_three a ha
    omega

/-- Strict form of the start data in `WithTop ℕ`. -/
theorem phaseSixPaperStart_allThreeStart_lt_phaseSeedTime
    {init : InputCfg n} {omega : InputLog n}
    {allThree four completed homogeneous seedSix M C R : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)} {sigma : Sign}
    (h : PhaseSixPaperStart init omega allThree four completed homogeneous
      seedSix M C R ell sigma) :
    LateF6OriginalLaw.allThreeStart init omega < (seedSix : WithTop ℕ) := by
  rw [h.all_three_time]
  exact WithTop.coe_lt_coe.mpr (phaseSixPaperStart_allThree_lt_seedSix h)

/-- Outside the seed and fuel failures, the paper timer event is contained in
the strict guarded event proved on main. -/
theorem phaseSixTimerFailurePaper_diff_subset_guarded
    (init : InputCfg n) (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (seedFailure fuelFailure : Set (InputLog n))
    (seedBudget fuelBudget : ℝ≥0∞)
    (hstart : PhaseSixPaperStartProducer init ell hell
      seedFailure fuelFailure seedBudget fuelBudget) :
    phaseSixTimerFailurePaper init \ (seedFailure ∪ fuelFailure) ⊆
      LateTimerProtectionGuarded.timerProtectionFailureGuarded init 6 := by
  rintro omega ⟨⟨s, hs, _hguard, hnext⟩, hnot⟩
  have hnotSeed : omega ∉ seedFailure := fun h => hnot (Or.inl h)
  have hnotFuel : omega ∉ fuelFailure := fun h => hnot (Or.inr h)
  obtain ⟨allThree, four, completed, homogeneous, seedSix, M, C, R,
      sigma, start⟩ := hstart.produce omega hnotSeed hnotFuel
  have hseedTime :=
    phaseSeedTime_eq_of_firstPhaseSeed' init omega 6 seedSix start.six_seed
  have hss : s = seedSix :=
    WithTop.coe_injective (hs.symm.trans hseedTime)
  subst hss
  exact ⟨s, hs, phaseSixPaperStart_allThreeStart_lt_phaseSeedTime start, hnext⟩

/-- The paper failure union is charged without any timer hypothesis: the
timer summand is the strict guarded tail already on main. -/
theorem law_phaseSixPaperFailure_tail_strict
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (seedFailure fuelFailure : Set (InputLog n))
    (seedBudget fuelBudget : ℝ≥0∞)
    (hstart : PhaseSixPaperStartProducer init ell hell
      seedFailure fuelFailure seedBudget fuelBudget) :
    law init (phaseSixPaperFailure init ell hell seedFailure fuelFailure) ≤
      seedBudget +
        (fuelBudget +
          (ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 2) +
            (ENNReal.ofReal
              (Real.rpow (n : ℝ) (-(103 / 50 : ℝ))) +
              phaseSixDrainBudget n))) := by
  have hguarded :
      law init (LateTimerProtectionGuarded.timerProtectionFailureGuarded init 6) ≤
        ENNReal.ofReal (Real.rpow (n : ℝ) (-(103 / 50 : ℝ))) :=
    LateTimerRouteProof.law_timerProtectionFailureGuarded_tail_of_goodInput
      init hinput 6 (by unfold LateTimedPhase; omega)
  have hsub : phaseSixPaperFailure init ell hell seedFailure fuelFailure ⊆
      seedFailure ∪
        (fuelFailure ∪
          (phaseSixSpreadFailure init ∪
            (LateTimerProtectionGuarded.timerProtectionFailureGuarded init 6 ∪
              phaseSixDrainFailure init ell hell))) := by
    intro omega hom
    rcases hom with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · by_cases hsf : omega ∈ seedFailure ∪ fuelFailure
      · rcases hsf with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          (phaseSixTimerFailurePaper_diff_subset_guarded init ell hell
            seedFailure fuelFailure seedBudget fuelBudget hstart ⟨h, hsf⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  calc
    law init (phaseSixPaperFailure init ell hell seedFailure fuelFailure) ≤
      law init
        (seedFailure ∪
          (fuelFailure ∪
            (phaseSixSpreadFailure init ∪
              (LateTimerProtectionGuarded.timerProtectionFailureGuarded init 6 ∪
                phaseSixDrainFailure init ell hell)))) := measure_mono hsub
    _ ≤ law init seedFailure +
        law init
          (fuelFailure ∪
            (phaseSixSpreadFailure init ∪
              (LateTimerProtectionGuarded.timerProtectionFailureGuarded init 6 ∪
                phaseSixDrainFailure init ell hell))) :=
      measure_union_le _ _
    _ ≤ seedBudget +
        (fuelBudget +
          (ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 2) +
            (ENNReal.ofReal
              (Real.rpow (n : ℝ) (-(103 / 50 : ℝ))) +
              phaseSixDrainBudget n))) := by
      refine add_le_add hstart.seed_tail ?_
      refine (measure_union_le _ _).trans (add_le_add hstart.fuel_tail ?_)
      refine (measure_union_le _ _).trans
        (add_le_add (law_phaseSixSpreadFailure_tail init hinput) ?_)
      exact (measure_union_le _ _).trans
        (add_le_add hguarded
          (law_phaseSixDrainFailure_tail init hinput.1 ell hell))

/-- `phaseSixPaperDrainReceipt_of_good` without the unused `htimer` hypothesis:
the proof only reads the timer through `hgood`. -/
theorem phaseSixPaperDrainReceipt_of_good_strict
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (seedFailure fuelFailure : Set (InputLog n))
    (seedBudget fuelBudget : ℝ≥0∞)
    (hstart : PhaseSixPaperStartProducer init ell hell
      seedFailure fuelFailure seedBudget fuelBudget)
    (omega : InputLog n)
    (hgood : omega ∉
      phaseSixPaperFailure init ell hell seedFailure fuelFailure) :
    ∃ homogeneous seedSix endpoint,
      PhaseSixPaperDrainReceipt init omega ell homogeneous seedSix endpoint := by
  have hnotSeed : omega ∉ seedFailure :=
    fun h => hgood (Or.inl h)
  have hnotFuel : omega ∉ fuelFailure :=
    fun h => hgood (Or.inr (Or.inl h))
  have hnotSpread : omega ∉ phaseSixSpreadFailure init :=
    fun h => hgood (Or.inr (Or.inr (Or.inl h)))
  have hnotTimer : omega ∉ phaseSixTimerFailurePaper init :=
    fun h => hgood (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have hnotDrain : omega ∉ phaseSixDrainFailure init ell hell :=
    fun h => hgood (Or.inr (Or.inr (Or.inr (Or.inr h))))
  obtain ⟨allThree, four, completed, homogeneous, seedSix, M, C, R,
      sigma, start⟩ := hstart.produce omega hnotSeed hnotFuel
  have hnlarge : 2 ≤ n := by
    have := (time_population_bounds hinput.1).2
    omega
  have hseedTime :=
    phaseSeedTime_eq_of_firstPhaseSeed' init omega 6 seedSix start.six_seed
  have hguardTop : LateF6OriginalLaw.allThreeStart init omega ≤
      (seedSix : WithTop ℕ) := by
    rw [start.all_three_time]
    exact_mod_cast start.guard
  have htimerLate :
      ((seedSix + protectionHorizon n : ℕ) : WithTop ℕ) <
        phaseSeedTime init 7 omega := by
    by_contra hnot
    apply hnotTimer
    exact ⟨seedSix, hseedTime, hguardTop, not_lt.mp hnot⟩
  have htimerSeven :
      ((seedSix + protectionHorizon n : ℕ) : WithTop ℕ) <
        LateMixedFiveSixWindow.firstPhaseSevenStart init omega := by
    simpa [LateTimerProtectionOriginalLaw.phaseSeedTime,
      LateMixedFiveSixWindow.firstPhaseSevenStart] using htimerLate
  have hallSix :
      ∀ a ∈ trace init omega (seedSix + logWindow n 3),
        6 ≤ a.phase.val := by
    by_contra hbad
    apply hnotSpread
    exact ⟨seedSix, start.six_seed, hbad⟩
  have hfit := spread_add_drain_horizon_le_protection hinput.1
  have hspreadLe : logWindow n 3 ≤ protectionHorizon n := by omega
  have hspreadBefore :
      ((seedSix + logWindow n 3 : ℕ) : WithTop ℕ) <
        LateMixedFiveSixWindow.firstPhaseSevenStart init omega :=
    (WithTop.coe_le_coe.mpr (Nat.add_le_add_left hspreadLe seedSix)).trans_lt
      htimerSeven
  have hbelowSix :=
    LateMixedFiveSixWindow.phase_lt_seven_before_firstPhaseSevenStart
      init omega (seedSix + logWindow n 3) hspreadBefore
  have hallExact : LateMixedFuel.allPhaseSix
      (trace init omega (seedSix + logWindow n 3)) := by
    intro a ha
    have hlo := hallSix a ha
    have hhi := hbelowSix a ha
    omega
  have hhomoTop : LateMixedFuel.homogeneousSixStart init omega ≤
      ((seedSix + logWindow n 3 : ℕ) : WithTop ℕ) := by
    simpa only [LateMixedFuel.homogeneousSixStart] using
      (TraceDrain.exitTime_le_iff init LateMixedFuel.allPhaseSix omega
        (seedSix + logWindow n 3)).2
        ⟨seedSix + logWindow n 3, le_rfl, hallExact⟩
  rw [start.mixed.six_start] at hhomoTop
  have hhomoLe : homogeneous ≤ seedSix + logWindow n 3 :=
    WithTop.coe_le_coe.mp hhomoTop
  let endpoint := homogeneous + phaseSixDrainHorizon n
  have hendpointLe : endpoint ≤ seedSix + protectionHorizon n := by
    dsimp [endpoint]
    omega
  have hbefore : (endpoint : WithTop ℕ) <
      LateMixedFiveSixWindow.firstPhaseSevenStart init omega :=
    (WithTop.coe_le_coe.mpr hendpointLe).trans_lt htimerSeven
  have hnoSeven : ¬ SomeSeven (trace init omega endpoint) := by
    intro hsome
    rcases hsome with ⟨a, ha, hge⟩
    have hlt :=
      LateMixedFiveSixWindow.phase_lt_seven_before_firstPhaseSevenStart
        init omega endpoint hbefore a ha
    omega
  have hsharp := start.sharpConfig hnlarge
  have hpotential : LatePotential.shallowLargePotential ell.val
      (trace init omega endpoint) = 0 := by
    by_contra hpos
    apply hnotDrain
    refine ⟨homogeneous, start.mixed.six_start, hsharp, ?_, ?_⟩
    · simpa only [endpoint] using hnoSeven
    · simpa only [endpoint] using hpos
  exact ⟨homogeneous, seedSix, endpoint,
    { homogeneous_time := start.mixed.six_start
      ready := start.ready
      seed_time := hseedTime
      endpoint_eq := rfl
      before_seven := hbefore
      potential_zero := hpotential }⟩

/-- Lemma 10's conclusion outside the five named failures, with no timer
hypothesis. -/
theorem no_shallow_main_at_firstPhaseSeven_of_good_strict
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (seedFailure fuelFailure : Set (InputLog n))
    (seedBudget fuelBudget : ℝ≥0∞)
    (hstart : PhaseSixPaperStartProducer init ell hell
      seedFailure fuelFailure seedBudget fuelBudget)
    (omega : InputLog n)
    (hgood : omega ∉
      phaseSixPaperFailure init ell hell seedFailure fuelFailure)
    (seven : ℕ)
    (hseven : LateMixedFiveSixWindow.firstPhaseSevenStart init omega =
      (seven : WithTop ℕ)) :
    ∀ a ∈ trace init omega seven,
      ¬ Phase6Convergence.highSt
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) ell.val a := by
  obtain ⟨homogeneous, seedSix, endpoint, hreceipt⟩ :=
    phaseSixPaperDrainReceipt_of_good_strict init hinput ell hell
      seedFailure fuelFailure seedBudget fuelBudget
      hstart omega hgood
  exact no_shallow_main_at_firstPhaseSeven_of_receipt hreceipt hseven

/-!
THEOREM LIST
* `phaseSixPaperStart_allThree_lt_seedSix`
* `phaseSixPaperStart_allThreeStart_lt_phaseSeedTime`
* `phaseSixTimerFailurePaper_diff_subset_guarded`
* `law_phaseSixPaperFailure_tail_strict`
* `phaseSixPaperDrainReceipt_of_good_strict`
* `no_shallow_main_at_firstPhaseSeven_of_good_strict`
-/

end Ripple.PopulationProtocol.ExactMajority.LatePhaseSixDrainStrictTimer

end
