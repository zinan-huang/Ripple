-- Ripple/PopulationProtocol/ExactMajority/Probability/LatePhaseSixDrainPaperTimeline.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LatePhaseSixDrainFirstBarrierPaper
import Ripple.PopulationProtocol.ExactMajority.Probability.LateTimerProtectionOriginalLaw
import Ripple.PopulationProtocol.ExactMajority.Probability.LateTimerPrefixScalar
import Ripple.PopulationProtocol.ExactMajority.Probability.LateMixedFiveSixWindow
import Ripple.PopulationProtocol.ExactMajority.Probability.ThresholdEpidemic
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6BlockSnapshot
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingStrongSeedReceipt
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingSeedReceipt

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal NNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LatePhaseSixDrainPaperTimeline

open TimeTheorem PairLog TraceDrain StageEventSpec
open LateTimerPrefixScalar LateTimerProtectionOriginalLaw
open LatePhaseSixDrainPaperNumerics
open LatePhaseSixDrainFirstBarrierPaper
open LateMixedFuel LateMixedFiveSixWindow
open LateSamplingStrongSeedReceipt LateSamplingSeedReceipt

variable {n : ℕ}

/-- Three-unit threshold-6 spreading failure from the genuine first seed. -/
def phaseSixSpreadFailure (init : InputCfg n) : Set (InputLog n) :=
  {omega | ∃ seedSix : ℕ,
    firstPhaseSeed init 6 seedSix omega ∧
    ¬ ∀ a ∈ trace init omega (seedSix + logWindow n 3),
      6 ≤ a.phase.val}

/-- The existing N08 theorem gives exactly `e^3 n^-2`. -/
theorem law_phaseSixSpreadFailure_tail
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (phaseSixSpreadFailure init) ≤
      ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 2) := by
  have htail : law init (phaseSixSpreadFailure init) ≤
      ENNReal.ofReal
        (Real.exp 3 * Real.rpow (n : ℝ) (1 - ((3 : ℕ) : ℝ))) :=
    ThresholdEpidemic.threshold_spread_sharp_tail
      init hinput (⟨6, by decide⟩ : Fin 11) (by norm_num) 3 (by norm_num)
  have heq :
      Real.exp 3 * Real.rpow (n : ℝ) (1 - ((3 : ℕ) : ℝ)) =
        Real.exp 3 / (n : ℝ) ^ 2 := by
    show Real.exp 3 * (n : ℝ) ^ (1 - ((3 : ℕ) : ℝ)) = _
    rw [show (1 : ℝ) - ((3 : ℕ) : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_natCast,
      div_eq_mul_inv]
  rw [heq] at htail
  exact htail

/-- The guarded paper event, with a finite genuine Phase-6 seed and
non-strict guard `allThreeStart ≤ σ₆`. -/
def phaseSixTimerFailurePaper (init : InputCfg n) : Set (InputLog n) :=
  {omega | ∃ seedSix : ℕ,
    phaseSeedTime init 6 omega = (seedSix : WithTop ℕ) ∧
    LateF6OriginalLaw.allThreeStart init omega ≤
      (seedSix : WithTop ℕ) ∧
    phaseSeedTime init 7 omega ≤
      ((seedSix + protectionHorizon n : ℕ) : WithTop ℕ)}

/-- Explicit input.  A proof of the guarded
Lemma-3 route instantiates this record; the drain proof does not assume an
unguarded all-logs timer theorem. -/
structure GuardedPhaseSixTimerInput (init : InputCfg n) : Prop where
  tail : law init (phaseSixTimerFailurePaper init) ≤
    ENNReal.ofReal (Real.rpow (n : ℝ) (-(103 / 50 : ℝ)))

/-- All pathwise data needed at the paper's homogeneous Phase-6 start. -/
structure PhaseSixPaperStart
    (init : InputCfg n) (omega : InputLog n)
    (allThree four completed homogeneous seedSix M C R : ℕ)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (sigma : Sign) : Prop where
  all_three_time : LateF6OriginalLaw.allThreeStart init omega =
    (allThree : WithTop ℕ)
  six_seed : firstPhaseSeed init 6 seedSix omega
  guard : allThree ≤ seedSix
  path : LateF6OriginalLaw.Prefix init omega allThree four completed
  mixed : LateMixedFuel.MixedFiveSixPrefix
    init omega completed homogeneous
  readout : LateStrengthening.LateSeedReadout
    init M ell.val sigma (trace init omega four)
  density : StrongSeedDensity n M C R
  ready : PhaseSixDrainReady n ell (trace init omega homogeneous)

/-- Concrete assembly from the row-2/3/4 receipts.  The only extra
fields are the genuine Phase-6 seed and the all-three guard used by the timer. -/
theorem phaseSixPaperStart_of_receipts
    {init : InputCfg n} {omega : InputLog n}
    {seed allThree four five completed homogeneous seedSix M C R Rlo Rhi : ℕ}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (sigma : Sign)
    (hstrong : StrongSeedReceipt init omega seed allThree four five completed
      M C R
      (LateMixedFuel.EntryFuelCertificate n ell hell sigma (M : ℝ) Rlo Rhi))
    (hseed : LateSamplingSeedReceipt init M ell.val sigma
      (trace init omega four))
    (hfuel : LateMixedFuel.CompatibleFuelReceipt
      init omega allThree four five completed homogeneous
      ell hell sigma (M : ℝ) Rlo Rhi)
    (hsix : firstPhaseSeed init 6 seedSix omega)
    (hguard : allThree ≤ seedSix) :
    PhaseSixPaperStart init omega allThree four completed homogeneous
      seedSix M C R ell sigma := by
  exact
    { all_three_time := hstrong.completion.observed_path.all_start
      six_seed := hsix
      guard := hguard
      path := hstrong.completion.observed_path
      mixed := hfuel.mixed_path
      readout := hseed.toLateSeedReadout
      density := hstrong.density
      ready := ⟨⟨hfuel.population, hfuel.phase_six⟩, hfuel.ledger⟩ }

theorem PhaseSixPaperStart.sharpConfig
    {init : InputCfg n} {omega : InputLog n}
    {allThree four completed homogeneous seedSix M C R : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)} {sigma : Sign}
    (h : PhaseSixPaperStart init omega allThree four completed homogeneous
      seedSix M C R ell sigma)
    (hn : 2 ≤ n) :
    PhaseSixSharpConfig n ell (trace init omega homogeneous) :=
  phaseSixSharpConfig_of_receipts hn ell h.path h.mixed h.readout
    h.density h.ready

/-- Named upstream exceptional sets and their unconditional charges. -/
structure PhaseSixPaperStartProducer
    (init : InputCfg n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (seedFailure fuelFailure : Set (InputLog n))
    (seedBudget fuelBudget : ℝ≥0∞) : Prop where
  seed_tail : law init seedFailure ≤ seedBudget
  fuel_tail : law init fuelFailure ≤ fuelBudget
  produce : ∀ omega,
    omega ∉ seedFailure → omega ∉ fuelFailure →
    ∃ allThree four completed homogeneous seedSix M C R,
      ∃ sigma : Sign,
      PhaseSixPaperStart init omega allThree four completed homogeneous
        seedSix M C R ell sigma

/-- The five-way named union. -/
def phaseSixPaperFailure
    (init : InputCfg n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (seedFailure fuelFailure : Set (InputLog n)) : Set (InputLog n) :=
  seedFailure ∪
    (fuelFailure ∪
      (phaseSixSpreadFailure init ∪
        (phaseSixTimerFailurePaper init ∪
          phaseSixDrainFailure init ell hell)))

/-- Original-law accounting.  The drain contributes `n^-2.02` exactly once;
there is no hidden scalar or timer term. -/
theorem law_phaseSixPaperFailure_tail
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (seedFailure fuelFailure : Set (InputLog n))
    (seedBudget fuelBudget : ℝ≥0∞)
    (hstart : PhaseSixPaperStartProducer init ell hell
      seedFailure fuelFailure seedBudget fuelBudget)
    (htimer : GuardedPhaseSixTimerInput init) :
    law init (phaseSixPaperFailure init ell hell seedFailure fuelFailure) ≤
      seedBudget +
        (fuelBudget +
          (ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 2) +
            (ENNReal.ofReal
              (Real.rpow (n : ℝ) (-(103 / 50 : ℝ))) +
              phaseSixDrainBudget n))) := by
  calc
    law init (phaseSixPaperFailure init ell hell seedFailure fuelFailure) ≤
      law init seedFailure +
        law init
          (fuelFailure ∪
            (phaseSixSpreadFailure init ∪
              (phaseSixTimerFailurePaper init ∪
                phaseSixDrainFailure init ell hell))) :=
      measure_union_le _ _
    _ ≤ seedBudget +
        law init
          (fuelFailure ∪
            (phaseSixSpreadFailure init ∪
              (phaseSixTimerFailurePaper init ∪
                phaseSixDrainFailure init ell hell))) :=
      add_le_add hstart.seed_tail le_rfl
    _ ≤ seedBudget +
        (fuelBudget +
          law init
            (phaseSixSpreadFailure init ∪
              (phaseSixTimerFailurePaper init ∪
                phaseSixDrainFailure init ell hell))) := by
      gcongr
      exact (measure_union_le _ _).trans
        (add_le_add hstart.fuel_tail le_rfl)
    _ ≤ seedBudget +
        (fuelBudget +
          (ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 2) +
            law init
              (phaseSixTimerFailurePaper init ∪
                phaseSixDrainFailure init ell hell))) := by
      gcongr
      exact (measure_union_le _ _).trans
        (add_le_add (law_phaseSixSpreadFailure_tail init hinput) le_rfl)
    _ ≤ seedBudget +
        (fuelBudget +
          (ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 2) +
            (ENNReal.ofReal
              (Real.rpow (n : ℝ) (-(103 / 50 : ℝ))) +
              phaseSixDrainBudget n))) := by
      gcongr
      exact (measure_union_le _ _).trans
        (add_le_add htimer.tail
          (law_phaseSixDrainFailure_tail init hinput.1 ell hell))

private theorem phaseSeedTime_eq_of_firstPhaseSeed
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

/-- Output of the paper-timeline drain. -/
structure PhaseSixPaperDrainReceipt
    (init : InputCfg n) (omega : InputLog n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (homogeneous seedSix endpoint : ℕ) : Prop where
  homogeneous_time : LateMixedFuel.homogeneousSixStart init omega =
    (homogeneous : WithTop ℕ)
  ready : PhaseSixDrainReady n ell (trace init omega homogeneous)
  seed_time : phaseSeedTime init 6 omega = (seedSix : WithTop ℕ)
  endpoint_eq : endpoint = homogeneous + phaseSixDrainHorizon n
  before_seven : (endpoint : WithTop ℕ) <
    LateMixedFiveSixWindow.firstPhaseSevenStart init omega
  potential_zero : LatePotential.shallowLargePotential ell.val
    (trace init omega endpoint) = 0

/-- Paper timeline: spread from `σ₆`, drain from the genuine homogeneous-six
start, and protect the combined interval from `σ₆`. -/
theorem phaseSixPaperDrainReceipt_of_good
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (seedFailure fuelFailure : Set (InputLog n))
    (seedBudget fuelBudget : ℝ≥0∞)
    (hstart : PhaseSixPaperStartProducer init ell hell
      seedFailure fuelFailure seedBudget fuelBudget)
    (htimer : GuardedPhaseSixTimerInput init)
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
    phaseSeedTime_eq_of_firstPhaseSeed init omega 6 seedSix start.six_seed
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

/-- Zero base-128 potential is literally absence of a biased Main below `ell`. -/
theorem shallowLargePotential_eq_zero_iff_no_high
    (ell : ℕ) (c : InputCfg n) :
    LatePotential.shallowLargePotential ell c = 0 ↔
      ∀ a ∈ c,
        ¬ Phase6Convergence.highSt
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) ell a := by
  classical
  unfold LatePotential.shallowLargePotential
  rw [Multiset.sum_eq_zero_iff]
  constructor
  · intro h a ha hhigh
    obtain ⟨hm, sigma, j, hb, hj⟩ := hhigh
    have hz := h _ (Multiset.mem_map_of_mem _ ha)
    have hz' : 128 ^ (ell - j.val - 1) = 0 := by
      simpa [hm, hb, hj] using hz
    have hp : 0 < 128 ^ (ell - j.val - 1) := pow_pos (by norm_num) _
    omega
  · intro h x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    by_cases hm : a.role = .main
    · cases hb : a.bias with
      | zero => simp [hm, hb]
      | dyadic sigma j =>
          by_cases hj : j.val < ell
          · exact False.elim ((h a ha) ⟨hm, sigma, j, hb, hj⟩)
          · simp [hm, hb, hj]
    · simp [hm]

private theorem phiMass_applyDraw_le
    (ell population : ℕ) (c : InputCfg n)
    (hwin : Phase6Convergence.Phase6Win
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      population c)
    (d : Draw (PhaseThreeModel.Numeric.hourIndex n) 256) :
    Phase6PhiPotential.phiMass ell (applyDraw c d) ≤
      Phase6PhiPotential.phiMass ell c := by
  cases d with
  | none => exact le_rfl
  | some pair =>
      exact Phase6PhiDrift.phiMass_stepOrSelf_le
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        ell population c hwin pair.1.1 pair.2.1

private theorem phiMass_trace_le_of_phaseSix_sources
    (ell : ℕ) (init : InputCfg n) (omega : InputLog n)
    (start endpoint : ℕ) (hse : start ≤ endpoint)
    (hwin : ∀ u, start ≤ u → u < endpoint →
      Phase6Convergence.Phase6Win
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        n (trace init omega u)) :
    Phase6PhiPotential.phiMass ell (trace init omega endpoint) ≤
      Phase6PhiPotential.phiMass ell (trace init omega start) := by
  induction endpoint, hse using Nat.le_induction with
  | base => exact le_rfl
  | succ endpoint hse ih =>
      calc
        Phase6PhiPotential.phiMass ell
            (trace init omega (endpoint + 1)) =
          Phase6PhiPotential.phiMass ell
            (applyDraw (trace init omega endpoint) (omega (endpoint + 1))) := by
            rw [TraceDrain.trace_succ]
        _ ≤ Phase6PhiPotential.phiMass ell
            (trace init omega endpoint) :=
          phiMass_applyDraw_le ell n (trace init omega endpoint)
            (hwin endpoint hse (Nat.lt_succ_self endpoint))
            (omega (endpoint + 1))
        _ ≤ Phase6PhiPotential.phiMass ell
            (trace init omega start) :=
          ih (fun u hsu hue => hwin u hsu (by omega))

/-- At the genuine first Phase-7 hit, no biased Main below `ell` remains.  The
zero was reached strictly earlier, and base-4 monotonicity transports it over
the remaining homogeneous Phase-6 prefix and the seed interaction itself. -/
theorem no_shallow_main_at_firstPhaseSeven_of_receipt
    {init : InputCfg n} {omega : InputLog n}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {homogeneous seedSix endpoint seven : ℕ}
    (hreceipt : PhaseSixPaperDrainReceipt
      init omega ell homogeneous seedSix endpoint)
    (hseven : LateMixedFiveSixWindow.firstPhaseSevenStart init omega =
      (seven : WithTop ℕ)) :
    ∀ a ∈ trace init omega seven,
      ¬ Phase6Convergence.highSt
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) ell.val a := by
  have hendpointSevenTop : (endpoint : WithTop ℕ) < (seven : WithTop ℕ) := by
    rw [← hseven]
    exact hreceipt.before_seven
  have hendpointSeven : endpoint < seven :=
    WithTop.coe_lt_coe.mp hendpointSevenTop
  have hhomEndpoint : homogeneous ≤ endpoint := by
    rw [hreceipt.endpoint_eq]
    omega
  have hphiEndpoint :
      Phase6PhiPotential.phiMass ell.val
        (trace init omega endpoint) = 0 := by
    apply (Phase6PhiPotential.phiMass_eq_zero_iff ell.val
      (trace init omega endpoint)).2
    exact (shallowLargePotential_eq_zero_iff_no_high
      ell.val (trace init omega endpoint)).1 hreceipt.potential_zero
  have hmono := phiMass_trace_le_of_phaseSix_sources
    ell.val init omega endpoint seven hendpointSeven.le
    (fun u heu huSeven => by
      have hhomu : homogeneous ≤ u := hhomEndpoint.trans heu
      have hreach := trace_reachable init omega hhomu
      have hcard : (trace init omega u).card = n :=
        (Protocol.reachable_card_eq hreach).trans hreceipt.ready.win.1
      have hlower := PhaseOneDrainStopping.phase_lower_reachable 6
        (trace init omega homogeneous) (trace init omega u) hreach
        (fun b hb => (hreceipt.ready.win.2 b hb).ge)
      have huBefore : (u : WithTop ℕ) <
          LateMixedFiveSixWindow.firstPhaseSevenStart init omega := by
        rw [hseven]
        exact WithTop.coe_lt_coe.mpr huSeven
      have hupper :=
        LateMixedFiveSixWindow.phase_lt_seven_before_firstPhaseSevenStart
          init omega u huBefore
      refine ⟨hcard, ?_⟩
      intro b hb
      have hlo := hlower b hb
      have hhi := hupper b hb
      omega)
  have hphiSeven :
      Phase6PhiPotential.phiMass ell.val
        (trace init omega seven) = 0 := by omega
  exact (Phase6PhiPotential.phiMass_eq_zero_iff ell.val
    (trace init omega seven)).1 hphiSeven

/-- Public all-failure-complement form of Lemma 10's conclusion. -/
theorem no_shallow_main_at_firstPhaseSeven_of_good
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (seedFailure fuelFailure : Set (InputLog n))
    (seedBudget fuelBudget : ℝ≥0∞)
    (hstart : PhaseSixPaperStartProducer init ell hell
      seedFailure fuelFailure seedBudget fuelBudget)
    (htimer : GuardedPhaseSixTimerInput init)
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
    phaseSixPaperDrainReceipt_of_good init hinput ell hell
      seedFailure fuelFailure seedBudget fuelBudget
      hstart htimer omega hgood
  exact no_shallow_main_at_firstPhaseSeven_of_receipt hreceipt hseven

/-- Deterministic consumer for the mixed 6/7 row. -/
theorem phaseSixToSeven_consumer
    {L K : ℕ} (sigma : Sign) (ell blockFloor : ℕ)
    {start final : Config (AgentState L K)}
    (hreach : Phase6BlockSnapshot.Phase6To7Reachable start final)
    (hentry : Phase6BlockSnapshot.Phase6To7FuelLedger
      sigma ell blockFloor start) :
    Phase6BlockSnapshot.Phase6To7FuelLedger
        sigma ell blockFloor final ∧
      Phase7MajorityBlockLedger.MajorityBlockLedger
        sigma ell blockFloor final := by
  have hledger :=
    Phase6BlockSnapshot.phase6To7FuelLedger_of_reachable
      (L := L) (K := K) sigma ell blockFloor hreach hentry
  exact ⟨hledger,
    Phase6BlockSnapshot.majorityBlockLedger_of_phase6To7FuelLedger
      (L := L) (K := K) sigma ell blockFloor final hledger⟩

/-!
THEOREM LIST
* `phaseSixSpreadFailure`, `law_phaseSixSpreadFailure_tail`
* `phaseSixTimerFailurePaper`, `GuardedPhaseSixTimerInput`
* `PhaseSixPaperStart`, `phaseSixPaperStart_of_receipts`
* `PhaseSixPaperStartProducer`, `phaseSixPaperFailure`
* `law_phaseSixPaperFailure_tail`
* `PhaseSixPaperDrainReceipt`, `phaseSixPaperDrainReceipt_of_good`
* `shallowLargePotential_eq_zero_iff_no_high`
* `no_shallow_main_at_firstPhaseSeven_of_receipt`
* `no_shallow_main_at_firstPhaseSeven_of_good`
* `phaseSixToSeven_consumer`

CLOSES
* The original-law Phase-6 drain row on the literal paper timeline.
* Work is counted from the genuine homogeneous Phase-6 start; protection is
  counted from the genuine Phase-6 seed.
* Outside the five named failures, the base-128 potential reaches zero strictly
  before the first Phase-7 hit.
* At the first Phase-7 configuration, no biased Main has index below `ell`.
* The drain charge is `n^(-2.02)`; spread and guarded timer charges remain
  separate summands.
* The deterministic mixed 6/7 consumer is stated in the existing API.

CARRIED PREMISES AND PRODUCERS
* `GoodInput`: `ThresholdEpidemic.GoodInput` in the library.
* Three-unit spread tail: `ThresholdEpidemic.threshold_spread_sharp_tail` in the library.
* Sharp initial potential:
  `homogeneous_largePotential_lt_paper_power` in the library.
* `path`, `readout`, `density`: respectively
  `StrongSeedReceipt.completion.observed_path`,
  `LateSamplingSeedReceipt.toLateSeedReadout`, and
  `StrongSeedReceipt.density` in the library.
* homogeneous-six `ready`: `LateMixedFuel.CompatibleFuelReceipt` in the library.
* genuine Phase-6 seed plus `allThree ≤ seedSix`: carried by
  `PhaseSixPaperStartProducer`; its global assembly belongs to the upstream
  seed/timer seam and is charged by the named `seedFailure`.
* `GuardedPhaseSixTimerInput`: deliberately open here;
  it is the output expected from a proof of the guarded Lemma-3 route.

UNFINISHED
* Instantiation of `GuardedPhaseSixTimerInput` in the non-strict
  paper form.
* Global assembly of `PhaseSixPaperStartProducer` from the already named
  upstream seed and fuel failure sets.  The constructor above identifies every
  deterministic field and leaves only the stopping-time alignment/guard.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LatePhaseSixDrainPaperTimeline

end
