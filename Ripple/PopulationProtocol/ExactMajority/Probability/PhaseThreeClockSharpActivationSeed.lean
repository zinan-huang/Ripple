-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockSharpActivationSeed.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockSharpActivation

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockSharpActivationSeed

open TimeTheorem PairLog PhaseThreeClockVirtual PhaseThreeClockGatedLaw
  PhaseThreeClockProbabilityFloors PhaseThreeClockActivationLaw
  PhaseThreeClockActivationSeed PhaseThreeClockActivationTails PhaseThreeClockSeedTails
  PhaseThreeClockSmallActivation PhaseThreeClockMacroscopicActivation
  PhaseThreeClockSharpActivation PhaseThreeClockActivationCalibration

variable {L K : ℕ}

def lateMacroscopicFromSmall (init : Cfg L K) (s C N : ℕ) : Set (Ω L K) :=
  {ω | ∃ u : ℕ, smallActivationTime init s C ω = (u : WithTop ℕ) ∧
    ((u + N : ℕ) : WithTop ℕ) < macroscopicTime init s ω}

def sharpActivationFailure (init : Cfg L K) (s C : ℕ) : Set (Ω L K) :=
  {ω | smallActivationTime init s C ω = ⊤} ∪
    lateMacroscopicFromSmall init s C (PhaseThreeModel.Numeric.activationHalfHorizon init.card)

theorem smallActivation_prefix_fibre_measurable (init : Cfg L K) (s C u : ℕ)
    (E : Set (Ω L K)) (hE : MeasurableSet[pairLogFiltration L K s] E) :
    MeasurableSet[pairLogFiltration L K u]
      (E ∩ {ω | smallActivationTime init s C ω = (u : WithTop ℕ)}) := by
  by_cases hsu : s ≤ u
  · exact (((pairLogFiltration L K).mono hsu) _ hE).inter
      (smallActivationTime_pastTime init s C u)
  · have hempty : E ∩ {ω | smallActivationTime init s C ω = (u : WithTop ℕ)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      exact hsu (smallActivationTime_finite_state init s C u ω hω.2).1
    rw [hempty]
    exact MeasurableSpace.measurableSet_empty _

theorem lateMacroscopic_fibre_measurable (init : Cfg L K) (s C u N : ℕ) :
    MeasurableSet[pairLogFiltration L K (u + N)]
      ({ω | smallActivationTime init s C ω = (u : WithTop ℕ)} ∩
        {ω | ((u + N : ℕ) : WithTop ℕ) < macroscopicTime init s ω}) :=
  (((pairLogFiltration L K).mono (by omega : u ≤ u + N)) _
    (smallActivationTime_pastTime init s C u)).inter
      ((macroscopicTime_isStoppingTime init s).measurableSet_gt (u + N))

theorem sharp_small_to_macroscopic_prefix_tail (init : Cfg L K) (s C : ℕ)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ init.card)
    (hlo : (6 / 25 : ℝ) * (init.card : ℝ) ≤ (C : ℝ)) (hCn : C ≤ init.card)
    (E : Set (Ω L K)) (hE : MeasurableSet[pairLogFiltration L K s] E) :
    law init (E ∩ lateMacroscopicFromSmall init s C
      (PhaseThreeModel.Numeric.activationHalfHorizon init.card)) ≤
      ENNReal.ofReal (1 / (C : ℝ) ^ 100) * law init E := by
  let N := PhaseThreeModel.Numeric.activationHalfHorizon init.card
  let A : ℕ → Set (Ω L K) :=
    fun u => E ∩ {ω | smallActivationTime init s C ω = (u : WithTop ℕ)}
  let B : ℕ → Set (Ω L K) :=
    fun u => {ω | ((u + N : ℕ) : WithTop ℕ) < macroscopicTime init s ω}
  have hprefix (u : ℕ) : MeasurableSet[pairLogFiltration L K u] (A u) :=
    smallActivation_prefix_fibre_measurable init s C u E hE
  have hdisj : Pairwise (fun u v => Disjoint (A u) (A v)) := by
    intro u v huv
    apply Set.disjoint_left.mpr
    rintro ω ⟨-, hu⟩ ⟨-, hv⟩
    exact huv (WithTop.coe_injective (hu.symm.trans hv))
  have hcover : E ∩ lateMacroscopicFromSmall init s C N ⊆ ⋃ u, A u ∩ B u := by
    rintro ω ⟨hω, u, hu, hb⟩
    exact Set.mem_iUnion.mpr ⟨u, ⟨hω, hu⟩, hb⟩
  have hmass : (∑' u, law init (A u)) ≤ law init E := by
    rw [← measure_iUnion hdisj
      (fun u => ((pairLogFiltration L K).le u) _ (hprefix u))]
    apply measure_mono
    intro ω hω
    obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hω
    exact hu.1
  have hlocal (u : ℕ) :
      law init (A u ∩ B u) ≤ ENNReal.ofReal (1 / (C : ℝ) ^ 100) * law init (A u) := by
    have hstart : ∀ ω ∈ A u, PhaseThreeModel.Numeric.smallActivation C ≤
        PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u) :=
      fun ω hω => (smallActivationTime_finite_state init s C u ω hω.2).2
    have hsub : A u ∩ B u ⊆
        A u ∩ {ω | PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω (u + N)) <
          macroscopicThreshold init.card} := by
      rintro ω ⟨hω, hb⟩
      have hsu := (smallActivationTime_finite_state init s C u ω hω.2).1
      exact ⟨hω, (macroscopicTime_gt_iff_count init s (u + N) (by omega) ω).1 hb⟩
    exact (measure_mono hsub).trans
      (sharp_activation_prefix_tail init C u hn hlo hCn (A u) (hprefix u) hstart)
  calc
    law init (E ∩ lateMacroscopicFromSmall init s C N) ≤
        law init (⋃ u, A u ∩ B u) := measure_mono hcover
    _ ≤ ∑' u, law init (A u ∩ B u) := measure_iUnion_le _
    _ ≤ ∑' u, ENNReal.ofReal (1 / (C : ℝ) ^ 100) * law init (A u) :=
      ENNReal.tsum_le_tsum hlocal
    _ = ENNReal.ofReal (1 / (C : ℝ) ^ 100) * ∑' u, law init (A u) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal (1 / (C : ℝ) ^ 100) * law init E :=
      mul_le_mul_left' hmass _

theorem sharp_activation_completion_prefix_tail (init : Cfg L K) (s C : ℕ)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ init.card)
    (hlo : (6 / 25 : ℝ) * (init.card : ℝ) ≤ (C : ℝ)) (hCn : C ≤ init.card)
    (E : Set (Ω L K)) (hE : MeasurableSet[pairLogFiltration L K s] E)
    (hseed : E ⊆ hasActiveAt init s) :
    law init (E ∩ sharpActivationFailure init s C) ≤
      ENNReal.ofReal (1 / (C : ℝ) ^ 100) * law init E := by
  have hd := activation_calibration_data hn hlo hCn
  have hm := hd.population_large
  have hsmall := hd.small_le_macro.trans hd.macro_le_population
  have hnull := smallActivationTime_infinite_prefix_null init (by omega) s C
    hsmall E hE hseed
  unfold sharpActivationFailure
  rw [Set.inter_union_distrib_left]
  apply (measure_union_le _ _).trans
  rw [hnull, zero_add]
  exact sharp_small_to_macroscopic_prefix_tail init s C hn hlo hCn E hE

variable {n : ℕ}

def seedClockCountPrefix (init : InputCfg n) (s C : ℕ) : Set (InputLog n) :=
  seedPrefix init s ∩ {ω | clockCount (labelsAt init ω s) = C}

theorem seed_clockCount_measurable (init : InputCfg n) (s C : ℕ) :
    MeasurableSet[pairLogFiltration _ _ s]
      {ω | clockCount (labelsAt init ω s) = C} :=
  (show MeasurableSet {f : Fin init.card →
      AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 | clockCount f = C} from
    (Set.to_countable _).measurableSet).preimage
      ((measurable_prefixLabels init s).comp (measurable_pairLog_prefix _ _ s))

theorem seedClockCountPrefix_measurable (init : InputCfg n) (s C : ℕ) :
    MeasurableSet[pairLogFiltration _ _ s] (seedClockCountPrefix init s C) :=
  (seedPrefix_measurable init s).inter (seed_clockCount_measurable init s C)

theorem seed_clock_calibration_inputs (init : InputCfg n)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (ω : InputLog n) (s C : ℕ) (hseed : ω ∈ seedPrefix init s)
    (hcount : clockCount (labelsAt init ω s) = C) :
    PhaseThreeModel.Numeric.populationThreshold ≤ init.card ∧
      (6 / 25 : ℝ) * (init.card : ℝ) ≤ (C : ℝ) ∧ C ≤ init.card := by
  have hcard := seedPrefix_card_eq init ω s hseed
  have hdensity := clock_density_at_seedPrefix init ω s hseed
  rw [hcount] at hdensity
  have hdensityR : (6 : ℝ) * (init.card : ℝ) ≤ 25 * (C : ℝ) := by
    exact_mod_cast hdensity
  have hC := clockCount_le_card (labelsAt init ω s)
  rw [hcount] at hC
  exact ⟨by simpa only [hcard] using hn, by linarith, hC⟩

theorem seed_sharp_activation_prefix_tail (init : InputCfg n)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) (s C : ℕ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedClockCountPrefix init s C) :
    law init (E ∩ sharpActivationFailure init s C) ≤
      ENNReal.ofReal (1 / (C : ℝ) ^ 100) * law init E := by
  by_cases he : E = ∅
  · simp only [he, Set.empty_inter, measure_empty, mul_zero, le_refl]
  · obtain ⟨ω, hω⟩ := Set.nonempty_iff_ne_empty.mpr he
    have hs := hseed hω
    obtain ⟨hm, hlo, hCn⟩ :=
      seed_clock_calibration_inputs init hn ω s C hs.1 hs.2
    exact sharp_activation_completion_prefix_tail init s C hm hlo hCn E hE
      (fun η hη => positive_activation_at_seedPrefix init η s (hseed hη).1)

theorem seed_sharp_activation_half_horizon_tail (init : InputCfg n)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) (s C : ℕ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedClockCountPrefix init s C) :
    law init (E ∩ ({ω | smallActivationTime init s C ω = ⊤} ∪
      lateMacroscopicFromSmall init s C (PhaseThreeModel.Numeric.activationHalfHorizon n))) ≤
      ENNReal.ofReal (1 / (C : ℝ) ^ 100) * law init E := by
  by_cases he : E = ∅
  · simp only [he, Set.empty_inter, measure_empty, mul_zero, le_refl]
  · obtain ⟨ω, hω⟩ := Set.nonempty_iff_ne_empty.mpr he
    have hcard := seedPrefix_card_eq init ω s (hseed hω).1
    have hN := congrArg PhaseThreeModel.Numeric.activationHalfHorizon hcard
    simpa only [sharpActivationFailure, hN] using
      seed_sharp_activation_prefix_tail init hn s C E hE hseed

theorem seed_sharp_activation_count_fibre_tail (init : InputCfg n)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) (s C : ℕ) :
    law init (seedClockCountPrefix init s C ∩ sharpActivationFailure init s C) ≤
      ENNReal.ofReal (1 / (C : ℝ) ^ 100) * law init (seedClockCountPrefix init s C) :=
  seed_sharp_activation_prefix_tail init hn s C (seedClockCountPrefix init s C)
    (seedClockCountPrefix_measurable init s C) (fun _ h => h)

def seedCountActivationFailure (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  {ω | ω ∈ sharpActivationFailure init s (clockCount (labelsAt init ω s))}

theorem seed_variable_clock_activation_tail (init : InputCfg n)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) (s : ℕ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ seedCountActivationFailure init s) ≤
      ∑' C : ℕ, ENNReal.ofReal (1 / (C : ℝ) ^ 100) *
        law init (E ∩ {ω | clockCount (labelsAt init ω s) = C}) := by
  let A : ℕ → Set (InputLog n) :=
    fun C => E ∩ {ω | clockCount (labelsAt init ω s) = C}
  have hA (C : ℕ) : MeasurableSet[pairLogFiltration _ _ s] (A C) :=
    hE.inter (seed_clockCount_measurable init s C)
  have hlocal (C : ℕ) :
      law init (A C ∩ sharpActivationFailure init s C) ≤
        ENNReal.ofReal (1 / (C : ℝ) ^ 100) * law init (A C) :=
    seed_sharp_activation_prefix_tail init hn s C (A C) (hA C)
      (fun ω hω => ⟨hseed hω.1, hω.2⟩)
  have hcover : E ∩ seedCountActivationFailure init s ⊆
      ⋃ C : ℕ, A C ∩ sharpActivationFailure init s C := by
    rintro ω ⟨hω, hb⟩
    exact Set.mem_iUnion.mpr ⟨clockCount (labelsAt init ω s), ⟨hω, rfl⟩, hb⟩
  exact (measure_mono hcover).trans
    ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hlocal))

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockSharpActivationSeed

end
