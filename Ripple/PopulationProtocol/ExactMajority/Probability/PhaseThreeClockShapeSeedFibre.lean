-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockShapeSeedFibre.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockShapeObservedTail

/-!
# Removing the observed Clock-mask parameter without a mask-count factor

The physical mask is measured at the genuine seed.  The mask fibres are
disjoint, so the original prefix mass is retained when they are summed.
The final AsyncEntry restriction is imposed by set inclusion after the
prefix estimate; it is never used as a conditioning event.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockShapeSeedFibre

open TimeTheorem PairLog PhaseThreeClockProducer PhaseThreeClockGatedLaw
  PhaseThreeClockActivationSeed PhaseThreeClockSeedTails
  PhaseThreeClockSharpActivationSeed PhaseThreeClockEarlyMarkCalibration
  PhaseThreeClockEarlyMarkSeedTail PhaseThreeClockMarkedShape
  PhaseThreeClockShapeObservedTail

variable {n : ℕ}

theorem negative_ninety_nine_rpow_eq (n : ℕ) :
    (n : ℝ) ^ (-99 : ℝ) = 1 / (n : ℝ) ^ 99 := by
  calc
    (n : ℝ) ^ (-99 : ℝ) = ((n : ℝ) ^ (99 : ℝ))⁻¹ :=
      Real.rpow_neg (Nat.cast_nonneg n) 99
    _ = _ := by first | rw [Real.rpow_ofNat, one_div] | simp [one_div]

theorem seed_clock_error_population (init : InputCfg n)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (ω : InputLog n) (s : ℕ) (C : Finset (Fin init.card))
    (hseed : ω ∈ seedPrefix init s) (hmask : C = clockSet (labelsAt init ω s)) :
    1 / (C.card : ℝ) ^ 100 ≤ 1 / (n : ℝ) ^ 99 := by
  have hcount : clockCount (labelsAt init ω s) = C.card := by
    change (clockSet (labelsAt init ω s)).card = C.card
    rw [← hmask]
  obtain ⟨hm, hlo, hCn⟩ :=
    seed_clock_calibration_inputs init hn ω s C.card hseed hcount
  obtain ⟨hC, hx, -, hlog, -⟩ :=
    PhaseThreeModel.Numeric.logarithmic_inputs hm hlo hCn
  have hcard := seedPrefix_card_eq init ω s hseed
  have hnpos : 0 < (n : ℝ) := by
    have hcR : (C.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hCn.trans hcard.le
    exact hC.trans_le hcR
  have hlogn : Real.log (n : ℝ) ≤ Real.log (C.card : ℝ) + 2 := by
    simpa only [hcard] using hlog
  calc
    1 / (C.card : ℝ) ^ 100 = (C.card : ℝ) ^ (-100 : ℝ) :=
      (negative_hundred_rpow_eq C.card).symm
    _ = Real.exp (Real.log (C.card : ℝ) * (-100)) :=
      Real.rpow_def_of_pos hC _
    _ ≤ Real.exp (Real.log (n : ℝ) * (-99)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = (n : ℝ) ^ (-99 : ℝ) := (Real.rpow_def_of_pos hnpos _).symm
    _ = _ := negative_ninety_nine_rpow_eq n

theorem seed_mask_prefix_union (init : InputCfg n) (s : ℕ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (B : Finset (Fin init.card) → Set (InputLog n)) (ε : ℝ≥0∞)
    (hlocal : ∀ C : Finset (Fin init.card),
      law init ((E ∩ {ω | C = clockSet (labelsAt init ω s)}) ∩ B C) ≤
        ε * law init (E ∩ {ω | C = clockSet (labelsAt init ω s)})) :
    law init (E ∩ {ω | ω ∈ B (clockSet (labelsAt init ω s))}) ≤
      ε * law init E := by
  let A : Finset (Fin init.card) → Set (InputLog n) :=
    fun C => E ∩ {ω | C = clockSet (labelsAt init ω s)}
  have hA (C : Finset (Fin init.card)) :
      MeasurableSet[pairLogFiltration _ _ s] (A C) :=
    hE.inter (seed_clockMask_measurable init s C)
  have hdisj : Pairwise (fun C D => Disjoint (A C) (A D)) := by
    intro C D hCD
    apply Set.disjoint_left.mpr
    intro ω hC hD
    exact hCD (hC.2.trans hD.2.symm)
  have hmass : (∑' C : Finset (Fin init.card), law init (A C)) ≤ law init E := by
    rw [← measure_iUnion hdisj (fun C => ((pairLogFiltration _ _).le s) _ (hA C))]
    apply measure_mono
    intro ω hω
    obtain ⟨C, hC⟩ := Set.mem_iUnion.mp hω
    exact hC.1
  have hcover : E ∩ {ω | ω ∈ B (clockSet (labelsAt init ω s))} ⊆
      ⋃ C : Finset (Fin init.card), A C ∩ B C := by
    rintro ω ⟨he, hb⟩
    exact Set.mem_iUnion.mpr ⟨clockSet (labelsAt init ω s), ⟨he, rfl⟩, hb⟩
  calc
    law init (E ∩ {ω | ω ∈ B (clockSet (labelsAt init ω s))}) ≤
        law init (⋃ C : Finset (Fin init.card), A C ∩ B C) := measure_mono hcover
    _ ≤ ∑' C : Finset (Fin init.card), law init (A C ∩ B C) := measure_iUnion_le _
    _ ≤ ∑' C : Finset (Fin init.card), ε * law init (A C) :=
      ENNReal.tsum_le_tsum hlocal
    _ = ε * ∑' C : Finset (Fin init.card), law init (A C) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ _ := mul_le_mul_left' hmass _

def seedNormalShapeFailure (init : InputCfg n) (ell s : ℕ) : Set (InputLog n) :=
  {ω | ω ∈ normalShapeFailure init (clockSet (labelsAt init ω s)) ell s}

def seedMarkedShapeFailure (init : InputCfg n) (ell s : ℕ) : Set (InputLog n) :=
  {ω | ω ∈ markedShapeFailure init (clockSet (labelsAt init ω s)) ell s}

theorem seed_normal_shape_population_prefix_tail
    (init : InputCfg n) (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (ell s : ℕ) (hell : 1 ≤ ell)
    (hlevel : ell + 1 ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ seedNormalShapeFailure init ell s) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 99) * law init E := by
  apply seed_mask_prefix_union init s E hE
    (fun C => normalShapeFailure init C ell s) (ENNReal.ofReal (1 / (n : ℝ) ^ 99))
  intro C
  let A := E ∩ {ω | C = clockSet (labelsAt init ω s)}
  by_cases ha : A = ∅
  · simp only [show E ∩ {ω | C = clockSet (labelsAt init ω s)} = ∅ from ha,
      Set.empty_inter, measure_empty, mul_zero, le_refl]
  obtain ⟨η, hη⟩ := Set.nonempty_iff_ne_empty.mpr ha
  have hcal := seed_clock_error_population init hn η s C (hseed hη.1) hη.2
  apply (seed_normal_shape_prefix_tail init hn C ell s hell hlevel A
    (hE.inter (seed_clockMask_measurable init s C))
    (fun ω hω => ⟨hseed hω.1, hω.2⟩)).trans
  exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal hcal) _

theorem seed_marked_shape_population_prefix_tail
    (init : InputCfg n) (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (ell s : ℕ) (hell : 1 ≤ ell)
    (hlevel : ell + 1 ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ seedMarkedShapeFailure init ell s) ≤
      (2 * ENNReal.ofReal (1 / (n : ℝ) ^ 99)) * law init E := by
  apply seed_mask_prefix_union init s E hE
    (fun C => markedShapeFailure init C ell s) (2 * ENNReal.ofReal (1 / (n : ℝ) ^ 99))
  intro C
  let A := E ∩ {ω | C = clockSet (labelsAt init ω s)}
  by_cases ha : A = ∅
  · simp only [show E ∩ {ω | C = clockSet (labelsAt init ω s)} = ∅ from ha,
      Set.empty_inter, measure_empty, mul_zero, le_refl]
  obtain ⟨η, hη⟩ := Set.nonempty_iff_ne_empty.mpr ha
  have hcal := seed_clock_error_population init hn η s C (hseed hη.1) hη.2
  apply (seed_marked_shape_prefix_tail init hn C ell s hell hlevel A
    (hE.inter (seed_clockMask_measurable init s C))
    (fun ω hω => ⟨hseed hω.1, hω.2⟩)).trans
  exact mul_le_mul_right' (mul_le_mul_left' (ENNReal.ofReal_le_ofReal hcal) 2) _

theorem seed_normal_shape_population_entry_fibre_tail
    (init : InputCfg n) (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (ell s : ℕ) (hell : 1 ≤ ell)
    (hlevel : ell + 1 ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    law init {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
      StageEventSpec.SeedProfile n init (trace init ω s) ∧
      (∃ T, T ≤ earlyHorizon n ∧ StageEventSpec.AsyncEntry init ω s T) ∧
      ω ∈ seedNormalShapeFailure init ell s} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 99) *
        law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  have hsub :
      {ω : InputLog n | seedTime init 3 ω = (s : WithTop ℕ) ∧
        StageEventSpec.SeedProfile n init (trace init ω s) ∧
        (∃ T, T ≤ earlyHorizon n ∧ StageEventSpec.AsyncEntry init ω s T) ∧
        ω ∈ seedNormalShapeFailure init ell s} ⊆
      seedPrefix init s ∩ seedNormalShapeFailure init ell s := by
    rintro ω ⟨hs, hp, -, hb⟩
    exact ⟨⟨hs, hp⟩, hb⟩
  exact (measure_mono hsub).trans
    ((seed_normal_shape_population_prefix_tail init hn ell s hell hlevel
      (seedPrefix init s) (seedPrefix_measurable init s) (fun _ h => h)).trans
      (mul_le_mul_left' (measure_mono (fun _ h => h.1 :
        seedPrefix init s ⊆ {ω | seedTime init 3 ω = (s : WithTop ℕ)})) _))

theorem seed_marked_shape_population_entry_fibre_tail
    (init : InputCfg n) (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (ell s : ℕ) (hell : 1 ≤ ell)
    (hlevel : ell + 1 ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    law init {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
      StageEventSpec.SeedProfile n init (trace init ω s) ∧
      (∃ T, T ≤ earlyHorizon n ∧ StageEventSpec.AsyncEntry init ω s T) ∧
      ω ∈ seedMarkedShapeFailure init ell s} ≤
      (2 * ENNReal.ofReal (1 / (n : ℝ) ^ 99)) *
        law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  have hsub :
      {ω : InputLog n | seedTime init 3 ω = (s : WithTop ℕ) ∧
        StageEventSpec.SeedProfile n init (trace init ω s) ∧
        (∃ T, T ≤ earlyHorizon n ∧ StageEventSpec.AsyncEntry init ω s T) ∧
        ω ∈ seedMarkedShapeFailure init ell s} ⊆
      seedPrefix init s ∩ seedMarkedShapeFailure init ell s := by
    rintro ω ⟨hs, hp, -, hb⟩
    exact ⟨⟨hs, hp⟩, hb⟩
  exact (measure_mono hsub).trans
    ((seed_marked_shape_population_prefix_tail init hn ell s hell hlevel
      (seedPrefix init s) (seedPrefix_measurable init s) (fun _ h => h)).trans
      (mul_le_mul_left' (measure_mono (fun _ h => h.1 :
        seedPrefix init s ⊆ {ω | seedTime init 3 ω = (s : WithTop ℕ)})) _))

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockShapeSeedFibre

end
