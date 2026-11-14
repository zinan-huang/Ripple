-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockEarlyMarkSeedTail.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockEarlyMarkPrefixTail

noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockEarlyMarkSeedTail

open TimeTheorem PairLog PhaseThreeClockVirtual PhaseThreeClockGatedLaw
  PhaseThreeClockSeedTails PhaseThreeClockSmallActivation PhaseThreeClockSharpActivationSeed
  PhaseThreeClockMarkedClockRates PhaseThreeClockMarkedProcess
  PhaseThreeClockEarlyMarkPrefixTail PhaseThreeClockEarlyMarks

variable {n : ℕ}

def phaseCapAt (init : InputCfg n) (t : ℕ) : Set (InputLog n) :=
  {ω | ∀ i, (virtualLabels init ω t i).phase.val ≤ 3}

theorem phaseCapAt_measurable (init : InputCfg n) (t : ℕ) :
    MeasurableSet[pairLogFiltration _ _ t] (phaseCapAt init t) :=
  (show MeasurableSet {f : Fin init.card → AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 |
    ∀ i, (f i).phase.val ≤ 3} from (Set.to_countable _).measurableSet).preimage
      (measurable_virtualLabels init t)

def observedMarkFailure (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ s : ℕ) : Set (InputLog n) :=
  {ω | ∃ u : ℕ, smallActivationTime init s C.card ω = (u : WithTop ℕ) ∧
    ω ∈ calibratedMarkFailure init C ℓ s u}

theorem seed_marked_prefix_tail (init : InputCfg n)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (C : Finset (Fin init.card)) (ℓ s : ℕ) (hℓ : 1 ≤ ℓ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : ∀ ω ∈ E, ω ∈ seedPrefix init s ∧ C = clockSet (labelsAt init ω s)) :
    law init (E ∩ observedMarkFailure init C ℓ s) ≤
      ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init E := by
  classical
  by_cases he : E = ∅
  · simp only [he, Set.empty_inter, measure_empty, mul_zero, le_refl]
  obtain ⟨η, hη⟩ := Set.nonempty_iff_ne_empty.mpr he
  have hsη := hseed η hη
  have hcount : clockCount (labelsAt init η s) = C.card := by
    change (clockSet (labelsAt init η s)).card = C.card
    rw [← hsη.2]
  obtain ⟨hm, hlo, hCn⟩ := seed_clock_calibration_inputs init hn η s C.card hsη.1 hcount
  have hupper := clock_upper_from_seedPrefix init η C s hsη.1 hsη.2
  let A : ℕ → Set (InputLog n) := fun u =>
    (E ∩ {ω | smallActivationTime init s C.card ω = (u : WithTop ℕ)}) ∩ phaseCapAt init u
  have hA (u : ℕ) : MeasurableSet[pairLogFiltration _ _ u] (A u) :=
    (smallActivation_prefix_fibre_measurable init s C.card u E hE).inter
      (phaseCapAt_measurable init u)
  have hdisj : Pairwise (fun u v => Disjoint (A u) (A v)) := by
    intro u v huv
    apply Set.disjoint_left.mpr
    rintro ω ⟨⟨-, hu⟩, -⟩ ⟨⟨-, hv⟩, -⟩
    exact huv (WithTop.coe_injective (hu.symm.trans hv))
  have hmass : (∑' u, law init (A u)) ≤ law init E := by
    rw [← measure_iUnion hdisj (fun u => ((pairLogFiltration _ _).le u) _ (hA u))]
    apply measure_mono
    intro ω hω
    obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hω
    exact hu.1.1
  have hlocal (u : ℕ) :
      law init (A u ∩ calibratedMarkFailure init C ℓ s u) ≤
        ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init (A u) := by
    by_cases hau : A u = ∅
    · simp only [hau, Set.empty_inter, measure_empty, mul_zero, le_refl]
    obtain ⟨ω, hω⟩ := Set.nonempty_iff_ne_empty.mpr hau
    have hsu := (smallActivationTime_finite_state init s C.card u ω hω.1.2).1
    apply calibrated_mark_prefix_tail init C ℓ s u hℓ hsu hm hlo hCn hupper (A u) (hA u)
    · intro ξ hξ
      exact hseed ξ hξ.1.1
    · intro ξ hξ
      exact markedAt_card_at_smallActivation_le_order init hn ξ C ℓ
        (PhaseThreeModel.Numeric.earlyCutoff C.card) s u
        (hseed ξ hξ.1.1).1 hℓ (hseed ξ hξ.1.1).2 hξ.2 hξ.1.2
  have hcover : E ∩ observedMarkFailure init C ℓ s ⊆
      ⋃ u, A u ∩ calibratedMarkFailure init C ℓ s u := by
    rintro ω ⟨hEω, u, hu, t, hcap, hD, hmark⟩
    have hcapu : ω ∈ phaseCapAt init u := fun i =>
      (PhaseThreeClockActivationLaw.virtualLabels_phase_mono init ω i
        (by omega : u ≤ u + t)).trans (hcap i)
    exact Set.mem_iUnion.mpr ⟨u, ⟨⟨hEω, hu⟩, hcapu⟩, t, hcap, hD, hmark⟩
  calc
    law init (E ∩ observedMarkFailure init C ℓ s) ≤
        law init (⋃ u, A u ∩ calibratedMarkFailure init C ℓ s u) := measure_mono hcover
    _ ≤ ∑' u, law init (A u ∩ calibratedMarkFailure init C ℓ s u) := measure_iUnion_le _
    _ ≤ ∑' u, ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init (A u) :=
      ENNReal.tsum_le_tsum hlocal
    _ = ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * ∑' u, law init (A u) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ _ := mul_le_mul_left' hmass _

def fullMarkFailure (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ s : ℕ) : Set (InputLog n) :=
  {ω | ∃ v, s ≤ v ∧ (∀ i, (virtualLabels init ω v i).phase.val ≤ 3) ∧
    (C.card : ℝ) ^ (1 / 3 : ℝ) <
      ((markedAt init C ℓ (PhaseThreeModel.Numeric.earlyCutoff C.card) s ω v).card : ℝ) ∧
    ((v : WithTop ℕ) ≤ smallActivationTime init s C.card ω ∨
      ∃ u : ℕ, smallActivationTime init s C.card ω = (u : WithTop ℕ) ∧ u ≤ v ∧
        PhaseThreeClockMarkedWindow.laterClockCount init C s ℓ u
          (PhaseThreeModel.Numeric.activationHalfHorizon init.card) (v - u) ω ≤
            (PhaseThreeModel.Numeric.fineTicks C.card : ℝ))}

theorem seed_full_mark_prefix_tail (init : InputCfg n)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (C : Finset (Fin init.card)) (ℓ s : ℕ) (hℓ : 1 ≤ ℓ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : ∀ ω ∈ E, ω ∈ seedPrefix init s ∧ C = clockSet (labelsAt init ω s)) :
    law init (E ∩ fullMarkFailure init C ℓ s) ≤
      ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init E := by
  apply (measure_mono ?_).trans (seed_marked_prefix_tail init hn C ℓ s hℓ E hE hseed)
  rintro ω ⟨he, v, hsv, hcap, hmark, hwindow⟩
  refine ⟨he, ?_⟩
  rcases hwindow with hbefore | ⟨u, hu, huv, hD⟩
  · have hsmall := marks_below_threshold_before_small init hn ω C ℓ
      (PhaseThreeModel.Numeric.earlyCutoff C.card) s v
      (hseed ω he).1 hsv hℓ (hseed ω he).2 hcap hbefore
    exact False.elim (lt_asymm hmark hsmall.2)
  · have hv : u + (v - u) = v := by omega
    refine ⟨u, hu, v - u, ?_, hD, ?_⟩
    · simpa only [hv] using hcap
    · simpa only [markedMass, hv] using hmark

theorem seed_clockMask_measurable (init : InputCfg n) (s : ℕ)
    (C : Finset (Fin init.card)) :
    MeasurableSet[pairLogFiltration _ _ s] {ω | C = clockSet (labelsAt init ω s)} :=
  (show MeasurableSet {f : Fin init.card → AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 |
    C = clockSet f} from (Set.to_countable _).measurableSet).preimage
      ((measurable_prefixLabels init s).comp (measurable_pairLog_prefix _ _ s))

def seedClockMaskPrefix (init : InputCfg n) (s : ℕ) (C : Finset (Fin init.card)) :
    Set (InputLog n) :=
  seedPrefix init s ∩ {ω | C = clockSet (labelsAt init ω s)}

theorem seed_marked_mask_fibre_tail (init : InputCfg n)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (C : Finset (Fin init.card)) (ℓ s : ℕ) (hℓ : 1 ≤ ℓ) :
    law init (seedClockMaskPrefix init s C ∩ fullMarkFailure init C ℓ s) ≤
      ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init (seedClockMaskPrefix init s C) :=
  seed_full_mark_prefix_tail init hn C ℓ s hℓ (seedClockMaskPrefix init s C)
    ((seedPrefix_measurable init s).inter (seed_clockMask_measurable init s C))
    (fun _ h => h)

def seedMarkedFailure (init : InputCfg n) (ℓ s : ℕ) : Set (InputLog n) :=
  {ω | ω ∈ fullMarkFailure init (clockSet (labelsAt init ω s)) ℓ s}

/-- Unfolding `seedMarkedFailure` by a rewrite (the kernel times out on the direct defeq). -/
theorem mem_seedMarkedFailure_iff (init : InputCfg n) (ℓ s : ℕ) (ω : InputLog n) :
    ω ∈ seedMarkedFailure init ℓ s ↔
      ω ∈ fullMarkFailure init (clockSet (labelsAt init ω s)) ℓ s := by
  have hdef : seedMarkedFailure init ℓ s =
      {ω | ω ∈ fullMarkFailure init (clockSet (labelsAt init ω s)) ℓ s} := rfl
  rw [hdef, Set.mem_setOf_eq]

theorem seed_variable_mask_mark_tail (init : InputCfg n)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) (ℓ s : ℕ) (hℓ : 1 ≤ ℓ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ seedMarkedFailure init ℓ s) ≤
      ∑' C : Finset (Fin init.card), ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) *
        law init (E ∩ {ω | C = clockSet (labelsAt init ω s)}) := by
  let A : Finset (Fin init.card) → Set (InputLog n) := fun C =>
    E ∩ {ω | C = clockSet (labelsAt init ω s)}
  have hlocal (C : Finset (Fin init.card)) :
      law init (A C ∩ fullMarkFailure init C ℓ s) ≤
        ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init (A C) :=
    seed_full_mark_prefix_tail init hn C ℓ s hℓ (A C)
      (hE.inter (seed_clockMask_measurable init s C)) (fun ω hω => ⟨hseed hω.1, hω.2⟩)
  have hcover : E ∩ seedMarkedFailure init ℓ s ⊆
      ⋃ C : Finset (Fin init.card), A C ∩ fullMarkFailure init C ℓ s := by
    rintro ω ⟨he, hb⟩
    obtain ⟨C0, hC0⟩ : ∃ C0 : Finset (Fin init.card), C0 = clockSet (labelsAt init ω s) :=
      ⟨_, rfl⟩
    have hb' : ω ∈ fullMarkFailure init (clockSet (labelsAt init ω s)) ℓ s :=
      (mem_seedMarkedFailure_iff init ℓ s ω).1 hb
    rw [← hC0] at hb'
    exact Set.mem_iUnion.mpr ⟨C0, ⟨he, hC0⟩, hb'⟩
  exact (measure_mono hcover).trans
    ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hlocal))

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockEarlyMarkSeedTail

end
