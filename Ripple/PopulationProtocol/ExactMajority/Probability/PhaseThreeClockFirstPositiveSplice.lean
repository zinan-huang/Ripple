-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockFirstPositiveSplice.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockFirstPositive
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockActivationSeed
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockSeedTails

/-!
# First-positive fronts on observed masks and passage fibres

The Clock labels may be random. They are partitioned by the mask observed
at the starting time, so no union-bound factor for the number of masks is
lost. The final splice allows a genuine observed passage time and retains
the probability of its prefix event.

The seed corollary observes homogeneous Phase 3 at a later time u. It does
not assert or condition on successful activation at a future time.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockFirstPositiveSplice

open TimeTheorem PairLog PhaseThreeClockProducer PhaseThreeClockSeedTails
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockFirstPositive
  PhaseThreeClockActivationLaw PhaseThreeClockActivationSeed

variable {L : ℕ}

/-- The current state supplies the two Clock-density facts used by the
logarithmic first-positive estimate. -/
def DenseHomogeneousStart (init : Cfg L 256) (ω : Ω L 256) (u : ℕ) : Prop :=
  HomogeneousStart init ω u ∧
    2 ≤ clockCount (virtualLabels init ω u) ∧
    6 * init.card ≤ 25 * clockCount (virtualLabels init ω u)

theorem denseHomogeneousStart_measurable (init : Cfg L 256) (u : ℕ) :
    MeasurableSet[pairLogFiltration L 256 u]
      {ω | DenseHomogeneousStart init ω u} := by
  exact (show MeasurableSet {f : Fin init.card → AgentState L 256 |
      ((∀ i, (f i).phase.val = 3) ∧
        ∀ i, nonMainCarrierSmallBiasZeroAgent (f i)) ∧
      2 ≤ clockCount f ∧ 6 * init.card ≤ 25 * clockCount f} from
    (Set.to_countable _).measurableSet).preimage
      (measurable_virtualLabels init u)

/-- A random physical Clock mask is observed and summed out exactly.
The coefficient remains m^(-10), with the original prefix probability. -/
theorem first_positive_dense_prefix_tail (init : Cfg L 256)
    (hc : 2 ≤ init.card) (u : ℕ)
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 u] E)
    (hstart : ∀ ω ∈ E, DenseHomogeneousStart init ω u) :
    law init (E ∩ {ω | (firstPositiveHorizon init.card : WithTop ℕ) <
      firstPositiveTime init u ω}) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 10) * law init E := by
  classical
  let A : Finset (Fin init.card) → Set (Ω L 256) :=
    fun C => E ∩ {ω | clockSet (virtualLabels init ω u) = C}
  let B : Set (Ω L 256) :=
    {ω | (firstPositiveHorizon init.card : WithTop ℕ) < firstPositiveTime init u ω}
  have hAm (C : Finset (Fin init.card)) :
      MeasurableSet[pairLogFiltration L 256 u] (A C) := by
    exact hE.inter ((show MeasurableSet {f : Fin init.card → AgentState L 256 |
        clockSet f = C} from (Set.to_countable _).measurableSet).preimage
          (measurable_virtualLabels init u))
  have hdisj : Pairwise (fun C D => Disjoint (A C) (A D)) := by
    intro C D hCD
    apply Set.disjoint_left.mpr
    rintro ω ⟨-, hC⟩ ⟨-, hD⟩
    exact hCD (hC.symm.trans hD)
  have hunion : (⋃ C, A C) = E := by
    ext ω
    constructor
    · intro hω
      obtain ⟨C, hC⟩ := Set.mem_iUnion.mp hω
      exact hC.1
    · intro hω
      exact Set.mem_iUnion.mpr ⟨clockSet (virtualLabels init ω u), hω, rfl⟩
  have hcover : E ∩ B ⊆ ⋃ C, A C ∩ B := by
    rintro ω ⟨hω, hb⟩
    exact Set.mem_iUnion.mpr ⟨clockSet (virtualLabels init ω u), ⟨hω, rfl⟩, hb⟩
  have hlocal (C : Finset (Fin init.card)) :
      law init (A C ∩ B) ≤ ENNReal.ofReal (1 / (init.card : ℝ) ^ 10) *
        law init (A C) := by
    by_cases hne : (A C).Nonempty
    · obtain ⟨ω, hω⟩ := hne
      have hCeq : clockSet (virtualLabels init ω u) = C := hω.2
      have hC : 2 ≤ C.card := by
        simpa only [clockCount, hCeq] using (hstart ω hω.1).2.1
      have hdensity : 6 * init.card ≤ 25 * C.card := by
        simpa only [clockCount, hCeq] using (hstart ω hω.1).2.2
      exact first_positive_passage_horizon_prefix_tail init hc C hC hdensity u
        (A C) (hAm C) (fun ω hω => (hstart ω hω.1).1) (fun _ hω => hω.2)
    · have hempty : A C = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      simp only [hempty, Set.empty_inter, measure_empty, mul_zero, le_refl]
  calc
    law init (E ∩ B) ≤ law init (⋃ C, A C ∩ B) := measure_mono hcover
    _ ≤ ∑' C, law init (A C ∩ B) := measure_iUnion_le _
    _ ≤ ∑' C, ENNReal.ofReal (1 / (init.card : ℝ) ^ 10) * law init (A C) :=
      ENNReal.tsum_le_tsum hlocal
    _ = ENNReal.ofReal (1 / (init.card : ℝ) ^ 10) * ∑' C, law init (A C) := by
      rw [ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal (1 / (init.card : ℝ) ^ 10) * law init E := by
      rw [← measure_iUnion hdisj
        (fun C => ((pairLogFiltration L 256).le u) _ (hAm C)), hunion]

/-- First-positive failure started at a finite observed passage. The event
does not assert that the passage exists on every sample path. -/
def passageFirstPositiveFailure (init : Cfg L 256)
    (T : Ω L 256 → WithTop ℕ) : Set (Ω L 256) :=
  {ω | ∃ u : ℕ, T ω = (u : WithTop ℕ) ∧
    (firstPositiveHorizon init.card : WithTop ℕ) < firstPositiveTime init u ω}

/-- The failure on each passage fibre is observable at its own deadline. -/
theorem passage_failure_fibre_measurable (init : Cfg L 256)
    (T : Ω L 256 → WithTop ℕ) (E : Set (Ω L 256)) (u : ℕ)
    (hprefix : MeasurableSet[pairLogFiltration L 256 u]
      (E ∩ {ω | T ω = (u : WithTop ℕ)})) :
    MeasurableSet[pairLogFiltration L 256 (u + firstPositiveHorizon init.card)]
      ((E ∩ {ω | T ω = (u : WithTop ℕ)}) ∩
        {ω | (firstPositiveHorizon init.card : WithTop ℕ) <
          firstPositiveTime init u ω}) :=
  first_positive_failure_measurable init u (firstPositiveHorizon init.card) _ hprefix

/-- Splice over genuine observed passage fibres. Each local estimate is
under law init and keeps the observed prefix probability; summing fibres
preserves that factor and never conditions on future success. -/
theorem first_positive_observed_passage_tail (init : Cfg L 256)
    (hc : 2 ≤ init.card) (T : Ω L 256 → WithTop ℕ)
    (E : Set (Ω L 256))
    (hprefix : ∀ u : ℕ, MeasurableSet[pairLogFiltration L 256 u]
      (E ∩ {ω | T ω = (u : WithTop ℕ)}))
    (hstart : ∀ u : ℕ, ∀ ω ∈ E, T ω = (u : WithTop ℕ) →
      DenseHomogeneousStart init ω u) :
    law init (E ∩ passageFirstPositiveFailure init T) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 10) * law init E := by
  let A : ℕ → Set (Ω L 256) :=
    fun u => E ∩ {ω | T ω = (u : WithTop ℕ)}
  let B : ℕ → Set (Ω L 256) :=
    fun u => {ω | (firstPositiveHorizon init.card : WithTop ℕ) <
      firstPositiveTime init u ω}
  have hdisj : Pairwise (fun u v => Disjoint (A u) (A v)) := by
    intro u v huv
    apply Set.disjoint_left.mpr
    rintro ω ⟨-, hu⟩ ⟨-, hv⟩
    exact huv (WithTop.coe_injective (hu.symm.trans hv))
  have hcover : E ∩ passageFirstPositiveFailure init T ⊆ ⋃ u, A u ∩ B u := by
    rintro ω ⟨hω, u, hu, hb⟩
    exact Set.mem_iUnion.mpr ⟨u, ⟨hω, hu⟩, hb⟩
  have hmass : (∑' u, law init (A u)) ≤ law init E := by
    rw [← measure_iUnion hdisj
      (fun u => ((pairLogFiltration L 256).le u) _ (hprefix u))]
    apply measure_mono
    intro ω hω
    obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hω
    exact hu.1
  have hlocal (u : ℕ) :
      law init (A u ∩ B u) ≤ ENNReal.ofReal (1 / (init.card : ℝ) ^ 10) *
        law init (A u) :=
    first_positive_dense_prefix_tail init hc u (A u) (hprefix u)
      (fun ω hω => hstart u ω hω.1 hω.2)
  calc
    law init (E ∩ passageFirstPositiveFailure init T) ≤
        law init (⋃ u, A u ∩ B u) := measure_mono hcover
    _ ≤ ∑' u, law init (A u ∩ B u) := measure_iUnion_le _
    _ ≤ ∑' u, ENNReal.ofReal (1 / (init.card : ℝ) ^ 10) * law init (A u) :=
      ENNReal.tsum_le_tsum hlocal
    _ = ENNReal.ofReal (1 / (init.card : ℝ) ^ 10) * ∑' u, law init (A u) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal (1 / (init.card : ℝ) ^ 10) * law init E :=
      mul_le_mul_left' hmass _

variable {n : ℕ}

/-- A first-seed prefix followed by a state observation at u. The two
times are deliberately separate: fresh seed Clocks can all have minute zero. -/
def seedHomogeneousPrefix (init : InputCfg n) (s u : ℕ) : Set (InputLog n) :=
  seedPrefix init s ∩ {ω | DenseHomogeneousStart init ω u}

theorem seedHomogeneousPrefix_measurable (init : InputCfg n)
    (s u : ℕ) (hsu : s ≤ u) :
    MeasurableSet[pairLogFiltration _ _ u] (seedHomogeneousPrefix init s u) :=
  (((pairLogFiltration _ _).mono hsu) _ (seedPrefix_measurable init s)).inter
    (denseHomogeneousStart_measurable init u)

theorem seed_first_positive_prefix_tail (init : InputCfg n)
    (hc : 2 ≤ init.card) (s u : ℕ) (hsu : s ≤ u) :
    law init (seedHomogeneousPrefix init s u ∩
      {ω | (firstPositiveHorizon init.card : WithTop ℕ) < firstPositiveTime init u ω}) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 10) *
        law init (seedHomogeneousPrefix init s u) :=
  first_positive_dense_prefix_tail init hc u (seedHomogeneousPrefix init s u)
    (seedHomogeneousPrefix_measurable init s u hsu) (fun _ hω => hω.2)

theorem seed_first_positive_fibre_tail (init : InputCfg n)
    (hc : 2 ≤ init.card) (s u : ℕ) (hsu : s ≤ u) :
    law init (seedHomogeneousPrefix init s u ∩
      {ω | (firstPositiveHorizon init.card : WithTop ℕ) < firstPositiveTime init u ω}) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 10) *
        law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply (seed_first_positive_prefix_tail init hc s u hsu).trans
  exact mul_le_mul_left' (measure_mono
    (show seedHomogeneousPrefix init s u ⊆
      {ω | seedTime init 3 ω = (s : WithTop ℕ)} from fun _ hω => hω.1.1)) _


/-- An observed complete activation endpoint, with the current phase cap.
The cap is tested at u; it is not a future no-backup condition. -/
def seedActivationEndpoint (init : InputCfg n) (s u : ℕ) : Set (InputLog n) :=
  seedPrefix init s ∩
    {ω | PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u) = init.card ∧
      ∀ i, (virtualLabels init ω u i).phase.val ≤ 3}

theorem seedActivationEndpoint_measurable (init : InputCfg n)
    (s u : ℕ) (hsu : s ≤ u) :
    MeasurableSet[pairLogFiltration _ _ u] (seedActivationEndpoint init s u) := by
  have hstate : MeasurableSet[pairLogFiltration _ _ u]
      {ω | PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u) = init.card ∧
        ∀ i, (virtualLabels init ω u i).phase.val ≤ 3} :=
    (show MeasurableSet {f : Fin init.card →
        AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 |
          PhaseThreeClockActivationLaw.activeCount f = init.card ∧ ∀ i, (f i).phase.val ≤ 3} from
      (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init u)
  exact (((pairLogFiltration _ _).mono hsu) _ (seedPrefix_measurable init s)).inter hstate

theorem seed_activated_first_positive_prefix_tail (init : InputCfg n)
    (hn : 9 ≤ n) (hc : 2 ≤ init.card) (s u : ℕ) (hsu : s ≤ u) :
    law init (seedActivationEndpoint init s u ∩
      {ω | (firstPositiveHorizon init.card : WithTop ℕ) < firstPositiveTime init u ω}) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 10) *
        law init (seedActivationEndpoint init s u) := by
  apply first_positive_dense_prefix_tail init hc u (seedActivationEndpoint init s u)
    (seedActivationEndpoint_measurable init s u hsu)
  intro ω hω
  exact dense_start_data_of_seedPrefix_full_activation init hn ω s u hω.1 hsu
    hω.2.1 hω.2.2

theorem seed_activated_first_positive_fibre_tail (init : InputCfg n)
    (hn : 9 ≤ n) (hc : 2 ≤ init.card) (s u : ℕ) (hsu : s ≤ u) :
    law init (seedActivationEndpoint init s u ∩
      {ω | (firstPositiveHorizon init.card : WithTop ℕ) < firstPositiveTime init u ω}) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 10) *
        law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply (seed_activated_first_positive_prefix_tail init hn hc s u hsu).trans
  exact mul_le_mul_left' (measure_mono
    (show seedActivationEndpoint init s u ⊆
      {ω | seedTime init 3 ω = (s : WithTop ℕ)} from fun _ hω => hω.1.1)) _

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockFirstPositiveSplice

end
