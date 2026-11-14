-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockObservedPassageSplice.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockObservedPassage

/-!
# Bulk passage on observed Clock counts and observed time fibres

The physical Clock count is read from the current virtual state, then
summed out as a measurable partition. The same construction is applied
to the finite fibres of an observed time. Neither partition loses a
union-bound factor: the calibrated coefficient remains m^(-9).

EnvironmentSpan is an event through the deadline. It is intersected with
failure after the local estimate, never placed in the observed prefix.
The final null statements likewise intersect with the all-time
environment and do not assume a finite starting time on every path.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockObservedPassageSplice

open TimeTheorem PairLog PhaseThreeClockVirtual PhaseThreeClockGatedLaw
  PhaseThreeClockEmbeddingBridge PhaseThreeClockObservedPassage

variable {L : ℕ}

def DensePositiveStart (init : Cfg L 256) (ℓ : ℕ)
    (ω : Ω L 256) (s : ℕ) : Prop :=
  1 ≤ frontCount (virtualLabels init ω s) ℓ ∧
    6 * init.card ≤ 25 * clockCount (virtualLabels init ω s)

def randomCountPassageFailure (init : Cfg L 256) (ℓ s N : ℕ) : Set (Ω L 256) :=
  {ω | EnvironmentSpan init s N ω ∧
    frontCount (virtualLabels init ω (s + N)) ℓ <
      StageEventSpec.bulkThreshold (clockCount (virtualLabels init ω s))}

theorem clockCount_le_population (init : Cfg L 256) (ω : Ω L 256) (s : ℕ) :
    clockCount (virtualLabels init ω s) ≤ init.card := by
  have h := Finset.card_le_card
    (Finset.subset_univ (clockSet (virtualLabels init ω s)))
  simpa only [clockCount, Finset.card_univ, Fintype.card_fin] using h

theorem clockCount_fibre_measurable (init : Cfg L 256) (s C : ℕ) :
    MeasurableSet[pairLogFiltration L 256 s]
      {ω | clockCount (virtualLabels init ω s) = C} :=
  (show MeasurableSet {f : Fin init.card → AgentState L 256 | clockCount f = C}
      from (Set.to_countable _).measurableSet).preimage
    (measurable_virtualLabels init s)

theorem densePositiveStart_measurable (init : Cfg L 256) (ℓ s : ℕ) :
    MeasurableSet[pairLogFiltration L 256 s]
      {ω | DensePositiveStart init ℓ ω s} :=
  (show MeasurableSet {f : Fin init.card → AgentState L 256 |
      1 ≤ frontCount f ℓ ∧ 6 * init.card ≤ 25 * clockCount f}
      from (Set.to_countable _).measurableSet).preimage
    (measurable_virtualLabels init s)

theorem randomCountPassageFailure_measurable (init : Cfg L 256) (ℓ s N : ℕ) :
    MeasurableSet[pairLogFiltration L 256 (s + N)]
      (randomCountPassageFailure init ℓ s N) := by
  have heq : randomCountPassageFailure init ℓ s N =
      ⋃ C : ℕ, {ω | clockCount (virtualLabels init ω s) = C} ∩
        observedPassageFailure init ℓ C s N := by
    ext ω
    constructor
    · rintro ⟨hspan, hbelow⟩
      exact Set.mem_iUnion.mpr
        ⟨clockCount (virtualLabels init ω s), rfl, hspan, hbelow⟩
    · intro hω
      obtain ⟨C, hC, hspan, hbelow⟩ := Set.mem_iUnion.mp hω
      have hC' : clockCount (virtualLabels init ω s) = C := hC
      exact ⟨hspan, by rw [hC']; exact hbelow⟩
  rw [heq]
  refine MeasurableSet.iUnion fun C => ?_
  have hCend : MeasurableSet[pairLogFiltration L 256 (s + N)]
      {ω | clockCount (virtualLabels init ω s) = C} :=
    ((pairLogFiltration L 256).mono (by omega : s ≤ s + N)) _
      (clockCount_fibre_measurable init s C)
  exact hCend.inter (observedPassageFailure_measurable init ℓ C s N)

/-- The Clock count may be random at the observed start. Summing its
disjoint measurable fibres retains the same prefix coefficient. -/
theorem random_count_bulk_prefix_tail (init : Cfg L 256)
    (hm : 20 ≤ init.card) (ℓ s : ℕ)
    (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1))
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 s] E)
    (hstart : ∀ ω ∈ E, DensePositiveStart init ℓ ω s) :
    law init (E ∩ randomCountPassageFailure init ℓ s
      (PhaseThreeModel.Numeric.firstHitHorizon init.card)) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 9) * law init E := by
  classical
  let A : ℕ → Set (Ω L 256) :=
    fun C => E ∩ {ω | clockCount (virtualLabels init ω s) = C}
  let B := randomCountPassageFailure init ℓ s
    (PhaseThreeModel.Numeric.firstHitHorizon init.card)
  have hAm (C : ℕ) : MeasurableSet[pairLogFiltration L 256 s] (A C) :=
    hE.inter (clockCount_fibre_measurable init s C)
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
      exact Set.mem_iUnion.mpr ⟨clockCount (virtualLabels init ω s), hω, rfl⟩
  have hcover : E ∩ B ⊆ ⋃ C, A C ∩ B := by
    rintro ω ⟨hω, hb⟩
    exact Set.mem_iUnion.mpr
      ⟨clockCount (virtualLabels init ω s), ⟨hω, rfl⟩, hb⟩
  have hlocal (C : ℕ) :
      law init (A C ∩ B) ≤ ENNReal.ofReal (1 / (init.card : ℝ) ^ 9) *
        law init (A C) := by
    by_cases hne : (A C).Nonempty
    · obtain ⟨ω, hω⟩ := hne
      have hCeq : clockCount (virtualLabels init ω s) = C := hω.2
      have hC : C ≤ init.card := by
        rw [← hCeq]; exact clockCount_le_population init ω s
      have hdensity : 6 * init.card ≤ 25 * C := by
        rw [← hCeq]; exact (hstart ω hω.1).2
      apply (measure_mono ?_).trans
        (observed_bulk_passage_prefix_tail init hm C ℓ s hC hdensity hℓ hcap
          (A C) (hAm C) (fun ω hω => ⟨(hstart ω hω.1).1, hω.2⟩))
      rintro ω ⟨ha, hspan, hbelow⟩
      have haeq : clockCount (virtualLabels init ω s) = C := ha.2
      exact ⟨ha, hspan, by rw [← haeq]; exact hbelow⟩
    · have hempty : A C = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      simp only [hempty, Set.empty_inter, measure_empty, mul_zero, le_refl]
  calc
    law init (E ∩ B) ≤ law init (⋃ C, A C ∩ B) := measure_mono hcover
    _ ≤ ∑' C, law init (A C ∩ B) := measure_iUnion_le _
    _ ≤ ∑' C, ENNReal.ofReal (1 / (init.card : ℝ) ^ 9) * law init (A C) :=
      ENNReal.tsum_le_tsum hlocal
    _ = ENNReal.ofReal (1 / (init.card : ℝ) ^ 9) * ∑' C, law init (A C) := by
      rw [ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal (1 / (init.card : ℝ) ^ 9) * law init E := by
      rw [← measure_iUnion hdisj
        (fun C => ((pairLogFiltration L 256).le s) _ (hAm C)), hunion]

def observedBulkFailure (init : Cfg L 256) (ℓ : ℕ)
    (T : Ω L 256 → WithTop ℕ) : Set (Ω L 256) :=
  {ω | ∃ s : ℕ, T ω = (s : WithTop ℕ) ∧
    ω ∈ randomCountPassageFailure init ℓ s
      (PhaseThreeModel.Numeric.firstHitHorizon init.card)}

/-- The failure on each observed time fibre is measured at that fibre's
deadline, including its finite environment span. -/
theorem bulk_failure_fibre_measurable (init : Cfg L 256) (ℓ : ℕ)
    (T : Ω L 256 → WithTop ℕ) (E : Set (Ω L 256)) (s : ℕ)
    (hprefix : MeasurableSet[pairLogFiltration L 256 s]
      (E ∩ {ω | T ω = (s : WithTop ℕ)})) :
    MeasurableSet[pairLogFiltration L 256
        (s + PhaseThreeModel.Numeric.firstHitHorizon init.card)]
      ((E ∩ {ω | T ω = (s : WithTop ℕ)}) ∩
        randomCountPassageFailure init ℓ s
          (PhaseThreeModel.Numeric.firstHitHorizon init.card)) := by
  have hEend : MeasurableSet[pairLogFiltration L 256
        (s + PhaseThreeModel.Numeric.firstHitHorizon init.card)]
      (E ∩ {ω | T ω = (s : WithTop ℕ)}) :=
    ((pairLogFiltration L 256).mono (by omega :
      s ≤ s + PhaseThreeModel.Numeric.firstHitHorizon init.card)) _ hprefix
  exact hEend.inter (randomCountPassageFailure_measurable init ℓ s _)

/-- A genuine observed passage can be infinite on other paths. The local
tail is summed only over its finite observed fibres, with no future
success condition in the prefix. -/
theorem bulk_observed_passage_tail (init : Cfg L 256)
    (hm : 20 ≤ init.card) (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1))
    (T : Ω L 256 → WithTop ℕ) (E : Set (Ω L 256))
    (hprefix : ∀ s : ℕ, MeasurableSet[pairLogFiltration L 256 s]
      (E ∩ {ω | T ω = (s : WithTop ℕ)}))
    (hstart : ∀ s : ℕ, ∀ ω ∈ E, T ω = (s : WithTop ℕ) →
      DensePositiveStart init ℓ ω s) :
    law init (E ∩ observedBulkFailure init ℓ T) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 9) * law init E := by
  let A : ℕ → Set (Ω L 256) :=
    fun s => E ∩ {ω | T ω = (s : WithTop ℕ)}
  let B : ℕ → Set (Ω L 256) :=
    fun s => randomCountPassageFailure init ℓ s
      (PhaseThreeModel.Numeric.firstHitHorizon init.card)
  have hdisj : Pairwise (fun s u => Disjoint (A s) (A u)) := by
    intro s u hsu
    apply Set.disjoint_left.mpr
    rintro ω ⟨-, hs⟩ ⟨-, hu⟩
    exact hsu (WithTop.coe_injective (hs.symm.trans hu))
  have hcover : E ∩ observedBulkFailure init ℓ T ⊆ ⋃ s, A s ∩ B s := by
    rintro ω ⟨hω, s, hs, hb⟩
    exact Set.mem_iUnion.mpr ⟨s, ⟨hω, hs⟩, hb⟩
  have hmass : (∑' s, law init (A s)) ≤ law init E := by
    rw [← measure_iUnion hdisj
      (fun s => ((pairLogFiltration L 256).le s) _ (hprefix s))]
    apply measure_mono
    intro ω hω
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hω
    exact hs.1
  have hlocal (s : ℕ) :
      law init (A s ∩ B s) ≤ ENNReal.ofReal (1 / (init.card : ℝ) ^ 9) *
        law init (A s) :=
    random_count_bulk_prefix_tail init hm ℓ s hℓ hcap (A s) (hprefix s)
      (fun ω hω => hstart s ω hω.1 hω.2)
  calc
    law init (E ∩ observedBulkFailure init ℓ T) ≤
        law init (⋃ s, A s ∩ B s) := measure_mono hcover
    _ ≤ ∑' s, law init (A s ∩ B s) := measure_iUnion_le _
    _ ≤ ∑' s, ENNReal.ofReal (1 / (init.card : ℝ) ^ 9) * law init (A s) :=
      ENNReal.tsum_le_tsum hlocal
    _ = ENNReal.ofReal (1 / (init.card : ℝ) ^ 9) * ∑' s, law init (A s) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal (1 / (init.card : ℝ) ^ 9) * law init E :=
      mul_le_mul_left' hmass _

def randomCountNeverHit (init : Cfg L 256) (ℓ s : ℕ) : Set (Ω L 256) :=
  {ω | (∀ t, ClockEnvironment (virtualLabels init ω (s + t))) ∧
    ¬ ∃ t, StageEventSpec.bulkThreshold (clockCount (virtualLabels init ω s)) ≤
      frontCount (virtualLabels init ω (s + t)) ℓ}

/-- Random current Clock counts also sum out in the qualitative finite
passage theorem. This is an outer-measure null statement, so the all-time
environment is not required to be a prefix event. -/
theorem random_count_never_hit_null (init : Cfg L 256)
    (hc : 2 ≤ init.card) (ℓ s : ℕ)
    (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1))
    (E : Set (Ω L 256))
    (hstart : ∀ ω ∈ E, DensePositiveStart init ℓ ω s) :
    law init (E ∩ randomCountNeverHit init ℓ s) = 0 := by
  classical
  let A : ℕ → Set (Ω L 256) :=
    fun C => E ∩ {ω | clockCount (virtualLabels init ω s) = C}
  let B := randomCountNeverHit init ℓ s
  have hcover : E ∩ B ⊆ ⋃ C, A C ∩ B := by
    rintro ω ⟨hω, hb⟩
    exact Set.mem_iUnion.mpr
      ⟨clockCount (virtualLabels init ω s), ⟨hω, rfl⟩, hb⟩
  have hlocal (C : ℕ) : law init (A C ∩ B) = 0 := by
    by_cases hne : (A C).Nonempty
    · obtain ⟨ω, hω⟩ := hne
      have hCeq : clockCount (virtualLabels init ω s) = C := hω.2
      have hdensity : 6 * init.card ≤ 25 * C := by
        rw [← hCeq]; exact (hstart ω hω.1).2
      apply le_antisymm ?_ zero_le
      apply (measure_mono ?_).trans
        (le_of_eq (observed_bulk_never_hit_null init hc C ℓ s hdensity hℓ hcap (A C)
          (fun ω hω => ⟨(hstart ω hω.1).1, hω.2⟩)))
      rintro ω ⟨ha, henv, hnever⟩
      have haeq : clockCount (virtualLabels init ω s) = C := ha.2
      exact ⟨ha, henv, by rw [← haeq]; exact hnever⟩
    · have hempty : A C = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      simp only [hempty, Set.empty_inter, measure_empty]
  apply le_antisymm ?_ zero_le
  calc
    law init (E ∩ B) ≤ law init (⋃ C, A C ∩ B) := measure_mono hcover
    _ ≤ ∑' C, law init (A C ∩ B) := measure_iUnion_le _
    _ = 0 := by simp only [hlocal, tsum_zero]

def observedBulkNeverHit (init : Cfg L 256) (ℓ : ℕ)
    (T : Ω L 256 → WithTop ℕ) : Set (Ω L 256) :=
  {ω | ∃ s : ℕ, T ω = (s : WithTop ℕ) ∧
    ω ∈ randomCountNeverHit init ℓ s}

/-- Qualitative finite bulk passage on any finite observed start fibre.
The statement does not impose finiteness of T on the remaining paths. -/
theorem bulk_observed_never_hit_null (init : Cfg L 256)
    (hc : 2 ≤ init.card) (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1))
    (T : Ω L 256 → WithTop ℕ) (E : Set (Ω L 256))
    (hstart : ∀ s : ℕ, ∀ ω ∈ E, T ω = (s : WithTop ℕ) →
      DensePositiveStart init ℓ ω s) :
    law init (E ∩ observedBulkNeverHit init ℓ T) = 0 := by
  let A : ℕ → Set (Ω L 256) :=
    fun s => E ∩ {ω | T ω = (s : WithTop ℕ)}
  let B : ℕ → Set (Ω L 256) := fun s => randomCountNeverHit init ℓ s
  have hcover : E ∩ observedBulkNeverHit init ℓ T ⊆ ⋃ s, A s ∩ B s := by
    rintro ω ⟨hω, s, hs, hb⟩
    exact Set.mem_iUnion.mpr ⟨s, ⟨hω, hs⟩, hb⟩
  have hlocal (s : ℕ) : law init (A s ∩ B s) = 0 :=
    random_count_never_hit_null init hc ℓ s hℓ hcap (A s)
      (fun ω hω => hstart s ω hω.1 hω.2)
  apply le_antisymm ?_ zero_le
  calc
    law init (E ∩ observedBulkNeverHit init ℓ T) ≤
        law init (⋃ s, A s ∩ B s) := measure_mono hcover
    _ ≤ ∑' s, law init (A s ∩ B s) := measure_iUnion_le _
    _ = 0 := by simp only [hlocal, tsum_zero]

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockObservedPassageSplice

end
