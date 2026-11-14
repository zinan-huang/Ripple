-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockObservedStarts.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockBulkFamily

/-!
# Canonical observed positive-front starts

The starting time is the first current state with a positive front and the
Clock density needed by P3a. It is defined on every log, with value top if
no such state is observed. Thus the quantitative passage theorems below
have no unproved start-data hypothesis.

On an AsyncEntry path the density holds at every later state. A separate
bridge identifies this stopping time with the genuine first positive
front used by ClockCore. Future entry success is not part of the prefix.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockObservedStarts

open TimeTheorem PairLog PhaseThreeClockObservedPassageSplice
  PhaseThreeClockBulkFamily

variable {L : ℕ}

open Classical in
def firstDenseTime (init : Cfg L 256) (s ell : ℕ)
    (ω : Ω L 256) : WithTop ℕ :=
  if h : ∃ u, s ≤ u ∧ DensePositiveStart init ell ω u
  then ((Nat.find h : ℕ) : WithTop ℕ) else ⊤

theorem firstDenseTime_le_iff (init : Cfg L 256) (s ell N : ℕ)
    (ω : Ω L 256) :
    firstDenseTime init s ell ω ≤ (N : WithTop ℕ) ↔
      ∃ u ≤ N, s ≤ u ∧ DensePositiveStart init ell ω u := by
  classical
  unfold firstDenseTime
  split_ifs with h
  · constructor
    · intro hle
      have hu : Nat.find h ≤ N := by exact_mod_cast hle
      exact ⟨Nat.find h, hu, Nat.find_spec h⟩
    · rintro ⟨u, hu, hsu, hstate⟩
      have hle : Nat.find h ≤ N :=
        (Nat.find_min' h ⟨hsu, hstate⟩).trans hu
      exact_mod_cast hle
  · constructor
    · intro hle
      exact absurd hle (by simp)
    · rintro ⟨u, -, hsu, hstate⟩
      exact absurd ⟨u, hsu, hstate⟩ h

theorem firstDenseTime_finite_state (init : Cfg L 256) (s ell u : ℕ)
    (ω : Ω L 256) (hu : firstDenseTime init s ell ω = (u : WithTop ℕ)) :
    s ≤ u ∧ DensePositiveStart init ell ω u := by
  classical
  unfold firstDenseTime at hu
  split_ifs at hu with h
  · have heq : Nat.find h = u := WithTop.coe_injective hu
    simpa only [heq] using Nat.find_spec h
  · exact absurd hu WithTop.top_ne_coe

theorem firstDenseTime_eq_of_firstAfter (init : Cfg L 256)
    (s ell u : ℕ) (ω : Ω L 256)
    (hfirst : StageEventSpec.firstAfter
      (fun v => 1 ≤ PhaseThreeClockGatedLaw.frontCount
        (PhaseThreeClockVirtual.virtualLabels init ω v) ell) s u)
    (hdensity : ∀ v, s ≤ v →
      6 * init.card ≤ 25 * PhaseThreeClockGatedLaw.clockCount
        (PhaseThreeClockVirtual.virtualLabels init ω v)) :
    firstDenseTime init s ell ω = (u : WithTop ℕ) := by
  have hupper : firstDenseTime init s ell ω ≤ (u : WithTop ℕ) :=
    (firstDenseTime_le_iff init s ell u ω).2
      ⟨u, le_rfl, hfirst.1, hfirst.2.1, hdensity u hfirst.1⟩
  apply le_antisymm hupper
  by_contra hnot
  have hlt : firstDenseTime init s ell ω < (u : WithTop ℕ) := lt_of_not_ge hnot
  have hfinite : firstDenseTime init s ell ω ≠ ⊤ := by
    intro htop
    rw [htop] at hlt
    exact not_lt_of_ge le_top hlt
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hvu : v < u := by
    rw [← hv] at hlt
    exact WithTop.coe_lt_coe.mp hlt
  have hstate := firstDenseTime_finite_state init s ell v ω hv.symm
  exact hfirst.2.2 v hstate.1 hvu hstate.2.1

theorem firstDenseTime_isStoppingTime (init : Cfg L 256) (s ell : ℕ) :
    IsStoppingTime (pairLogFiltration L 256) (firstDenseTime init s ell) := by
  intro N
  have hm : MeasurableSet[pairLogFiltration L 256 N]
      (⋃ u : ℕ, {ω | u ≤ N ∧ s ≤ u ∧ DensePositiveStart init ell ω u}) := by
    refine MeasurableSet.iUnion fun u => ?_
    by_cases hu : u ≤ N
    · by_cases hs : s ≤ u
      · have hstate : MeasurableSet[pairLogFiltration L 256 N]
            {ω | DensePositiveStart init ell ω u} :=
          ((pairLogFiltration L 256).mono hu) _
            (densePositiveStart_measurable init ell u)
        simpa only [hu, hs, true_and] using hstate
      · simp only [hs, and_false, false_and, Set.setOf_false, MeasurableSet.empty]
    · simp only [hu, false_and, Set.setOf_false, MeasurableSet.empty]
  convert hm using 1
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  exact firstDenseTime_le_iff init s ell N ω

theorem firstDenseTime_prefix_fibre_measurable (init : Cfg L 256)
    (s ell u : ℕ) (E : Set (Ω L 256))
    (hE : MeasurableSet[pairLogFiltration L 256 s] E) :
    MeasurableSet[pairLogFiltration L 256 u]
      (E ∩ {ω | firstDenseTime init s ell ω = (u : WithTop ℕ)}) := by
  by_cases hsu : s ≤ u
  · exact (((pairLogFiltration L 256).mono hsu) _ hE).inter
      ((firstDenseTime_isStoppingTime init s ell).measurableSet_eq_of_countable u)
  · have hempty :
        (E ∩ {ω | firstDenseTime init s ell ω = (u : WithTop ℕ)}) = ∅ := by
      ext ω
      constructor
      · rintro ⟨-, hu⟩
        exact False.elim (hsu (firstDenseTime_finite_state init s ell u ω hu).1)
      · intro hω
        exact False.elim hω
    rw [hempty]
    exact MeasurableSpace.measurableSet_empty _

/-- P3a from a canonical observed start, with no start-data hypothesis. -/
theorem firstDense_bulk_prefix_tail (init : Cfg L 256) (hm : 20 ≤ init.card)
    (s ell : ℕ) (hell : 1 ≤ ell) (hcap : ell ≤ 256 * (L + 1))
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 s] E) :
    law init (E ∩ observedBulkFailure init ell (firstDenseTime init s ell)) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 9) * law init E :=
  bulk_observed_passage_tail init hm ell hell hcap (firstDenseTime init s ell) E
    (fun u => firstDenseTime_prefix_fibre_measurable init s ell u E hE)
    (fun u ω _ hu => (firstDenseTime_finite_state init s ell u ω hu).2)

theorem firstDense_bulk_prefix_measurable (init : Cfg L 256)
    (s ell : ℕ) (E : Set (Ω L 256))
    (hE : MeasurableSet[pairLogFiltration L 256 s] E) :
    MeasurableSet
      (E ∩ observedBulkFailure init ell (firstDenseTime init s ell)) :=
  observed_bulk_prefix_measurable init ell (firstDenseTime init s ell) E
    (fun u => firstDenseTime_prefix_fibre_measurable init s ell u E hE)

/-- The canonical all-level P3a event retains the same prefix mass. -/
theorem firstDense_bulk_family_prefix_tail {n : ℕ} (init : InputCfg n)
    (hm : 20 ≤ init.card) (hcard : init.card = n)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (s : ℕ) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ s] E) :
    law init (E ∩ bulkFamilyFailure init
      (Finset.Icc 1 (PhaseThreeModel.Numeric.clockCap n))
      (fun ell => firstDenseTime init s ell)) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 8) * law init E := by
  apply numeric_bulk_family_prefix_tail init hm hcard hn
    (fun ell => firstDenseTime init s ell) E
  · intro ell _ u
    exact firstDenseTime_prefix_fibre_measurable init s ell u E hE
  · intro ell _ u ω _ hu
    exact (firstDenseTime_finite_state init s ell u ω hu).2

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockObservedStarts

end
