/-
  Bridge from Mathlib measures to the lightweight ProbSpec interface.

  A Mathlib `Measure Ω` gives `ProbSpec Ω` via `fun E => μ E`,
  and the `ProbAxioms` follow from standard measure properties.
-/
import Ripple.sCRNUniversality.Probability.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

namespace Ripple.sCRNUniversality.Probability

open MeasureTheory

noncomputable def ProbSpec.ofMeasure
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) :
    ProbSpec Ω where
  Pr := fun E => μ E

private theorem ENNReal.tsum_le_of_sum_range_le
    {err : ℕ → ENNReal} {ε : ENNReal}
    (h : ∀ N, (Finset.range N).sum err ≤ ε) :
    (∑' n, err n) ≤ ε := by
  rw [ENNReal.tsum_eq_iSup_nat]
  exact iSup_le h

theorem ProbAxioms.ofMeasure
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) :
    ProbAxioms.{_, 0} (ProbSpec.ofMeasure μ) where
  monotone := fun hEF => measure_mono hEF
  union_le_add := fun E F => measure_union_le E F
  finUnion_le_sum := by
    classical
    intro I s E
    induction s using Finset.induction_on with
    | empty =>
      show μ _ ≤ _
      have : finUnion ∅ E = ∅ := by
        ext ω; simp [finUnion]
      rw [this, measure_empty]; exact zero_le'
    | insert a s ha ih =>
      show μ _ ≤ _
      simp only [ProbSpec.ofMeasure] at ih
      have hsub : finUnion (Insert.insert a s) E ⊆ E a ∪ finUnion s E := by
        intro ω ⟨i, hi, hEi⟩
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact Or.inl hEi
        · exact Or.inr ⟨i, hi, hEi⟩
      calc μ (finUnion (Insert.insert a s) E)
          ≤ μ (E a ∪ finUnion s E) := measure_mono hsub
        _ ≤ μ (E a) + μ (finUnion s E) := measure_union_le _ _
        _ ≤ μ (E a) + s.sum (fun i => μ (E i)) := add_le_add le_rfl ih
        _ = (Insert.insert a s).sum (fun i => μ (E i)) := by
            rw [Finset.sum_insert ha]
  countUnion_le_of_prefixBounds := by
    intro E err ε hE herr
    have hsub : countUnion E ⊆ ⋃ n, E n := by
      intro ω ⟨n, hn⟩; exact Set.mem_iUnion.mpr ⟨n, hn⟩
    calc μ (countUnion E)
        ≤ μ (⋃ n, E n) := measure_mono hsub
      _ ≤ ∑' n, μ (E n) := measure_iUnion_le _
      _ ≤ ∑' n, err n := ENNReal.tsum_le_tsum hE
      _ ≤ ε := ENNReal.tsum_le_of_sum_range_le herr

end Ripple.sCRNUniversality.Probability
