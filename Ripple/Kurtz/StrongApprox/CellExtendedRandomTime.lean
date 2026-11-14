-- Ripple/Kurtz/StrongApprox/CellExtendedRandomTime.lean
import Ripple.Kurtz.StrongApprox.CellExtendedStoppingLine

noncomputable section

namespace Ripple.Kurtz.StrongApprox.CellExtendedRandomTime

open MeasureTheory ProbabilityTheory Set Filter Topology Preorder
open scoped ENNReal NNReal BigOperators
open CellRandomTimeEvaluation CellStoppingLineFreshness
open CellExtendedStoppingLine

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Countably-valued random time, known to lie in one rectangular past. -/
theorem measurable_cellPath_at_countable_bounded
    (u : ι → ℝ≥0) (l : ι)
    (τ : CellFamily ι → ℝ≥0)
    (hτ : Measurable[cellPast u] τ)
    (hbound : ∀ c, τ c ≤ u l)
    (hcount : (Set.range τ).Countable) :
    Measurable[cellPast u] fun c => cellPath (τ c) (c l) := by
  classical
  haveI : Countable (Set.range τ) := hcount.to_subtype
  letI mu : MeasurableSpace (CellFamily ι) := cellPast u
  refine measurable_to_countable' ?_
  intro k
  have hset :
      {c | cellPath (τ c) (c l) = k} =
        ⋃ r : Set.range τ,
          {c | τ c = r.1} ∩ {c | cellPath r.1 (c l) = k} := by
    ext c
    constructor
    · intro hc
      exact Set.mem_iUnion.mpr
        ⟨⟨τ c, ⟨c, rfl⟩⟩, rfl, hc⟩
    · intro hc
      obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hc
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hr ⊢
      rw [hr.1]
      exact hr.2
  show MeasurableSet {c | cellPath (τ c) (c l) = k}
  rw [hset]
  apply MeasurableSet.iUnion
  intro r
  obtain ⟨c0, hc0⟩ := r.2
  have hrbound : r.1 ≤ u l := by
    rw [← hc0]
    exact hbound c0
  exact (hτ (measurableSet_singleton r.1)).inter
    ((measurable_cellPath_cellPast u l r.1 hrbound)
      (measurableSet_singleton k))

noncomputable def cappedUpperTime
    (m : ℕ) (U t : ℝ≥0) : ℝ≥0 :=
  min (upperDyadicTime m t) U

@[fun_prop]
theorem measurable_cappedUpperTime
    (m : ℕ) (U : ℝ≥0) :
    Measurable (cappedUpperTime m U) := by
  exact (measurable_upperDyadicTime m).min measurable_const

theorem cappedUpperTime_le
    (m : ℕ) (U t : ℝ≥0) : cappedUpperTime m U t ≤ U :=
  min_le_right _ _

theorem cappedUpperTime_range_countable
    (m : ℕ) (U : ℝ≥0) :
    (Set.range (cappedUpperTime m U)).Countable := by
  refine Set.Countable.mono ?_
    ((Set.countable_range fun j : ℕ => dyadicGridTime m j).union
      (Set.countable_singleton U))
  rintro x ⟨t, rfl⟩
  by_cases h : upperDyadicTime m t ≤ U
  · left
    exact ⟨upperDyadicIndex m t, by simp only [cappedUpperTime, min_eq_left h]; rfl⟩
  · right
    simp [cappedUpperTime, min_eq_right (le_of_not_ge h)]

theorem cellPath_cappedUpper_eventually
    (c : ℕ → CellSpace) {t U : ℝ≥0} (ht : t ≤ U) :
    ∀ᶠ m : ℕ in atTop,
      cellPath (cappedUpperTime m U t) c = cellPath t c := by
  by_cases hlt : t < U
  · have hplain := cellPath_upperDyadic_eventually c t
    have hlim : Tendsto (fun m => (upperDyadicTime m t : ℝ)) atTop
        (𝓝 (t : ℝ)) :=
      (upperDyadicTime_tendsto_right t).mono_right nhdsWithin_le_nhds
    have hbelow : ∀ᶠ m : ℕ in atTop,
        upperDyadicTime m t < U := by
      have hreal : (t : ℝ) < (U : ℝ) := by exact_mod_cast hlt
      filter_upwards [(tendsto_order.1 hlim).2 _ hreal] with m hm
      exact_mod_cast hm
    filter_upwards [hplain, hbelow] with m hm hmu
    simpa [cappedUpperTime, min_eq_left hmu.le] using hm
  · have heq : t = U := le_antisymm ht (not_lt.mp hlt)
    subst U
    filter_upwards [] with m
    simp [cappedUpperTime, min_eq_right (le_upperDyadicTime m t)]

/-- Evaluation at an arbitrary measurable random time bounded by one cell-past
rectangle. -/
theorem measurable_cellPath_boundedRandomTime
    (u : ι → ℝ≥0) (l : ι)
    (τ : CellFamily ι → ℝ≥0)
    (hτ : Measurable[cellPast u] τ)
    (hbound : ∀ c, τ c ≤ u l) :
    Measurable[cellPast u] fun c => cellPath (τ c) (c l) := by
  let F : ℕ → CellFamily ι → ℕ := fun m c =>
    cellPath (cappedUpperTime m (u l) (τ c)) (c l)
  have hF : ∀ m, Measurable[cellPast u] (F m) := by
    intro m
    apply measurable_cellPath_at_countable_bounded u l
      (fun c => cappedUpperTime m (u l) (τ c))
    · exact (measurable_cappedUpperTime m (u l)).comp hτ
    · exact fun c => cappedUpperTime_le m (u l) (τ c)
    · exact Set.Countable.mono
        (by
          rintro x ⟨c, rfl⟩
          exact ⟨τ c, rfl⟩)
        (cappedUpperTime_range_countable m (u l))
  have hevent (c : CellFamily ι) :
      ∀ᶠ m : ℕ in atTop, F m c = cellPath (τ c) (c l) :=
    cellPath_cappedUpper_eventually (c l) (hbound c)
  letI mu : MeasurableSpace (CellFamily ι) := cellPast u
  refine measurable_to_countable' ?_
  intro k
  have hset :
      {c | cellPath (τ c) (c l) = k} =
        ⋃ N : ℕ, ⋂ m : ℕ, {c | N ≤ m → F m c = k} := by
    ext c
    constructor
    · intro hc
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hevent c)
      exact Set.mem_iUnion.mpr
        ⟨N, Set.mem_iInter.mpr fun m hm => by rw [hN m hm]; exact hc⟩
    · intro hc
      obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hc
      obtain ⟨M, hM⟩ := eventually_atTop.1 (hevent c)
      have hvalue := (Set.mem_iInter.mp hN (max N M)) (le_max_left _ _)
      rw [hM (max N M) (le_max_right _ _)] at hvalue
      exact hvalue
  show MeasurableSet {c | cellPath (τ c) (c l) = k}
  rw [hset]
  apply MeasurableSet.iUnion
  intro N
  apply MeasurableSet.iInter
  intro m
  by_cases hNm : N ≤ m
  · have heq : {c | N ≤ m → F m c = k} = F m ⁻¹' {k} := by
      ext c
      simp [hNm]
    rw [heq]
    exact hF m (measurableSet_singleton k)
  · have heq : {c | N ≤ m → F m c = k} = Set.univ := by
      ext c
      simp [hNm]
    rw [heq]
    exact MeasurableSet.univ

/-- Count in channel `l` at the finite part of an extended line. -/
noncomputable def extendedPathAt
    (σ : ExtendedCellLine ι) (l : ι) (c : CellFamily ι) : ℕ :=
  cellPath (finitePart σ c l) (c l)

@[fun_prop]
theorem measurable_extendedPathAt
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (l : ι) :
    Measurable[extendedStoppedPast σ hσ] (extendedPathAt σ l) := by
  have hambient : Measurable (extendedPathAt σ l) := by
    exact measurable_cellFamilyPath_randomTime id measurable_id
      (finitePart σ) (measurable_finitePart hσ.measurable) l
  intro B hB
  refine ⟨hambient hB, ?_⟩
  intro u
  let τu : CellFamily ι → ℝ≥0 := fun c => belowValue σ u c l
  have hτu : Measurable[cellPast u] τu :=
    measurable_belowValue hσ u l
  have hbound : ∀ c, τu c ≤ u l :=
    fun c => belowValue_le hσ u c l
  have heval : Measurable[cellPast u]
      (fun c => cellPath (τu c) (c l)) :=
    measurable_cellPath_boundedRandomTime u l τu hτu hbound
  have heq :
      extendedPathAt σ l ⁻¹' B ∩ extendedLineBelow σ u =
        (fun c => cellPath (τu c) (c l)) ⁻¹' B ∩
          extendedLineBelow σ u := by
    ext c
    by_cases hc : c ∈ extendedLineBelow σ u
    · simp only [Set.mem_inter_iff, Set.mem_preimage, hc, and_true]
      show extendedPathAt σ l c ∈ B ↔ cellPath (belowValue σ u c l) (c l) ∈ B
      rw [belowValue_eq_of_mem hc]
      rfl
    · simp [hc]
  rw [heq]
  exact (heval hB).inter (hσ.stopping u)

noncomputable def lineIncrement
    (σ τ : ExtendedCellLine ι) (l : ι) (c : CellFamily ι) : ℕ :=
  extendedPathAt τ l c - extendedPathAt σ l c

@[fun_prop]
theorem measurable_lineIncrement
    {σ τ : ExtendedCellLine ι}
    (hσ : ExtendedCellStoppingLine σ)
    (hτ : ExtendedCellStoppingLine τ)
    (hle : ∀ c l, σ c l ≤ τ c l)
    (l : ι) :
    Measurable[extendedStoppedPast τ hτ]
      (lineIncrement σ τ l) := by
  have hsource : Measurable[extendedStoppedPast τ hτ]
      (extendedPathAt σ l) :=
    Measurable.mono (measurable_extendedPathAt hσ l)
      (extendedStoppedPast_mono hσ hτ hle) le_rfl
  exact (measurable_extendedPathAt hτ l).sub hsource

end Ripple.Kurtz.StrongApprox.CellExtendedRandomTime

end
