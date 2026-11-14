/-
  Ripple.Kurtz.StrongApprox.BlockIid — independence across the coordinates of a product space
  combined with independence inside each coordinate (block) gives an independent family indexed
  by cells.

  Mathematics: the coarse-block construction.

  Setting: `Ω = ι → B` with `P = Measure.infinitePi μ`, a cell index `κ`, a block map `b : κ → ι`,
  and cell functions `W c : B → β c` read off the block `ω (b c)`. If for every block `j` the
  cells `{c | b c = j}` are independent under `μ j`, then the whole family `c ↦ W c (ω (b c))` is
  independent under `P`, and its marginals are `(μ (b c)).map (W c)`.
-/

import Mathlib

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set

variable {ι κ : Type*} {B : Type*} [MeasurableSpace B]

/-! ### Coordinates of a product measure -/

theorem infinitePi_eval_preimage (μ : ι → Measure B) [∀ j, IsProbabilityMeasure (μ j)] (j : ι)
    {s : Set B} (hs : MeasurableSet s) :
    Measure.infinitePi μ ((fun ω : ι → B => ω j) ⁻¹' s) = μ j s := by
  rw [← Measure.map_apply (measurable_pi_apply j) hs, Measure.infinitePi_map_eval]

/-- The law of a cell function read off one coordinate. -/
theorem infinitePi_map_cell (μ : ι → Measure B) [∀ j, IsProbabilityMeasure (μ j)]
    {β : Type*} [MeasurableSpace β] (j : ι) {W : B → β} (hW : Measurable W) :
    (Measure.infinitePi μ).map (fun ω : ι → B => W (ω j)) = (μ j).map W := by
  rw [← Measure.infinitePi_map_eval μ j, Measure.map_map hW (measurable_pi_apply j)]
  rfl

/-- **Cells of a block product are independent.** -/
theorem iIndepFun_cells [DecidableEq ι] (μ : ι → Measure B) [∀ j, IsProbabilityMeasure (μ j)]
    {β : κ → Type*} [∀ c, MeasurableSpace (β c)] (b : κ → ι) (W : ∀ c, B → β c)
    (hW : ∀ c, Measurable (W c))
    (hblk : ∀ j, iIndepFun (fun c : {c // b c = j} => W c.1) (μ j)) :
    iIndepFun (fun c (ω : ι → B) => W c (ω (b c))) (Measure.infinitePi μ) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  classical
  have htmeas : ∀ j ∈ S.image b,
      MeasurableSet (⋂ c ∈ S.filter (fun c => b c = j), (W c) ⁻¹' (sets c)) := by
    intro j _
    refine Finset.measurableSet_biInter _ fun c hc => ?_
    exact hW c (hsets c (Finset.mem_filter.mp hc).1)
  have hE : (⋂ c ∈ S, (fun ω : ι → B => W c (ω (b c))) ⁻¹' sets c) =
      (↑(S.image b) : Set ι).pi
        (fun j => ⋂ c ∈ S.filter (fun c => b c = j), (W c) ⁻¹' (sets c)) := by
    ext ω
    simp only [mem_iInter, mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_image,
      Finset.mem_filter]
    constructor
    · rintro h j ⟨c, hcS, rfl⟩ c' ⟨hc'S, hc'⟩
      rw [← hc']; exact h c' hc'S
    · intro h c hc
      exact h (b c) ⟨c, hc, rfl⟩ c ⟨hc, rfl⟩
  rw [hE, Measure.infinitePi_pi μ htmeas]
  have hblock : ∀ j ∈ S.image b,
      μ j (⋂ c ∈ S.filter (fun c => b c = j), (W c) ⁻¹' (sets c)) =
        ∏ c ∈ S.filter (fun c => b c = j), μ (b c) ((W c) ⁻¹' sets c) := by
    intro j _
    have h1 : (⋂ c ∈ S.filter (fun c => b c = j), (W c) ⁻¹' (sets c)) =
        ⋂ c ∈ S.subtype (fun c => b c = j), (W c.1) ⁻¹' (sets c.1) := by
      ext x
      simp only [mem_iInter, Finset.mem_subtype, Finset.mem_filter]
      constructor
      · intro h c hc; exact h c.1 ⟨hc, c.2⟩
      · intro h c hc; exact h ⟨c, hc.2⟩ hc.1
    rw [h1, (hblk j).meas_biInter
      (fun c hc => ⟨sets c.1, hsets c.1 (Finset.mem_subtype.mp hc), rfl⟩)]
    rw [Finset.prod_subtype_eq_prod_filter (fun c => μ j ((W c) ⁻¹' sets c))]
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [(Finset.mem_filter.mp hc).2]
  calc ∏ j ∈ S.image b, μ j (⋂ c ∈ S.filter (fun c => b c = j), (W c) ⁻¹' (sets c))
      = ∏ j ∈ S.image b, ∏ c ∈ S.filter (fun c => b c = j), μ (b c) ((W c) ⁻¹' sets c) :=
        Finset.prod_congr rfl hblock
    _ = ∏ c ∈ S, μ (b c) ((W c) ⁻¹' sets c) :=
        Finset.prod_fiberwise_of_maps_to (fun c hc => Finset.mem_image_of_mem b hc) _
    _ = ∏ c ∈ S, Measure.infinitePi μ ((fun ω : ι → B => W c (ω (b c))) ⁻¹' sets c) := by
        refine Finset.prod_congr rfl fun c hc => ?_
        rw [show (fun ω : ι → B => W c (ω (b c))) ⁻¹' sets c =
          (fun ω : ι → B => ω (b c)) ⁻¹' ((W c) ⁻¹' sets c) from rfl]
        rw [infinitePi_eval_preimage μ (b c) (hW c (hsets c hc))]

/-! ### Functions of one factor of a product measure -/

section Prod

variable {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]

theorem prod_fst_preimage (μ : Measure α) (ν : Measure γ) [IsProbabilityMeasure ν] (s : Set α) :
    (μ.prod ν) (Prod.fst ⁻¹' s) = μ s := by
  rw [← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one]

theorem prod_snd_preimage (μ : Measure α) (ν : Measure γ) [IsProbabilityMeasure μ]
    [SFinite ν] (t : Set γ) :
    (μ.prod ν) (Prod.snd ⁻¹' t) = ν t := by
  rw [← Set.univ_prod, Measure.prod_prod, measure_univ, one_mul]

/-- An independent family of functions of the first factor stays independent under a product. -/
theorem iIndepFun_comp_fst {μ : Measure α} (ν : Measure γ) [IsProbabilityMeasure ν]
    {β : κ → Type*} [∀ i, MeasurableSpace (β i)] {f : ∀ i, α → β i} (hf : iIndepFun f μ) :
    iIndepFun (fun i (x : α × γ) => f i x.1) (μ.prod ν) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hf ⊢
  intro S sets hsets
  have hE : (⋂ i ∈ S, (fun x : α × γ => f i x.1) ⁻¹' sets i) =
      Prod.fst ⁻¹' (⋂ i ∈ S, f i ⁻¹' sets i) := by
    ext x; simp
  rw [hE, prod_fst_preimage, hf S hsets]
  exact Finset.prod_congr rfl fun i _ => (prod_fst_preimage μ ν _).symm

theorem map_comp_fst (μ : Measure α) (ν : Measure γ) [IsProbabilityMeasure ν]
    {β : Type*} [MeasurableSpace β] {g : α → β} (hg : Measurable g) :
    (μ.prod ν).map (fun x : α × γ => g x.1) = μ.map g := by
  rw [show (fun x : α × γ => g x.1) = g ∘ Prod.fst from rfl,
    ← Measure.map_map hg measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]

theorem map_comp_snd (μ : Measure α) (ν : Measure γ) [IsProbabilityMeasure μ] [SFinite ν]
    {β : Type*} [MeasurableSpace β] {g : γ → β} (hg : Measurable g) :
    (μ.prod ν).map (fun x : α × γ => g x.2) = ν.map g := by
  rw [show (fun x : α × γ => g x.2) = g ∘ Prod.snd from rfl,
    ← Measure.map_map hg measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]

end Prod

end Ripple.Kurtz.StrongApprox
