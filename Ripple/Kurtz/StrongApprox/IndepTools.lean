/-
  Ripple.Kurtz.StrongApprox.IndepTools — general independence lemmas used to assemble the Poisson
  representation (PR), and the Poisson law of a finite sum of independent Poisson counts.

  * `iIndepFun_prod_pair`: independent families on the two factors of a product measure, read
    off pairwise, form an independent family of pairs (π-system of rectangles).
  * `iIndepFun_cellData`: an independent family of "cell data" `d i`, each carrying an
    independent family of functions `W (i, j)` under its own law, gives an independent family
    indexed by `ι × κ` (the pattern of `iIndepFun_cells`, with an abstract independent family in
    place of the coordinates of a product measure).
  * `iIndepFun_finsets_comp`: measurable functions of an independent family over pairwise
    disjoint finite index sets are independent.
  * `poisson_add_masses`, `poisson_sum_masses`: point masses of sums of independent Poisson
    counts (binomial theorem).
-/

import Mathlib
import Ripple.Kurtz.StrongApprox.PoissonSplitting

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset

/-! ### Pairs on a product measure -/

section Pair

variable {α γ ι : Type*} [MeasurableSpace α] [MeasurableSpace γ] {μ : Measure α} {ν : Measure γ}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {A B : ι → Type*} [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (B i)]

/-- Independent families on the two factors of a product, paired coordinatewise, are
independent. -/
theorem iIndepFun_prod_pair {f : ∀ i, α → A i} {g : ∀ i, γ → B i} (hf : iIndepFun f μ)
    (hg : iIndepFun g ν) (hfm : ∀ i, Measurable (f i)) (hgm : ∀ i, Measurable (g i)) :
    iIndepFun (fun i (x : α × γ) => (f i x.1, g i x.2)) (μ.prod ν) := by
  let F : ∀ i, α × γ → A i × B i := fun i x => (f i x.1, g i x.2)
  have hFm : ∀ i, Measurable (F i) := fun i =>
    ((hfm i).comp measurable_fst).prodMk ((hgm i).comp measurable_snd)
  let π : ι → Set (Set (α × γ)) := fun i =>
    {E | ∃ t ∈ image2 (fun s t => s ×ˢ t) {s : Set (A i) | MeasurableSet s}
      {t : Set (B i) | MeasurableSet t}, F i ⁻¹' t = E}
  rw [iIndepFun_iff_iIndep]
  refine iIndepSets.iIndep (fun i => (hFm i).comap_le) π
    (fun i => isPiSystem_prod.comap (F i)) (fun i => ?_) ?_
  · rw [← generateFrom_prod, MeasurableSpace.comap_generateFrom]
    rfl
  · rw [iIndepSets_iff]
    intro S E hE
    have hE' : ∀ i ∈ S, ∃ (s : Set (A i)) (t : Set (B i)), MeasurableSet s ∧ MeasurableSet t ∧
        E i = (f i ⁻¹' s) ×ˢ (g i ⁻¹' t) := by
      intro i hi
      obtain ⟨u, hu, hEu⟩ := hE i hi
      obtain ⟨s, hs, t, ht, rfl⟩ := hu
      refine ⟨s, t, hs, ht, ?_⟩
      rw [← hEu]
      ext ⟨x, y⟩
      simp [F]
    choose! s t hs ht hEst using hE'
    have h1 : (⋂ i ∈ S, E i) = (⋂ i ∈ S, f i ⁻¹' s i) ×ˢ (⋂ i ∈ S, g i ⁻¹' t i) := by
      ext ⟨x, y⟩
      simp only [Set.mem_iInter, Set.mem_prod, Set.mem_preimage]
      constructor
      · intro h
        exact ⟨fun i hi => by have := h i hi; rw [hEst i hi] at this; exact this.1,
          fun i hi => by have := h i hi; rw [hEst i hi] at this; exact this.2⟩
      · intro h i hi
        rw [hEst i hi]
        exact ⟨h.1 i hi, h.2 i hi⟩
    rw [h1, Measure.prod_prod,
      (iIndepFun_iff_measure_inter_preimage_eq_mul.mp hf) S (fun i hi => hs i hi),
      (iIndepFun_iff_measure_inter_preimage_eq_mul.mp hg) S (fun i hi => ht i hi),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hEst i hi, Measure.prod_prod]

end Pair

/-! ### Cells carrying independent families -/

section CellData

variable {Ω ι κ D β : Type*} [MeasurableSpace Ω] [MeasurableSpace D] [MeasurableSpace β]
  {P : Measure Ω}

/-- **Cells with independent data.** If the cell data `d i : Ω → D` are independent and, for
each `i`, the functions `W (i, j)` of the data are independent under the law of `d i`, then the
family `(i, j) ↦ W (i, j) (d i ω)` is independent. -/
theorem iIndepFun_cellData [IsProbabilityMeasure P] [DecidableEq ι] [DecidableEq κ] {d : ι → Ω → D}
    (hd : iIndepFun d P)
    (hdm : ∀ i, Measurable (d i)) (W : ι × κ → D → β) (hW : ∀ p, Measurable (W p))
    (hin : ∀ i, iIndepFun (fun j => W (i, j)) (P.map (d i))) :
    iIndepFun (fun p ω => W p (d p.1 ω)) P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  let J : ι → Finset κ := fun i => (S.filter (fun p => p.1 = i)).image Prod.snd
  have hJ : ∀ i j, j ∈ J i → (i, j) ∈ S := by
    intro i j hj
    have hj' : j ∈ (S.filter (fun p => p.1 = i)).image Prod.snd := hj
    obtain ⟨p, hp, hpj⟩ := Finset.mem_image.mp hj'
    obtain ⟨hpS, hp1⟩ := Finset.mem_filter.mp hp
    have : p = (i, j) := Prod.ext hp1 hpj
    rw [← this]
    exact hpS
  let E : ι → Set D := fun i => ⋂ j ∈ J i, W (i, j) ⁻¹' sets (i, j)
  have hEmeas : ∀ i, MeasurableSet (E i) := fun i =>
    Finset.measurableSet_biInter _ fun j hj => hW _ (hsets _ (hJ i j hj))
  have hE : (⋂ p ∈ S, (fun ω => W p (d p.1 ω)) ⁻¹' sets p) =
      ⋂ i ∈ S.image Prod.fst, d i ⁻¹' E i := by
    ext ω
    constructor
    · intro h
      rw [Set.mem_iInter₂] at h ⊢
      intro i _
      rw [Set.mem_preimage, Set.mem_iInter₂]
      intro j hj
      exact h (i, j) (hJ i j hj)
    · intro h
      rw [Set.mem_iInter₂] at h ⊢
      intro p hp
      have h1 := h p.1 (Finset.mem_image_of_mem Prod.fst hp)
      rw [Set.mem_preimage, Set.mem_iInter₂] at h1
      have hmem : p.2 ∈ (S.filter (fun q => q.1 = p.1)).image Prod.snd :=
        Finset.mem_image_of_mem Prod.snd (Finset.mem_filter.mpr ⟨hp, rfl⟩)
      exact h1 p.2 hmem
  rw [hE, (iIndepFun_iff_measure_inter_preimage_eq_mul.mp hd) (S.image Prod.fst)
    (fun i _ => hEmeas i)]
  have hfac : ∀ i ∈ S.image Prod.fst, P (d i ⁻¹' E i) =
      ∏ p ∈ S.filter (fun p => p.1 = i), P ((fun ω => W p (d p.1 ω)) ⁻¹' sets p) := by
    intro i _
    rw [← Measure.map_apply (hdm i) (hEmeas i)]
    have h1 := (iIndepFun_iff_measure_inter_preimage_eq_mul.mp (hin i))
      ((S.filter (fun p => p.1 = i)).image Prod.snd)
      (sets := fun j => sets (i, j)) (fun j hj => hsets _ (hJ i j hj))
    have hinj : ∀ p ∈ S.filter (fun p => p.1 = i), ∀ p' ∈ S.filter (fun p => p.1 = i),
        p.2 = p'.2 → p = p' := by
      intro p hp p' hp' hpp'
      exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hp').2.symm) hpp'
    change (P.map (d i)) (⋂ j ∈ (S.filter (fun p => p.1 = i)).image Prod.snd,
      W (i, j) ⁻¹' sets (i, j)) = _
    rw [h1, Finset.prod_image hinj]
    refine Finset.prod_congr rfl fun p hp => ?_
    obtain ⟨hpS, hp1⟩ := Finset.mem_filter.mp hp
    obtain ⟨a, b⟩ := p
    simp only at hp1
    subst hp1
    rw [Measure.map_apply (hdm a) (hW _ (hsets _ hpS))]
    rfl
  rw [Finset.prod_congr rfl hfac,
    Finset.prod_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem Prod.fst hp)]

end CellData

/-! ### Functions over disjoint finite index sets -/

section Finsets

variable {Ω ι J β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
  {P : Measure Ω}

/-- **Disjoint blocks of an independent family are independent**: measurable functions of the
tuples `(f i)_{i ∈ S j}` over pairwise disjoint finite sets `S j` form an independent family. -/
theorem iIndepFun_finsets_comp [IsProbabilityMeasure P] [DecidableEq ι] [DecidableEq J]
    {f : ι → Ω → β} (hf : iIndepFun f P)
    (hfm : ∀ i, Measurable (f i)) (S : J → Finset ι) (hS : Pairwise (Function.onFun Disjoint S))
    (φ : ∀ j, ((i : S j) → β) → γ) (hφ : ∀ j, Measurable (φ j)) :
    iIndepFun (fun j ω => φ j (fun i : S j => f i ω)) P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro T sets hsets
  induction T using Finset.induction_on with
  | empty => simp
  | insert j₀ T' hj₀ ih =>
    rw [Finset.set_biInter_insert, Finset.prod_insert hj₀]
    let U : Finset ι := T'.biUnion S
    have hdisj : Disjoint (S j₀) U := by
      rw [Finset.disjoint_biUnion_right]
      intro j hj
      exact hS (fun h => hj₀ (h ▸ hj))
    let tS : Ω → ((i : S j₀) → β) := fun ω i => f i ω
    let tU : Ω → ((i : U) → β) := fun ω i => f i ω
    have hind : IndepFun tS tU P := hf.indepFun_finset (S j₀) U hdisj hfm
    let res : (j : T') → ((i : U) → β) → ((i : S j.1) → β) := fun j v i =>
      v ⟨i.1, Finset.mem_biUnion.mpr ⟨j.1, j.2, i.2⟩⟩
    have hres : ∀ j, Measurable (res j) := fun j =>
      measurable_pi_lambda _ fun i => measurable_pi_apply _
    let G' : Set ((i : U) → β) := ⋂ j : T', (fun v => φ j.1 (res j v)) ⁻¹' sets j.1
    have hG'meas : MeasurableSet G' :=
      MeasurableSet.iInter fun j =>
        ((hφ j.1).comp (hres j)) (hsets j.1 (Finset.mem_insert_of_mem j.2))
    have hG : (⋂ j ∈ T', (fun ω => φ j (fun i : S j => f i ω)) ⁻¹' sets j) = tU ⁻¹' G' := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_preimage, G', Subtype.forall]
      rfl
    have hF : ((fun ω => φ j₀ (fun i : S j₀ => f i ω)) ⁻¹' sets j₀) =
        tS ⁻¹' (φ j₀ ⁻¹' sets j₀) := rfl
    rw [hG, hF, hind.measure_inter_preimage_eq_mul _ _
      ((hφ j₀) (hsets j₀ (Finset.mem_insert_self _ _))) hG'meas, ← hG, ← hF,
      ih (fun j hj => hsets j (Finset.mem_insert_of_mem hj))]

end Finsets

/-! ### Sums of independent Poisson counts -/

section PoissonSum

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Binomial identity behind the Poisson convolution. -/
theorem sum_poisTerm_mul_poisTerm (a b : ℝ) (k : ℕ) :
    ∑ m ∈ range (k + 1), poisTerm m a * poisTerm (k - m) b = poisTerm k (a + b) := by
  unfold poisTerm
  rw [add_pow, neg_add, Real.exp_add, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hchoose : (k.choose m : ℝ) * (m.factorial * (k - m).factorial) = k.factorial := by
    rw [← mul_assoc]
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hmk
  have hm0 : (0:ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hkm0 : (0:ℝ) < (k - m).factorial := by exact_mod_cast Nat.factorial_pos (k - m)
  have hk0 : (0:ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity), ← hchoose]
  ring

/-- **Sum of two independent Poisson counts** (point masses). -/
theorem poisson_add_masses {X Y : Ω → ℕ} (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hXl : ∀ k, P {ω | X ω = k} = ENNReal.ofReal (poisTerm k a))
    (hYl : ∀ k, P {ω | Y ω = k} = ENNReal.ofReal (poisTerm k b)) (k : ℕ) :
    P {ω | X ω + Y ω = k} = ENNReal.ofReal (poisTerm k (a + b)) := by
  have hset : {ω | X ω + Y ω = k} =
      ⋃ m ∈ Finset.range (k + 1), ({ω | X ω = m} ∩ {ω | Y ω = k - m}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Finset.mem_range, exists_prop]
    constructor
    · intro h
      exact ⟨X ω, by omega, rfl, by omega⟩
    · rintro ⟨m, hm, h1, h2⟩
      omega
  have hdisj : (↑(Finset.range (k + 1)) : Set ℕ).PairwiseDisjoint
      (fun m => {ω | X ω = m} ∩ {ω | Y ω = k - m}) := by
    intro m _ m' _ hne
    refine Set.disjoint_left.mpr fun ω h h' => hne ?_
    rw [← h.1, ← h'.1]
  have hmeas : ∀ m ∈ Finset.range (k + 1), MeasurableSet ({ω | X ω = m} ∩ {ω | Y ω = k - m}) := by
    intro m _
    have h1 : {ω | X ω = m} = X ⁻¹' {m} := rfl
    have h2 : {ω | Y ω = k - m} = Y ⁻¹' {k - m} := rfl
    rw [h1, h2]
    exact (hX (measurableSet_singleton _)).inter (hY (measurableSet_singleton _))
  rw [hset, measure_biUnion_finset hdisj hmeas]
  have hterm : ∀ m ∈ Finset.range (k + 1), P ({ω | X ω = m} ∩ {ω | Y ω = k - m}) =
      ENNReal.ofReal (poisTerm m a * poisTerm (k - m) b) := by
    intro m _
    have h1 : {ω | X ω = m} = X ⁻¹' {m} := rfl
    have h2 : {ω | Y ω = k - m} = Y ⁻¹' {k - m} := rfl
    rw [h1, h2, hXY.measure_inter_preimage_eq_mul _ _ (measurableSet_singleton _)
      (measurableSet_singleton _), ← h1, ← h2, hXl, hYl,
      ENNReal.ofReal_mul (poisTerm_nonneg _ ha)]
  rw [Finset.sum_congr rfl hterm, ← ENNReal.ofReal_sum_of_nonneg
    (fun m _ => mul_nonneg (poisTerm_nonneg _ ha) (poisTerm_nonneg _ hb)),
    sum_poisTerm_mul_poisTerm]

/-- **Sum of finitely many independent Poisson counts** (point masses). -/
theorem poisson_sum_masses [IsProbabilityMeasure P] {X : ℕ → Ω → ℕ} (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) {lam : ℕ → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (hl : ∀ i k, P {ω | X i ω = k} = ENNReal.ofReal (poisTerm k (lam i))) (K k : ℕ) :
    P {ω | ∑ i ∈ range K, X i ω = k} = ENNReal.ofReal (poisTerm k (∑ i ∈ range K, lam i)) := by
  induction K generalizing k with
  | zero =>
    simp only [Finset.sum_range_zero]
    rcases k with _ | k
    · simp [poisTerm]
    · simp [poisTerm]
  | succ K ih =>
    simp_rw [Finset.sum_range_succ]
    have hind' : IndepFun (fun ω => ∑ i ∈ range K, X i ω) (X K) P := by
      have h := hind.indepFun_finsetSum_of_notMem hX (s := range K) (i := K) (by simp)
      have hfun : (∑ i ∈ range K, X i) = fun ω => ∑ i ∈ range K, X i ω := by
        funext ω
        exact Finset.sum_apply _ _ _
      rw [hfun] at h
      exact h
    exact poisson_add_masses (Finset.measurable_sum _ fun i _ => hX i) (hX K) hind'
      (Finset.sum_nonneg fun i _ => hlam i) (hlam K) ih (hl K) k

end PoissonSum

end Ripple.Kurtz.StrongApprox
