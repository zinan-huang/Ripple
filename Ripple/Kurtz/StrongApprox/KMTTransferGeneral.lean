-- Ripple/Kurtz/StrongApprox/KMTTransferGeneral.lean
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.Kernel.IndepFun
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.InfinitePi

/-!
# General tools for the KMT transfer to a prescribed Brownian family

* `map_compProd_comap`: the composition product `P ⊗ₘ κ.comap b` pushes forward to
  `P.map b ⊗ₘ κ` under `(b z.1, z.2)`.
* `independentPi κ`: the Markov kernel `b ↦ ⨂ j, κ (b j)` on a product of coordinates.
* `iIndepFun_pairs_of_independent_marking`: independent base variables stay independent
  after conditionally independent coordinatewise marking.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Ripple.Kurtz.StrongApprox.KMTTransferGeneral

section CompProdComap

variable {Ω B C : Type*} [MeasurableSpace Ω] [MeasurableSpace B] [MeasurableSpace C]

theorem map_compProd_comap (P : Measure Ω) [SFinite P]
    (κ : Kernel B C) [IsMarkovKernel κ] (b : Ω → B) (hb : Measurable b) :
    (P ⊗ₘ Kernel.comap κ b hb).map (fun z : Ω × C => (b z.1, z.2)) = P.map b ⊗ₘ κ := by
  have hm : Measurable (fun z : Ω × C => (b z.1, z.2)) :=
    (hb.comp measurable_fst).prodMk measurable_snd
  ext s hs
  rw [Measure.map_apply hm hs, Measure.compProd_apply (hm hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hb]
  simp only [Kernel.comap_apply]
  rfl

end CompProdComap

section IndependentPi

variable {B C J : Type*} [MeasurableSpace B] [MeasurableSpace C]

theorem measurable_pi_family {K : Type*} [Fintype K]
    (κ : Kernel B C) [IsMarkovKernel κ] :
    Measurable (fun x : K → B => Measure.pi fun k => κ (x k)) := by
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_pi.symm isPiSystem_pi ?_
  rintro _ ⟨t, ht, rfl⟩
  have ht' : ∀ k, MeasurableSet (t k) := fun k => ht k (mem_univ k)
  have h : (fun x : K → B => (Measure.pi fun k => κ (x k)) (Set.univ.pi t)) =
      fun x => ∏ k, κ (x k) (t k) := funext fun x => Measure.pi_pi _ _
  rw [h]
  exact Finset.measurable_prod _ fun k _ => (κ.measurable_coe (ht' k)).comp (measurable_pi_apply k)

theorem measurable_infinitePi_family (κ : Kernel B C) [IsMarkovKernel κ] :
    Measurable (fun x : J → B => Measure.infinitePi fun j => κ (x j)) := by
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_
  intro A hA
  obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders A).1 hA
  have h : (fun x : J → B => (Measure.infinitePi fun j => κ (x j)) (cylinder s S)) =
      fun x => (Measure.pi fun i : s => κ (x i)) S :=
    funext fun x => Measure.infinitePi_cylinder _ hS
  rw [h]
  exact (Measure.measurable_coe hS).comp
    ((measurable_pi_family (K := s) κ).comp (measurable_pi_lambda _ fun i : s => measurable_pi_apply (i : J)))

/-- The countable product kernel `b ↦ ⨂ j, κ (b j)`. -/
def independentPi (J : Type*) (κ : Kernel B C) [IsMarkovKernel κ] :
    Kernel (J → B) (J → C) where
  toFun x := Measure.infinitePi fun j => κ (x j)
  measurable' := measurable_infinitePi_family κ

instance (κ : Kernel B C) [IsMarkovKernel κ] : IsMarkovKernel (independentPi J κ) :=
  ⟨fun x => by
    change IsProbabilityMeasure (Measure.infinitePi fun j => κ (x j))
    infer_instance⟩

theorem independentPi_apply (κ : Kernel B C) [IsMarkovKernel κ] (b : J → B) :
    independentPi J κ b = Measure.infinitePi fun j => κ (b j) := rfl

theorem independentPi_map_eval (κ : Kernel B C) [IsMarkovKernel κ] (b : J → B) (j : J) :
    (independentPi J κ b).map (fun c => c j) = κ (b j) := by
  rw [independentPi_apply]
  exact Measure.infinitePi_map_eval _ j

theorem independentPi_eval_iIndep (κ : Kernel B C) [IsMarkovKernel κ] (ν : Measure (J → B)) :
    Kernel.iIndepFun (fun (j : J) (c : J → C) => c j) (independentPi J κ) ν := by
  rw [Kernel.iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  refine Filter.Eventually.of_forall fun b => ?_
  have h := (iIndepFun_iff_measure_inter_preimage_eq_mul.mp
    (iIndepFun_infinitePi (P := fun j => κ (b j)) (X := fun j (c : C) => c)
      (fun j => measurable_id))) S hsets
  exact h

end IndependentPi


section Marking

variable {Ω B C J ι : Type*} [MeasurableSpace Ω] [MeasurableSpace B] [MeasurableSpace C]

/-- An infinite product, read on an injective finite family of coordinates. -/
theorem infinitePi_map_comp_injective [Fintype ι] (ν : J → Measure C)
    [∀ j, IsProbabilityMeasure (ν j)] (e : ι → J) (he : Function.Injective e) :
    (Measure.infinitePi ν).map (fun c i => c (e i)) = Measure.pi fun i => ν (e i) := by
  have hind : iIndepFun (fun (i : ι) (c : J → C) => c (e i)) (Measure.infinitePi ν) :=
    (iIndepFun_infinitePi (P := ν) (X := fun j (c : C) => c) (fun j => measurable_id)).precomp he
  rw [hind.map_fun_eq_pi_map (fun i => (measurable_pi_apply (e i)).aemeasurable)]
  congr 1
  funext i
  exact Measure.infinitePi_map_eval ν (e i)

variable (P : Measure Ω) [IsProbabilityMeasure P] (κ : Kernel B C) [IsMarkovKernel κ]
  (b : Ω → J → B) (e : ι → J)

/-- The pair family `(b z.1 (e i), z.2 (e i))` on the marked space. -/
def markedPair (z : Ω × (J → C)) : ι → B × C := fun i => (b z.1 (e i), z.2 (e i))

theorem measurable_markedPair (hb : Measurable b) :
    Measurable (markedPair b e : Ω × (J → C) → ι → B × C) := by
  refine measurable_pi_lambda _ fun i => ?_
  exact ((measurable_pi_apply (e i)).comp (hb.comp measurable_fst)).prodMk
    ((measurable_pi_apply (e i)).comp measurable_snd)

/-- Box formula for the marked pairs. -/
theorem marking_box [Fintype ι] (hb : Measurable b) (he : Function.Injective e)
    (hX : iIndepFun (fun (i : ι) ω => b ω (e i)) P)
    (t : ι → Set (B × C)) (ht : ∀ i, MeasurableSet (t i)) :
    (P ⊗ₘ Kernel.comap (independentPi J κ) b hb) (markedPair b e ⁻¹' Set.univ.pi t) =
      ∏ i, (P.map (fun ω => b ω (e i)) ⊗ₘ κ) (t i) := by
  have hZ := measurable_markedPair (C := C) b e hb
  have hmeas : ∀ i, Measurable (fun ω => b ω (e i)) := fun i =>
    (measurable_pi_apply (e i)).comp hb
  rw [Measure.compProd_apply (hZ (MeasurableSet.univ_pi ht))]
  have inner : ∀ ω, (Kernel.comap (independentPi J κ) b hb) ω
      (Prod.mk ω ⁻¹' (markedPair b e ⁻¹' Set.univ.pi t)) =
      ∏ i, κ (b ω (e i)) (Prod.mk (b ω (e i)) ⁻¹' t i) := by
    intro ω
    rw [Kernel.comap_apply, independentPi_apply]
    have hset : Prod.mk ω ⁻¹' (markedPair b e ⁻¹' Set.univ.pi t) =
        (fun c : J → C => fun i => c (e i)) ⁻¹'
          Set.univ.pi (fun i => Prod.mk (b ω (e i)) ⁻¹' t i) := by
      ext c
      simp [markedPair]
    have hm : Measurable (fun c : J → C => fun i : ι => c (e i)) :=
      measurable_pi_lambda _ fun i => measurable_pi_apply (e i)
    have hs : MeasurableSet (Set.univ.pi (fun i => Prod.mk (b ω (e i)) ⁻¹' t i)) :=
      MeasurableSet.univ_pi fun i => measurable_prodMk_left (ht i)
    rw [hset, ← Measure.map_apply hm hs, infinitePi_map_comp_injective _ e he, Measure.pi_pi]
  simp_rw [inner]
  set f : ι → B → ℝ≥0∞ := fun i x => κ x (Prod.mk x ⁻¹' t i) with hf
  have hfm : ∀ i, Measurable (f i) := fun i =>
    Kernel.measurable_kernel_prodMk_left (κ := κ) (ht i)
  have hind : iIndepFun (fun (i : ι) ω => f i (b ω (e i))) P :=
    hX.comp f hfm
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun i ω => f i (b ω (e i))) hind (fun i => (hfm i).comp (hmeas i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Measure.compProd_apply (ht i), lintegral_map (hfm i) (hmeas i)]

/-- Independent base variables remain independent after conditionally independent
coordinatewise marking. -/
theorem iIndepFun_pairs_of_independent_marking [Fintype ι] (hb : Measurable b) (he : Function.Injective e)
    (hX : iIndepFun (fun (i : ι) ω => b ω (e i)) P) :
    iIndepFun (fun (i : ι) (z : Ω × (J → C)) => (b z.1 (e i), z.2 (e i)))
      (P ⊗ₘ Kernel.comap (independentPi J κ) b hb) := by
  classical
  have hmeas : ∀ i, Measurable (fun ω => b ω (e i)) := fun i =>
    (measurable_pi_apply (e i)).comp hb
  haveI : ∀ i, IsProbabilityMeasure (P.map (fun ω => b ω (e i)) ⊗ₘ κ) := fun i => by
    haveI : IsProbabilityMeasure (P.map (fun ω => b ω (e i))) :=
      Measure.isProbabilityMeasure_map (hmeas i).aemeasurable
    infer_instance
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  let t : ι → Set (B × C) := fun i => if i ∈ S then sets i else Set.univ
  have ht : ∀ i, MeasurableSet (t i) := fun i => by
    by_cases hi : i ∈ S
    · simp only [t, hi, if_true]; exact hsets i hi
    · simp [t, hi]
  have h1 : (⋂ i ∈ S, (fun (z : Ω × (J → C)) => (b z.1 (e i), z.2 (e i))) ⁻¹' sets i) =
      markedPair b e ⁻¹' Set.univ.pi t := by
    ext z
    simp only [mem_iInter, mem_preimage, mem_pi, mem_univ, true_implies, markedPair, t]
    constructor
    · intro h i
      by_cases hi : i ∈ S
      · simpa [hi] using h i hi
      · simp [hi]
    · intro h i hi
      simpa [hi] using h i
  rw [h1, marking_box P κ b e hb he hX t ht]
  have h2 : ∀ i ∈ S, (P ⊗ₘ Kernel.comap (independentPi J κ) b hb)
      ((fun (z : Ω × (J → C)) => (b z.1 (e i), z.2 (e i))) ⁻¹' sets i) =
      (P.map (fun ω => b ω (e i)) ⊗ₘ κ) (sets i) := by
    intro i hi
    let t' : ι → Set (B × C) := fun j => if j = i then sets i else Set.univ
    have ht' : ∀ j, MeasurableSet (t' j) := fun j => by
      by_cases hj : j = i
      · simp only [t', hj, if_true]; exact hsets i hi
      · simp [t', hj]
    have h3 : ((fun (z : Ω × (J → C)) => (b z.1 (e i), z.2 (e i))) ⁻¹' sets i) =
        markedPair b e ⁻¹' Set.univ.pi t' := by
      ext z
      simp only [mem_preimage, mem_pi, mem_univ, true_implies, markedPair, t']
      constructor
      · intro h j
        by_cases hj : j = i
        · subst hj; simpa using h
        · simp [hj]
      · intro h
        simpa using h i
    rw [h3, marking_box P κ b e hb he hX t' ht']
    rw [Finset.prod_eq_single i]
    · simp [t']
    · intro j _ hj
      simp [t', hj]
    · intro hi'
      exact absurd (Finset.mem_univ i) hi'
  rw [Finset.prod_congr rfl h2]
  rw [← Finset.prod_subset (Finset.subset_univ S) (fun i _ hi => by simp [t, hi])]
  exact Finset.prod_congr rfl fun i hi => by simp [t, hi]

/-- Coordinatewise joint law of the marked space. -/
theorem map_marked_coord (hb : Measurable b) (j : J) :
    (P ⊗ₘ Kernel.comap (independentPi J κ) b hb).map
        (fun z : Ω × (J → C) => (b z.1 j, z.2 j)) =
      P.map (fun ω => b ω j) ⊗ₘ κ := by
  have hbj : Measurable (fun ω => b ω j) := (measurable_pi_apply j).comp hb
  have hm : Measurable (fun z : Ω × (J → C) => (b z.1 j, z.2 j)) :=
    (hbj.comp measurable_fst).prodMk ((measurable_pi_apply j).comp measurable_snd)
  ext s hs
  rw [Measure.map_apply hm hs, Measure.compProd_apply (hm hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hbj]
  refine lintegral_congr fun ω => ?_
  rw [Kernel.comap_apply]
  have h : Prod.mk ω ⁻¹' ((fun z : Ω × (J → C) => (b z.1 j, z.2 j)) ⁻¹' s) =
      (fun c : J → C => c j) ⁻¹' (Prod.mk (b ω j) ⁻¹' s) := rfl
  rw [h, ← Measure.map_apply (measurable_pi_apply j) (measurable_prodMk_left hs),
    independentPi_map_eval]

/-- The marked space has conditional law `independentPi κ` given the base array. -/
theorem condDistrib_marking [Countable J] [StandardBorelSpace C] [Nonempty C]
    (hb : Measurable b) :
    condDistrib Prod.snd (fun z : Ω × (J → C) => b z.1)
        (P ⊗ₘ Kernel.comap (independentPi J κ) b hb)
      =ᵐ[(P ⊗ₘ Kernel.comap (independentPi J κ) b hb).map (fun z => b z.1)]
        independentPi J κ := by
  have h1 : (P ⊗ₘ Kernel.comap (independentPi J κ) b hb).map (fun z => b z.1) = P.map b := by
    have h : (P ⊗ₘ Kernel.comap (independentPi J κ) b hb).map (fun z => b z.1) =
        ((P ⊗ₘ Kernel.comap (independentPi J κ) b hb).fst).map b := by
      rw [Measure.fst, Measure.map_map hb measurable_fst]
      rfl
    rw [h, Measure.fst_compProd]
  refine condDistrib_ae_eq_of_measure_eq_compProd (κ := independentPi J κ) (μ := P ⊗ₘ Kernel.comap (independentPi J κ) b hb) (fun z => b z.1)
    (measurable_snd (α := Ω) (β := J → C)).aemeasurable ?_
  rw [h1]
  exact map_compProd_comap P (independentPi J κ) b hb

/-- Reading one marked coordinate together with the base point is the single-coordinate
composition product. -/
theorem map_marked_coord_comap (hb : Measurable b) (j : J) :
    (P ⊗ₘ Kernel.comap (independentPi J κ) b hb).map
        (fun z : Ω × (J → C) => (z.1, z.2 j)) =
      P ⊗ₘ Kernel.comap κ (fun ω => b ω j) ((measurable_pi_apply j).comp hb) := by
  have hm : Measurable (fun z : Ω × (J → C) => (z.1, z.2 j)) :=
    measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd)
  ext s hs
  rw [Measure.map_apply hm hs, Measure.compProd_apply (hm hs), Measure.compProd_apply hs]
  refine lintegral_congr fun ω => ?_
  rw [Kernel.comap_apply, Kernel.comap_apply]
  have h : Prod.mk ω ⁻¹' ((fun z : Ω × (J → C) => (z.1, z.2 j)) ⁻¹' s) =
      (fun c : J → C => c j) ⁻¹' (Prod.mk ω ⁻¹' s) := rfl
  rw [h, ← Measure.map_apply (measurable_pi_apply j) (measurable_prodMk_left hs),
    independentPi_map_eval]

end Marking

end Ripple.Kurtz.StrongApprox.KMTTransferGeneral
