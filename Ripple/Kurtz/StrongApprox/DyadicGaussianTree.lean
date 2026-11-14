-- Ripple/Kurtz/StrongApprox/DyadicGaussianTree.lean
import Mathlib
import Ripple.Kurtz.StrongApprox.GaussianBlockSum

/-!
# The finite dyadic Gaussian tree

The source at depth `r` contains one distinguished endpoint normal and one split
normal for every parent strictly above level `r`.  In particular, the endpoint
normal and the split normal of the whole interval are distinct.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox.DyadicGaussianTree

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal
open Ripple.Kurtz.StrongApprox

/-- Level-zero has one cell; each refinement has a left and a right copy. -/
def DyadicCell : ℕ → Type
  | 0 => Unit
  | r + 1 => DyadicCell r ⊕ DyadicCell r

instance dyadicCellFintype (r : ℕ) : Fintype (DyadicCell r) := by
  induction r with
  | zero =>
      change Fintype Unit
      infer_instance
  | succ r ih =>
      change Fintype (DyadicCell r ⊕ DyadicCell r)
      letI : Fintype (DyadicCell r) := ih
      infer_instance

/-- One endpoint normal at depth zero; at the next depth add one normal per old cell. -/
def DyadicNoise : ℕ → Type
  | 0 => Unit
  | r + 1 => DyadicNoise r ⊕ DyadicCell r

instance dyadicNoiseFintype (r : ℕ) : Fintype (DyadicNoise r) := by
  induction r with
  | zero =>
      change Fintype Unit
      infer_instance
  | succ r ih =>
      change Fintype (DyadicNoise r ⊕ DyadicCell r)
      letI : Fintype (DyadicNoise r) := ih
      infer_instance

abbrev DyadicNoiseSpace (r : ℕ) := DyadicNoise r → ℝ
abbrev DyadicFreshSpace (r : ℕ) := DyadicCell r → ℝ

noncomputable def dyadicNoiseMeasure (r : ℕ) : Measure (DyadicNoiseSpace r) :=
  Measure.pi fun _ : DyadicNoise r => gaussianReal 0 1

noncomputable def dyadicFreshMeasure (r : ℕ) : Measure (DyadicFreshSpace r) :=
  Measure.pi fun _ : DyadicCell r => gaussianReal 0 1

instance dyadicNoiseMeasure_isProbabilityMeasure (r : ℕ) :
    IsProbabilityMeasure (dyadicNoiseMeasure r) := by
  unfold dyadicNoiseMeasure
  infer_instance

instance dyadicFreshMeasure_isProbabilityMeasure (r : ℕ) :
    IsProbabilityMeasure (dyadicFreshMeasure r) := by
  unfold dyadicFreshMeasure
  infer_instance

/-- Split a depth-`r+1` source into the old source and the fresh split normals. -/
noncomputable def dyadicNoiseSplit (r : ℕ) :
    DyadicNoiseSpace (r + 1) ≃ᵐ DyadicNoiseSpace r × DyadicFreshSpace r := by
  change ((DyadicNoise r ⊕ DyadicCell r) → ℝ) ≃ᵐ
    (DyadicNoise r → ℝ) × (DyadicCell r → ℝ)
  exact MeasurableEquiv.sumPiEquivProdPi
    (fun _ : DyadicNoise r ⊕ DyadicCell r => ℝ)

/-- The source split is measure preserving. -/
theorem dyadicNoiseSplit_measurePreserving (r : ℕ) :
    MeasurePreserving (dyadicNoiseSplit r) (dyadicNoiseMeasure (r + 1))
      ((dyadicNoiseMeasure r).prod (dyadicFreshMeasure r)) := by
  simpa [dyadicNoiseSplit, dyadicNoiseMeasure, dyadicFreshMeasure, DyadicNoise] using
    (measurePreserving_sumPiEquivProdPi
      (X := fun _ : DyadicNoise r ⊕ DyadicCell r => ℝ)
      (fun _ => gaussianReal 0 1))

/-- Forget the last `d` generations of split normals. -/
noncomputable def dyadicNoiseRestrict : (r d : ℕ) →
    DyadicNoiseSpace (r + d) → DyadicNoiseSpace r
  | r, 0 => id
  | r, d + 1 =>
      dyadicNoiseRestrict r d ∘
        (fun x => (dyadicNoiseSplit (r + d) x).1)

/-- Restriction of the finite product source preserves its smaller product law. -/
theorem dyadicNoiseRestrict_measurePreserving : ∀ r d,
    MeasurePreserving (dyadicNoiseRestrict r d) (dyadicNoiseMeasure (r + d))
      (dyadicNoiseMeasure r)
  | r, 0 => by
      simpa [dyadicNoiseRestrict] using
        (MeasurePreserving.id (dyadicNoiseMeasure r))
  | r, d + 1 => by
      have hdrop : MeasurePreserving (fun p : DyadicNoiseSpace (r + d) ×
          DyadicFreshSpace (r + d) => p.1)
          ((dyadicNoiseMeasure (r + d)).prod (dyadicFreshMeasure (r + d)))
          (dyadicNoiseMeasure (r + d)) := measurePreserving_fst
      have h := (dyadicNoiseRestrict_measurePreserving r d).comp
        (hdrop.comp (dyadicNoiseSplit_measurePreserving (r + d)))
      simpa [dyadicNoiseRestrict, Function.comp_def] using h

/-! ## A generic binary refinement lemma -/

/-- Convert a family of pairs into a function on `left indices ⊕ right indices`. -/
noncomputable def dyadicChildrenEquiv (ι D : Type*) [Fintype ι] [MeasurableSpace D] :
    (ι → D × D) ≃ᵐ (ι ⊕ ι → D) :=
  (MeasurableEquiv.arrowProdEquivProdArrow D D ι).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ ι => D)).symm

/-- The preceding rearrangement preserves a product of identical laws. -/
theorem dyadicChildrenEquiv_measurePreserving
    {ι D : Type*} [Fintype ι] [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] :
    MeasurePreserving (dyadicChildrenEquiv ι D)
      (Measure.pi fun _ : ι => μ.prod μ)
      (Measure.pi fun _ : ι ⊕ ι => μ) := by
  exact (measurePreserving_arrowProdEquivProdArrow D D ι
    (fun _ => μ) (fun _ => μ)).trans
      (measurePreserving_sumPiEquivProdPi_symm
        (X := fun _ : ι ⊕ ι => D) (fun _ => μ))

/-- Apply one binary split independently to every parent. -/
def dyadicRefine {ι A B D : Type*} [Fintype ι]
    (split : A × B → D × D) (p : (ι → A) × (ι → B)) : ι ⊕ ι → D
  | Sum.inl i => (split (p.1 i, p.2 i)).1
  | Sum.inr i => (split (p.1 i, p.2 i)).2

/-- Product-law induction for a binary refinement. -/
theorem dyadicRefine_measurePreserving
    {ι A B D : Type*} [Fintype ι]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace D]
    {μA : Measure A} {μB : Measure B} {μD : Measure D}
    [IsProbabilityMeasure μA] [IsProbabilityMeasure μB] [IsProbabilityMeasure μD]
    {split : A × B → D × D} (hsplit : Measurable split)
    (hlaw : (μA.prod μB).map split = μD.prod μD) :
    MeasurePreserving (dyadicRefine split)
      ((Measure.pi fun _ : ι => μA).prod (Measure.pi fun _ : ι => μB))
      (Measure.pi fun _ : ι ⊕ ι => μD) := by
  let zip := (MeasurableEquiv.arrowProdEquivProdArrow A B ι).symm
  have hzip : MeasurePreserving zip
      ((Measure.pi fun _ : ι => μA).prod (Measure.pi fun _ : ι => μB))
      (Measure.pi fun _ : ι => μA.prod μB) :=
    MeasurePreserving.symm _
      (measurePreserving_arrowProdEquivProdArrow A B ι
        (fun _ => μA) (fun _ => μB))
  have hcoord : MeasurePreserving (fun x : ι → A × B => fun i => split (x i))
      (Measure.pi fun _ : ι => μA.prod μB)
      (Measure.pi fun _ : ι => μD.prod μD) := by
    refine ⟨by fun_prop, ?_⟩
    rw [Measure.pi_map_pi (fun _ => hsplit.aemeasurable)]
    simp_rw [hlaw]
  have hchildren := dyadicChildrenEquiv_measurePreserving (ι := ι) (D := D) μD
  have h := hchildren.comp (hcoord.comp hzip)
  change MeasurePreserving
    ((dyadicChildrenEquiv ι D) ∘
      (fun x : ι → A × B => fun i => split (x i)) ∘ zip)
      _ _ at h
  have hfun : ((dyadicChildrenEquiv ι D) ∘
      (fun x : ι → A × B => fun i => split (x i)) ∘ zip) = dyadicRefine split := by
    funext p c
    cases c <;> rfl
  rw [hfun] at h
  exact h

/-- A coordinate law follows from a finite vector law. -/
theorem vectorComponent_map_eq
    {Ω ι D : Type*} [MeasurableSpace Ω] [Fintype ι] [MeasurableSpace D]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {μ : ι → Measure D} [∀ i, IsProbabilityMeasure (μ i)]
    {X : Ω → ι → D} (hX : Measurable X)
    (hlaw : P.map X = Measure.pi μ) (i : ι) :
    P.map (fun ω => X ω i) = μ i := by
  rw [show (fun ω => X ω i) = (fun x : ι → D => x i) ∘ X by rfl,
    ← Measure.map_map (measurable_pi_apply i) hX, hlaw]
  exact (measurePreserving_eval μ i).map_eq

/-- A finite vector law equal to a product law implies coordinate independence. -/
theorem iIndepFun_of_vector_map_eq_pi
    {Ω ι D : Type*} [MeasurableSpace Ω] [Fintype ι] [MeasurableSpace D]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {μ : ι → Measure D} [∀ i, IsProbabilityMeasure (μ i)]
    {X : Ω → ι → D} (hX : Measurable X)
    (hlaw : P.map X = Measure.pi μ) :
    iIndepFun (fun i ω => X ω i) P := by
  rw [iIndepFun_iff_map_fun_eq_pi_map (f := fun i ω => X ω i)
    (fun i => (((measurable_pi_apply i).comp hX).aemeasurable :
      AEMeasurable (fun ω => X ω i) P))]
  have hc : ∀ i, P.map (fun ω => X ω i) = μ i :=
    vectorComponent_map_eq hX hlaw
  simp_rw [hc]
  simpa using hlaw

/-! ## Lengths and the one-parent Gaussian rotation -/

/-- The variance/cell length at level `r` of a horizon-`2^K` tree. -/
def dyadicVariance (K r : ℕ) : ℝ≥0 :=
  ⟨(2 : ℝ) ^ K / (2 : ℝ) ^ r, by positivity⟩

@[simp] theorem dyadicVariance_succ (K r : ℕ) :
    dyadicVariance K (r + 1) = dyadicVariance K r / 2 := by
  apply NNReal.coe_injective
  change (2 : ℝ) ^ K / (2 : ℝ) ^ (r + 1) =
    ((2 : ℝ) ^ K / (2 : ℝ) ^ r) / 2
  rw [pow_succ]
  field_simp

@[simp] theorem dyadicVariance_self (K : ℕ) : dyadicVariance K K = 1 := by
  apply NNReal.coe_injective
  change (2 : ℝ) ^ K / (2 : ℝ) ^ K = 1
  exact div_self (by positivity)

theorem dyadicVariance_pos (K r : ℕ) : 0 < (dyadicVariance K r : ℝ) := by
  change 0 < (2 : ℝ) ^ K / (2 : ℝ) ^ r
  positivity

/-- Scaling a standard normal by `sqrt v` gives variance `v`. -/
theorem gaussianReal_map_sqrt_mul (v : ℝ≥0) :
    (gaussianReal 0 1).map (fun z : ℝ => Real.sqrt (v : ℝ) * z) =
      gaussianReal 0 v := by
  rw [gaussianReal_map_const_mul]
  simp only [mul_zero]
  congr 1
  apply NNReal.coe_injective
  simp [Real.sq_sqrt v.coe_nonneg]

/-- The average/difference linear map. -/
noncomputable def gaussianPairAverage : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  ((2 : ℝ)⁻¹ • (ContinuousLinearMap.fst ℝ ℝ ℝ +
    ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
  ((2 : ℝ)⁻¹ • (ContinuousLinearMap.fst ℝ ℝ ℝ -
    ContinuousLinearMap.snd ℝ ℝ ℝ))

@[simp] theorem gaussianPairAverage_apply (p : ℝ × ℝ) :
    gaussianPairAverage p = ((p.1 + p.2) / 2, (p.1 - p.2) / 2) := by
  ext <;> simp [gaussianPairAverage, div_eq_mul_inv] <;> ring

/-- Split a `N(0,v)` parent increment using an independent standard normal. -/
noncomputable def gaussianHalfSplit (v : ℝ≥0) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((p.1 + Real.sqrt (v : ℝ) * p.2) / 2,
    (p.1 - Real.sqrt (v : ℝ) * p.2) / 2)

@[fun_prop] theorem measurable_gaussianHalfSplit (v : ℝ≥0) :
    Measurable (gaussianHalfSplit v) := by
  unfold gaussianHalfSplit
  fun_prop

/-- Abstract form of the one-parent step: for independent `N(0,v)` variables
`G`, `A`, the half sum and half difference are independent `N(0,v/2)`. -/
theorem gaussian_half_pair_map
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {G A : Ω → ℝ} {v : ℝ≥0}
    (hGm : Measurable G) (hAm : Measurable A)
    (hGmap : P.map G = gaussianReal 0 v) (hAmap : P.map A = gaussianReal 0 v)
    (hGA : IndepFun G A P) :
    P.map (fun p => ((G p + A p) / 2, (G p - A p) / 2)) =
      (gaussianReal 0 (v / 2)).prod (gaussianReal 0 (v / 2)) := by
  have hLm : Measurable (fun p => (G p + A p) / 2) :=
    (hGm.add hAm).div_const 2
  have hRm : Measurable (fun p => (G p - A p) / 2) :=
    (hGm.sub hAm).div_const 2
  have hGlaw : HasLaw G (gaussianReal 0 v) P := ⟨hGm.aemeasurable, hGmap⟩
  have hAlaw : HasLaw A (gaussianReal 0 v) P := ⟨hAm.aemeasurable, hAmap⟩
  have hJointGA : HasGaussianLaw (fun p => (G p, A p)) P :=
    IndepFun.hasGaussianLaw hGlaw.hasGaussianLaw hAlaw.hasGaussianLaw hGA
  have hJointLR : HasGaussianLaw
      (fun p => ((G p + A p) / 2, (G p - A p) / 2)) P := by
    simpa using hJointGA.map_fun gaussianPairAverage
  have hSumMap : P.map (G + A) = gaussianReal 0 (v + v) := by
    have h := gaussianReal_add_gaussianReal_of_indepFun hGA hGmap hAmap
    rwa [add_zero] at h
  have hLmap : P.map (fun p => (G p + A p) / 2) = gaussianReal 0 (v / 2) := by
    rw [show (fun p => (G p + A p) / 2) = (fun y : ℝ => y / 2) ∘ (G + A) by
      funext p; rfl,
      ← Measure.map_map (by fun_prop : Measurable fun y : ℝ => y / 2)
        (show Measurable (G + A) from hGm.add hAm), hSumMap,
      gaussianReal_map_div_const]
    simp only [zero_div]
    congr 1
    apply NNReal.coe_injective
    norm_num
    ring
  have hNegAmap : P.map (-A) = gaussianReal 0 v := by
    rw [show (-A) = (fun y : ℝ => -y) ∘ A by
      funext p; rfl,
      ← Measure.map_map measurable_neg hAm, hAmap, gaussianReal_map_neg]
    simp
  have hGAneg : IndepFun G (-A) P := by
    have h := hGA.comp measurable_id (measurable_neg : Measurable fun y : ℝ => -y)
    simpa [Function.comp_def] using h
  have hDiffMap : P.map (G - A) = gaussianReal 0 (v + v) := by
    simpa [sub_eq_add_neg] using
      gaussianReal_add_gaussianReal_of_indepFun hGAneg hGmap hNegAmap
  have hRmap : P.map (fun p => (G p - A p) / 2) = gaussianReal 0 (v / 2) := by
    rw [show (fun p => (G p - A p) / 2) = (fun y : ℝ => y / 2) ∘ (G - A) by
      funext p; rfl,
      ← Measure.map_map (by fun_prop : Measurable fun y : ℝ => y / 2)
        (show Measurable (G - A) from hGm.sub hAm), hDiffMap,
      gaussianReal_map_div_const]
    simp only [zero_div]
    congr 1
    apply NNReal.coe_injective
    norm_num
    ring
  have hGtwo : MemLp G 2 P := hGlaw.hasGaussianLaw.memLp_two
  have hAtwo : MemLp A 2 P := hAlaw.hasGaussianLaw.memLp_two
  have hCovGG : cov[G, G; P] = (v : ℝ) := by
    rw [covariance_self hGm.aemeasurable, hGlaw.variance_eq,
      variance_id_gaussianReal]
  have hCovAA : cov[A, A; P] = (v : ℝ) := by
    rw [covariance_self hAm.aemeasurable, hAlaw.variance_eq,
      variance_id_gaussianReal]
  have hCovGA : cov[G, A; P] = 0 := hGA.covariance_eq_zero hGtwo hAtwo
  have hCovAG : cov[A, G; P] = 0 := hGA.symm.covariance_eq_zero hAtwo hGtwo
  have hCovSumDiff' : cov[G + A, G - A; P] = 0 := by
    rw [covariance_add_left hGtwo hAtwo (hGtwo.sub hAtwo),
      covariance_sub_right hGtwo hGtwo hAtwo,
      covariance_sub_right hAtwo hGtwo hAtwo,
      hCovGG, hCovGA, hCovAG, hCovAA]
    ring
  have hCovSumDiff :
      cov[fun p => G p + A p, fun p => G p - A p; P] = 0 := hCovSumDiff'
  have hCovLR : cov[fun p => (G p + A p) / 2, fun p => (G p - A p) / 2; P] = 0 := by
    rw [covariance_fun_div_left, covariance_fun_div_right, hCovSumDiff]
    norm_num
  have hLRind : IndepFun (fun p => (G p + A p) / 2) (fun p => (G p - A p) / 2) P :=
    hJointLR.indepFun_of_covariance_eq_zero hCovLR
  rw [hLRind.map_prod_eq_prod_map_map hLm.aemeasurable hRm.aemeasurable,
    hLmap, hRmap]

/-- The one-parent Gaussian step. -/
theorem gaussianHalfSplit_measurePreserving (v : ℝ≥0) :
    MeasurePreserving (gaussianHalfSplit v)
      ((gaussianReal 0 v).prod (gaussianReal 0 1))
      ((gaussianReal 0 (v / 2)).prod (gaussianReal 0 (v / 2))) := by
  refine ⟨measurable_gaussianHalfSplit v, ?_⟩
  have hGmap : ((gaussianReal 0 v).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ => p.1) = gaussianReal 0 v :=
    (measurePreserving_fst :
      MeasurePreserving (fun p : ℝ × ℝ => p.1)
        ((gaussianReal 0 v).prod (gaussianReal 0 1))
        (gaussianReal 0 v)).map_eq
  have hZmap : ((gaussianReal 0 v).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ => p.2) = gaussianReal 0 1 :=
    (measurePreserving_snd :
      MeasurePreserving (fun p : ℝ × ℝ => p.2)
        ((gaussianReal 0 v).prod (gaussianReal 0 1))
        (gaussianReal 0 1)).map_eq
  have hAmap : ((gaussianReal 0 v).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ => Real.sqrt (v : ℝ) * p.2) = gaussianReal 0 v := by
    rw [show (fun p : ℝ × ℝ => Real.sqrt (v : ℝ) * p.2) =
        (fun z : ℝ => Real.sqrt (v : ℝ) * z) ∘ (fun p : ℝ × ℝ => p.2) by rfl,
      ← Measure.map_map
        (by fun_prop : Measurable fun z : ℝ => Real.sqrt (v : ℝ) * z)
        measurable_snd, hZmap, gaussianReal_map_const_mul]
    simp only [mul_zero]
    congr 1
    apply NNReal.coe_injective
    simp [Real.sq_sqrt v.coe_nonneg]
  have hGZ : IndepFun (fun p : ℝ × ℝ => p.1) (fun p : ℝ × ℝ => p.2)
      ((gaussianReal 0 v).prod (gaussianReal 0 1)) := by
    simpa using
      (indepFun_prod (μ := gaussianReal 0 v) (ν := gaussianReal 0 1)
        measurable_id measurable_id)
  have hGA : IndepFun (fun p : ℝ × ℝ => p.1)
      (fun p : ℝ × ℝ => Real.sqrt (v : ℝ) * p.2)
      ((gaussianReal 0 v).prod (gaussianReal 0 1)) := by
    have h := hGZ.comp measurable_id
      (by fun_prop : Measurable fun z : ℝ => Real.sqrt (v : ℝ) * z)
    simpa [Function.comp_def] using h
  exact gaussian_half_pair_map (G := fun p : ℝ × ℝ => p.1)
    (A := fun p : ℝ × ℝ => Real.sqrt (v : ℝ) * p.2)
    measurable_fst (by fun_prop) hGmap hAmap hGA

/-! ## The Gaussian increment tree -/

/-- Increments on every cell of a level. -/
noncomputable def gaussianLevel : (K r : ℕ) →
    DyadicNoiseSpace r → DyadicCell r → ℝ
  | K, 0 => fun x i => Real.sqrt (dyadicVariance K 0 : ℝ) * x i
  | K, r + 1 => fun x =>
      let old := (dyadicNoiseSplit r x).1
      let fresh := (dyadicNoiseSplit r x).2
      dyadicRefine (gaussianHalfSplit (dyadicVariance K r))
        (gaussianLevel K r old, fresh)

/-- Exact product law at every level. -/
theorem gaussianLevel_measurePreserving (K : ℕ) : ∀ r,
    MeasurePreserving (gaussianLevel K r) (dyadicNoiseMeasure r)
      (Measure.pi fun _ : DyadicCell r => gaussianReal 0 (dyadicVariance K r))
  | 0 => by
      refine ⟨?_, ?_⟩
      · change Measurable (fun (x : DyadicNoiseSpace 0) (i : DyadicCell 0) =>
          Real.sqrt (dyadicVariance K 0 : ℝ) * x i)
        exact measurable_pi_lambda _ (fun i =>
          (measurable_pi_apply i).const_mul _)
      change (Measure.pi fun _ : Unit => gaussianReal 0 1).map
        (fun x i => Real.sqrt (dyadicVariance K 0 : ℝ) * x i) =
        Measure.pi fun _ : Unit => gaussianReal 0 (dyadicVariance K 0)
      rw [Measure.pi_map_pi (fun _ =>
        (by fun_prop : AEMeasurable
          (fun z : ℝ => Real.sqrt (dyadicVariance K 0 : ℝ) * z)
          (gaussianReal 0 1)))]
      simp_rw [gaussianReal_map_sqrt_mul]
  | r + 1 => by
      have hold := gaussianLevel_measurePreserving K r
      have hprod := MeasurePreserving.prod hold
        (MeasurePreserving.id (dyadicFreshMeasure r))
      have hrefine := dyadicRefine_measurePreserving
        (ι := DyadicCell r)
        (μA := gaussianReal 0 (dyadicVariance K r))
        (μB := gaussianReal 0 1)
        (μD := gaussianReal 0 (dyadicVariance K r / 2))
        (split := gaussianHalfSplit (dyadicVariance K r))
        (measurable_gaussianHalfSplit _)
        (gaussianHalfSplit_measurePreserving _).map_eq
      have h := hrefine.comp (hprod.comp (dyadicNoiseSplit_measurePreserving r))
      simpa [gaussianLevel, dyadicFreshMeasure, Function.comp_def,
        dyadicVariance_succ] using h

/-- Vector form of the exact level law. -/
theorem gaussianLevel_map (K r : ℕ) :
    (dyadicNoiseMeasure r).map (gaussianLevel K r) =
      Measure.pi fun _ : DyadicCell r => gaussianReal 0 (dyadicVariance K r) :=
  (gaussianLevel_measurePreserving K r).map_eq

/-- Every level-`r` increment is `N(0,2^K/2^r)`. -/
theorem gaussianLevel_component_map (K r : ℕ) (j : DyadicCell r) :
    (dyadicNoiseMeasure r).map (fun x => gaussianLevel K r x j) =
      gaussianReal 0 (dyadicVariance K r) :=
  vectorComponent_map_eq (gaussianLevel_measurePreserving K r).measurable
    (gaussianLevel_map K r) j

/-- The increments on a fixed level are independent. -/
theorem gaussianLevel_iIndep (K r : ℕ) :
    iIndepFun (fun j x => gaussianLevel K r x j) (dyadicNoiseMeasure r) :=
  iIndepFun_of_vector_map_eq_pi (gaussianLevel_measurePreserving K r).measurable
    (gaussianLevel_map K r)

/-- Level `r` of the horizon `2^(r+d)` tree, read on the single depth-`r+d` source. -/
noncomputable def gaussianLevelOnHorizon (r d : ℕ) :
    DyadicNoiseSpace (r + d) → DyadicCell r → ℝ :=
  gaussianLevel (r + d) r ∘ dyadicNoiseRestrict r d

/-- Exact product law for a coarser level on the full finite source. -/
theorem gaussianLevelOnHorizon_measurePreserving (r d : ℕ) :
    MeasurePreserving (gaussianLevelOnHorizon r d) (dyadicNoiseMeasure (r + d))
      (Measure.pi fun _ : DyadicCell r =>
        gaussianReal 0 (dyadicVariance (r + d) r)) := by
  simpa [gaussianLevelOnHorizon] using
    (gaussianLevel_measurePreserving (r + d) r).comp
      (dyadicNoiseRestrict_measurePreserving r d)

/-- Coarser-level increments remain independent on the common horizon source. -/
theorem gaussianLevelOnHorizon_iIndep (r d : ℕ) :
    iIndepFun (fun j x => gaussianLevelOnHorizon r d x j)
      (dyadicNoiseMeasure (r + d)) :=
  iIndepFun_of_vector_map_eq_pi
    (gaussianLevelOnHorizon_measurePreserving r d).measurable
    (gaussianLevelOnHorizon_measurePreserving r d).map_eq

/-! ## Dyadic endpoint values and the midpoint identity -/

/-- Left and right endpoint values of every cell. -/
noncomputable def gaussianEndpoints : (K r : ℕ) →
    DyadicNoiseSpace r → DyadicCell r → ℝ × ℝ
  | K, 0 => fun x i => (0, Real.sqrt (dyadicVariance K 0 : ℝ) * x i)
  | K, r + 1 => fun x c =>
      let old := (dyadicNoiseSplit r x).1
      let fresh := (dyadicNoiseSplit r x).2
      match c with
      | Sum.inl j =>
          let e := gaussianEndpoints K r old j
          let m := (e.1 + e.2) / 2 +
            Real.sqrt (dyadicVariance K r : ℝ) / 2 * fresh j
          (e.1, m)
      | Sum.inr j =>
          let e := gaussianEndpoints K r old j
          let m := (e.1 + e.2) / 2 +
            Real.sqrt (dyadicVariance K r : ℝ) / 2 * fresh j
          (m, e.2)

/-- The value inserted at the midpoint of parent `j`. -/
noncomputable def gaussianMidpoint (K r : ℕ)
    (x : DyadicNoiseSpace (r + 1)) (j : DyadicCell r) : ℝ :=
  let e := gaussianEndpoints K r (dyadicNoiseSplit r x).1 j
  (e.1 + e.2) / 2 +
    Real.sqrt (dyadicVariance K r : ℝ) / 2 * (dyadicNoiseSplit r x).2 j

/-- The midpoint formula is definitional. -/
theorem gaussianMidpoint_formula (K r : ℕ)
    (x : DyadicNoiseSpace (r + 1)) (j : DyadicCell r) :
    gaussianMidpoint K r x j =
      let e := gaussianEndpoints K r (dyadicNoiseSplit r x).1 j
      (e.1 + e.2) / 2 +
        Real.sqrt (dyadicVariance K r : ℝ) / 2 * (dyadicNoiseSplit r x).2 j := rfl

/-- The left child ends at the inserted midpoint; this is also definitional. -/
theorem gaussianLeftChild_midpoint (K r : ℕ)
    (x : DyadicNoiseSpace (r + 1)) (j : DyadicCell r) :
    (gaussianEndpoints K (r + 1) x (Sum.inl j)).2 =
      gaussianMidpoint K r x j := rfl

/-- The right child begins at the inserted midpoint; this is also definitional. -/
theorem gaussianRightChild_midpoint (K r : ℕ)
    (x : DyadicNoiseSpace (r + 1)) (j : DyadicCell r) :
    (gaussianEndpoints K (r + 1) x (Sum.inr j)).1 =
      gaussianMidpoint K r x j := rfl

/-- Endpoint differences are exactly the recursively constructed increments. -/
theorem gaussianEndpoints_sub_eq_level (K : ℕ) : ∀ r
    (x : DyadicNoiseSpace r) (j : DyadicCell r),
    (gaussianEndpoints K r x j).2 - (gaussianEndpoints K r x j).1 =
      gaussianLevel K r x j
  | 0, x, j => by
      simp [gaussianEndpoints, gaussianLevel]
  | r + 1, x, j => by
      have ih := gaussianEndpoints_sub_eq_level K r (dyadicNoiseSplit r x).1
      rcases j with j | j <;>
        simp [gaussianEndpoints, gaussianLevel, dyadicRefine,
          gaussianHalfSplit, ← ih j] <;> ring

/-! ## The integer skeleton -/

/-- There are exactly `2^r` cells at level `r`. -/
theorem card_dyadicCell (r : ℕ) : Fintype.card (DyadicCell r) = 2 ^ r := by
  induction r with
  | zero => simp [DyadicCell]
  | succ r ih =>
      have h1 : Fintype.card (DyadicCell (r + 1)) =
          Fintype.card (DyadicCell r ⊕ DyadicCell r) :=
        Fintype.card_congr (Equiv.refl _)
      rw [h1, Fintype.card_sum, ih, pow_succ]
      omega

/-- An arbitrary fixed enumeration of the leaf cells by `Fin (2^K)`. -/
noncomputable def dyadicLeafCell (K : ℕ) (j : Fin (2 ^ K)) : DyadicCell K :=
  (Fintype.equivFin (DyadicCell K)).symm
    (Fin.cast (card_dyadicCell K).symm j)

theorem dyadicLeafCell_injective (K : ℕ) :
    Function.Injective (dyadicLeafCell K) := by
  intro i j h
  apply Fin.ext
  have h' := congrArg
    (fun c => ((Fintype.equivFin (DyadicCell K)) c).val) h
  simpa [dyadicLeafCell] using h'

/-- Unit-time Gaussian increments at the leaves. -/
noncomputable def gaussianUnitIncrement (K : ℕ) (j : Fin (2 ^ K))
    (x : DyadicNoiseSpace K) : ℝ :=
  gaussianLevel K K x (dyadicLeafCell K j)

/-- Each leaf increment is standard normal. -/
theorem gaussianUnitIncrement_map (K : ℕ) (j : Fin (2 ^ K)) :
    (dyadicNoiseMeasure K).map (gaussianUnitIncrement K j) = gaussianReal 0 1 := by
  simpa [gaussianUnitIncrement, dyadicVariance_self] using
    gaussianLevel_component_map K K (dyadicLeafCell K j)

/-- The integer-skeleton Gaussian increments are independent. -/
theorem gaussianUnitIncrement_iIndep (K : ℕ) :
    iIndepFun (gaussianUnitIncrement K) (dyadicNoiseMeasure K) := by
  simpa [gaussianUnitIncrement] using
    (gaussianLevel_iIndep K K).precomp (dyadicLeafCell_injective K)

/-- Extend the finite leaf increment family by zero outside the horizon. -/
noncomputable def gaussianUnitIncrementNat (K : ℕ)
    (x : DyadicNoiseSpace K) (j : ℕ) : ℝ :=
  if h : j < 2 ^ K then gaussianUnitIncrement K ⟨j, h⟩ x else 0

/-- The integer skeleton `W(j)`. -/
noncomputable def gaussianSkeleton (K : ℕ)
    (x : DyadicNoiseSpace K) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, gaussianUnitIncrementNat K x i

@[simp] theorem gaussianSkeleton_zero (K : ℕ) (x : DyadicNoiseSpace K) :
    gaussianSkeleton K x 0 = 0 := by
  simp [gaussianSkeleton]

/-- Consecutive skeleton increments are the leaf normals. -/
theorem gaussianSkeleton_succ_sub (K j : ℕ) (h : j < 2 ^ K)
    (x : DyadicNoiseSpace K) :
    gaussianSkeleton K x (j + 1) - gaussianSkeleton K x j =
      gaussianUnitIncrement K ⟨j, h⟩ x := by
  simp [gaussianSkeleton, Finset.sum_range_succ,
    gaussianUnitIncrementNat, h]

/-!
THEOREM LIST
* `dyadicNoiseSplit_measurePreserving`, `dyadicNoiseRestrict_measurePreserving`
* `dyadicRefine_measurePreserving`
* `gaussianHalfSplit_measurePreserving`
* `gaussianLevel_map`, `gaussianLevel_component_map`, `gaussianLevel_iIndep`
* `gaussianLevelOnHorizon_measurePreserving`, `gaussianLevelOnHorizon_iIndep`
* `gaussianMidpoint_formula`, `gaussianLeftChild_midpoint`, `gaussianRightChild_midpoint`
* `gaussianEndpoints_sub_eq_level`
* `gaussianUnitIncrement_map`, `gaussianUnitIncrement_iIndep`
* `gaussianSkeleton_succ_sub`

CLOSES K10: concrete finite common source, exact level-wise independent Gaussian laws,
midpoint bookkeeping identities, and standard-normal integer-skeleton increments.

UNFINISHED IN THIS FILE: no mathematical item intentionally omitted.
END
-/

end Ripple.Kurtz.StrongApprox.DyadicGaussianTree

end
