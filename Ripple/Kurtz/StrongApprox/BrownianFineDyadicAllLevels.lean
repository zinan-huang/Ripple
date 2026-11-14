-- Ripple/Kurtz/StrongApprox/BrownianFineDyadicAllLevels.lean
import Ripple.Kurtz.StrongApprox.BrownianFineDyadicAdapters

/-!
# Brownian fine dyadic increments at every stored level

Declarations of `BrownianFineDyadicAdapters` used here:
* `BrownianFineDyadicAdapters.partialMidpointAffine`;
* `BrownianFineDyadicAdapters.brownianDyadicIncrementVector_indep_fineLevelVector`;
* `BrownianFineDyadicAdapters.brownianChildPairVector_map_of_parentLaw`.

Declarations of `BrownianFineDyadicStep` reached through that import:
* `brownianDyadicIncrementVector`, `brownianChildPairVector`;
* `measurable_brownianDyadicIncrementVector`;
* `measurable_brownianChildPairVector`;
* `brownianDyadicIncrementVector_base_map`.

`DyadicBrownianOn P W H` has four fields:
* `eval_measurable : ∀ t, Measurable (W t)`;
* `continuous_ae : ∀ᵐ omega ∂P, Continuous (fun t => W t omega)`;
* `cell_law` for every entropy level and cell;
* `cell_independent` for every entropy level.

The final two theorems in this file have exactly the `cell_law` and
`cell_independent` expressions at every fine entropy level `K+r`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal NNReal BigOperators

namespace Ripple.Kurtz.StrongApprox.BrownianFineDyadicAllLevels

open BrownianFinePath BrownianFineDyadicStep BrownianFineDyadicAdapters
open FineSchauderSeries DyadicGaussianTree

/-! ## The chronological parent-to-child index equivalence -/

/-- `inl (j,c)` is child `(j,2c)` and `inr (j,c)` is child
`(j,2c+1)`. -/
def childChronologicalMap (K r : ℕ) :
    FineLevelIndex K r ⊕ FineLevelIndex K r →
      FineLevelIndex K (r + 1)
  | Sum.inl q =>
      ⟨q.1, ⟨2 * q.2.val, by
        rw [pow_succ]
        omega⟩⟩
  | Sum.inr q =>
      ⟨q.1, ⟨2 * q.2.val + 1, by
        rw [pow_succ]
        omega⟩⟩

private theorem childChronologicalMap_injective (K r : ℕ) :
    Function.Injective (childChronologicalMap K r) := by
  intro a b h
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          congr 1
          apply Prod.ext
          · exact congrArg
              (fun q : FineLevelIndex K (r + 1) => q.1) h
          · apply Fin.ext
            have hv := congrArg
              (fun q : FineLevelIndex K (r + 1) => q.2.val) h
            simp [childChronologicalMap] at hv
            omega
      | inr b =>
          exfalso
          have hv := congrArg
            (fun q : FineLevelIndex K (r + 1) => q.2.val) h
          simp [childChronologicalMap] at hv
          omega
  | inr a =>
      cases b with
      | inl b =>
          exfalso
          have hv := congrArg
            (fun q : FineLevelIndex K (r + 1) => q.2.val) h
          simp [childChronologicalMap] at hv
          omega
      | inr b =>
          congr 1
          apply Prod.ext
          · exact congrArg
              (fun q : FineLevelIndex K (r + 1) => q.1) h
          · apply Fin.ext
            have hv := congrArg
              (fun q : FineLevelIndex K (r + 1) => q.2.val) h
            simp [childChronologicalMap] at hv
            omega

private theorem childChronologicalMap_surjective (K r : ℕ) :
    Function.Surjective (childChronologicalMap K r) := by
  rintro ⟨j, c⟩
  obtain ⟨d, hd | hd⟩ := Nat.even_or_odd' c.val
  · have hdlt : d < 2 ^ r := by
      have hc := c.isLt
      have h2 := pow_succ 2 r
      omega
    refine ⟨Sum.inl ⟨j, ⟨d, hdlt⟩⟩, ?_⟩
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp [childChronologicalMap]
      omega
  · have hdlt : d < 2 ^ r := by
      have hc := c.isLt
      have h2 := pow_succ 2 r
      omega
    refine ⟨Sum.inr ⟨j, ⟨d, hdlt⟩⟩, ?_⟩
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp [childChronologicalMap]
      omega

noncomputable def childChronologicalEquiv (K r : ℕ) :
    FineLevelIndex K r ⊕ FineLevelIndex K r ≃
      FineLevelIndex K (r + 1) :=
  Equiv.ofBijective (childChronologicalMap K r)
    ⟨childChronologicalMap_injective K r,
      childChronologicalMap_surjective K r⟩

/-- The requested measurable equivalence on the finite chronological index. -/
noncomputable def childChronologicalMeasurableEquiv (K r : ℕ) :
    FineLevelIndex K r ⊕ FineLevelIndex K r ≃ᵐ
      FineLevelIndex K (r + 1) where
  toEquiv := childChronologicalEquiv K r
  measurable_toFun := by
    have h : (childChronologicalEquiv K r : _ → _) =
        Sum.elim
          (fun q => childChronologicalEquiv K r (Sum.inl q))
          (fun q => childChronologicalEquiv K r (Sum.inr q)) := by
      funext s
      cases s <;> rfl
    show Measurable (childChronologicalEquiv K r)
    rw [h]
    exact Measurable.sumElim (measurable_of_finite _)
      (measurable_of_finite _)
  measurable_invFun := Measurable.of_discrete

@[simp] theorem childChronologicalEquiv_inl
    (K r : ℕ) (q : FineLevelIndex K r) :
    childChronologicalEquiv K r (Sum.inl q) =
      ⟨q.1, ⟨2 * q.2.val, by
        rw [pow_succ]
        omega⟩⟩ := rfl

@[simp] theorem childChronologicalEquiv_inr
    (K r : ℕ) (q : FineLevelIndex K r) :
    childChronologicalEquiv K r (Sum.inr q) =
      ⟨q.1, ⟨2 * q.2.val + 1, by
        rw [pow_succ]
        omega⟩⟩ := rfl

private theorem fineLeft_childChronological_inl
    (K r : ℕ) (q : FineLevelIndex K r) :
    fineLeft K (r + 1)
        (childChronologicalEquiv K r (Sum.inl q)) =
      fineLeft K r q := by
  simp only [childChronologicalEquiv_inl]
  unfold fineLeft fineFlatIndex
  simp only [pow_succ]
  push_cast
  field_simp [pow_ne_zero r (by norm_num : (2 : ℝ) ≠ 0)]
  try ring

private theorem fineRight_childChronological_inl
    (K r : ℕ) (q : FineLevelIndex K r) :
    fineRight K (r + 1)
        (childChronologicalEquiv K r (Sum.inl q)) =
      fineMidpoint K r q := by
  simp only [childChronologicalEquiv_inl]
  unfold fineMidpoint fineRight fineLeft fineFlatIndex
  simp only [pow_succ]
  push_cast
  field_simp [pow_ne_zero r (by norm_num : (2 : ℝ) ≠ 0)]
  try ring

private theorem fineLeft_childChronological_inr
    (K r : ℕ) (q : FineLevelIndex K r) :
    fineLeft K (r + 1)
        (childChronologicalEquiv K r (Sum.inr q)) =
      fineMidpoint K r q := by
  simp only [childChronologicalEquiv_inr]
  unfold fineMidpoint fineRight fineLeft fineFlatIndex
  simp only [pow_succ]
  push_cast
  field_simp [pow_ne_zero r (by norm_num : (2 : ℝ) ≠ 0)]
  try ring

private theorem fineRight_childChronological_inr
    (K r : ℕ) (q : FineLevelIndex K r) :
    fineRight K (r + 1)
        (childChronologicalEquiv K r (Sum.inr q)) =
      fineRight K r q := by
  simp only [childChronologicalEquiv_inr]
  unfold fineRight fineFlatIndex
  simp only [pow_succ]
  push_cast
  field_simp [pow_ne_zero r (by norm_num : (2 : ℝ) ≠ 0)]
  try ring

/-- Reindex vectors by the chronological index equivalence. -/
noncomputable def childVectorChronologicalEquiv (K r : ℕ) :
    (FineLevelIndex K r ⊕ FineLevelIndex K r → ℝ) ≃ᵐ
      (FineLevelIndex K (r + 1) → ℝ) :=
  MeasurableEquiv.piCongrLeft
    (fun _ : FineLevelIndex K (r + 1) => ℝ)
    (childChronologicalEquiv K r)

/-- The reindexed child-pair vector is literally the next increment vector. -/
theorem childPair_reindexed_eq_incrementVector
    (K r : ℕ) (omega : BrownianFineSpace K) :
    childVectorChronologicalEquiv K r
        (brownianChildPairVector K r omega) =
      brownianDyadicIncrementVector K (r + 1) omega := by
  funext q
  dsimp [childVectorChronologicalEquiv]
  rw [MeasurableEquiv.coe_piCongrLeft]
  obtain ⟨s, rfl⟩ := (childChronologicalEquiv K r).surjective q
  rw [Equiv.piCongrLeft_apply_apply]
  cases s with
  | inl p =>
      have h1 := fineLeft_childChronological_inl K r p
      have h2 := fineRight_childChronological_inl K r p
      simp only [childChronologicalEquiv_inl] at h1 h2
      simp [brownianChildPairVector, brownianDyadicIncrementVector,
        brownianDyadicIncrement, h1, h2]
  | inr p =>
      have h1 := fineLeft_childChronological_inr K r p
      have h2 := fineRight_childChronological_inr K r p
      simp only [childChronologicalEquiv_inr] at h1 h2
      simp [brownianChildPairVector, brownianDyadicIncrementVector,
        brownianDyadicIncrement, h1, h2]

/-- A constant finite product law is invariant under the chronological
reindexing.  This is the pinned `measurePreserving_piCongrLeft` API. -/
theorem childVectorChronologicalEquiv_map_pi
    (K r : ℕ) (v : ℝ≥0) :
    (Measure.pi
        (fun _ : FineLevelIndex K r ⊕ FineLevelIndex K r =>
          gaussianReal 0 v)).map
        (childVectorChronologicalEquiv K r) =
      Measure.pi
        (fun _ : FineLevelIndex K (r + 1) => gaussianReal 0 v) := by
  simpa [childVectorChronologicalEquiv] using
    (measurePreserving_piCongrLeft
      (α := fun _ : FineLevelIndex K (r + 1) => ℝ)
      (fun _ : FineLevelIndex K (r + 1) => gaussianReal 0 v)
      (childChronologicalEquiv K r)).map_eq

/-! ## Product law and independence at every fine level -/

/-- **All-level headline.**  Every stored fine-level increment vector is iid
Gaussian with variance `dyadicVariance 0 r = 2^(-r)`. -/
theorem brownianDyadicIncrementVector_map_allLevels
    (K : ℕ) : ∀ r : ℕ,
    (brownianFineMeasure K).map
        (brownianDyadicIncrementVector K r) =
      Measure.pi
        (fun _ : FineLevelIndex K r =>
          gaussianReal 0 (dyadicVariance 0 r))
  | 0 => by
      simpa using brownianDyadicIncrementVector_base_map K
  | r + 1 => by
      have hchild := brownianChildPairVector_map_of_parentLaw K r
        (brownianDyadicIncrementVector_map_allLevels K r)
      calc
        (brownianFineMeasure K).map
            (brownianDyadicIncrementVector K (r + 1)) =
          (brownianFineMeasure K).map
            (fun omega => childVectorChronologicalEquiv K r
              (brownianChildPairVector K r omega)) := by
                exact Measure.map_congr
                  (Filter.Eventually.of_forall fun omega =>
                    (childPair_reindexed_eq_incrementVector K r omega).symm)
        _ = ((brownianFineMeasure K).map
              (brownianChildPairVector K r)).map
              (childVectorChronologicalEquiv K r) := by
            exact (Measure.map_map
              (childVectorChronologicalEquiv K r).measurable
              (measurable_brownianChildPairVector K r)).symm
        _ = (Measure.pi
              (fun _ : FineLevelIndex K r ⊕ FineLevelIndex K r =>
                gaussianReal 0 (dyadicVariance 0 (r + 1)))).map
              (childVectorChronologicalEquiv K r) := by
            rw [hchild]
        _ = Measure.pi
              (fun _ : FineLevelIndex K (r + 1) =>
                gaussianReal 0 (dyadicVariance 0 (r + 1))) :=
            childVectorChronologicalEquiv_map_pi K r
              (dyadicVariance 0 (r + 1))

/-- Coordinate independence follows from the full vector product law. -/
theorem brownianDyadicIncrementVector_iIndep_allLevels
    (K r : ℕ) :
    iIndepFun
      (fun q omega => brownianDyadicIncrementVector K r omega q)
      (brownianFineMeasure K) :=
  iIndepFun_of_vector_map_eq_pi
    (measurable_brownianDyadicIncrementVector K r)
    (brownianDyadicIncrementVector_map_allLevels K r)

/-! ## Exact adapter to the fine entropy levels `m = K+r` -/

/-- Row-major chronological index as a bounded `Fin`. -/
def fineFlatFin (K r : ℕ) (q : FineLevelIndex K r) :
    Fin (2 ^ (K + r)) :=
  ⟨fineFlatIndex K r q, by
    rw [pow_add]
    exact fineFlatIndex_lt K r q⟩

private theorem fineFlatFin_injective (K r : ℕ) :
    Function.Injective (fineFlatFin K r) := by
  intro q p h
  apply fineFlatIndex_injective K r
  exact congrArg Fin.val h

private theorem fineFlatFin_bijective (K r : ℕ) :
    Function.Bijective (fineFlatFin K r) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨fineFlatFin_injective K r, ?_⟩
  change
    Fintype.card (Fin (2 ^ K) × Fin (2 ^ r)) =
      Fintype.card (Fin (2 ^ (K + r)))
  simp [pow_add]

noncomputable def fineFlatEquiv (K r : ℕ) :
    FineLevelIndex K r ≃ Fin (2 ^ (K + r)) :=
  Equiv.ofBijective (fineFlatFin K r)
    (fineFlatFin_bijective K r)

noncomputable def fineFlatVectorEquiv (K r : ℕ) :
    (FineLevelIndex K r → ℝ) ≃ᵐ
      (Fin (2 ^ (K + r)) → ℝ) :=
  MeasurableEquiv.piCongrLeft
    (fun _ : Fin (2 ^ (K + r)) => ℝ)
    (fineFlatEquiv K r)

private theorem entropyFinePoint_left
    (K r : ℕ) (q : FineLevelIndex K r) :
    brownianDyadicPoint ((2 : ℝ) ^ K) (K + r)
        (fineFlatEquiv K r q).val =
      fineLeft K r q := by
  change
    (2 : ℝ) ^ K * (fineFlatIndex K r q : ℝ) /
        (2 : ℝ) ^ (K + r) =
      (fineFlatIndex K r q : ℝ) / (2 : ℝ) ^ r
  rw [pow_add]
  field_simp [pow_ne_zero K (by norm_num : (2 : ℝ) ≠ 0),
    pow_ne_zero r (by norm_num : (2 : ℝ) ≠ 0)]
  try ring

private theorem entropyFinePoint_right
    (K r : ℕ) (q : FineLevelIndex K r) :
    brownianDyadicPoint ((2 : ℝ) ^ K) (K + r)
        ((fineFlatEquiv K r q).val + 1) =
      fineRight K r q := by
  change
    (2 : ℝ) ^ K * ((fineFlatIndex K r q + 1 : ℕ) : ℝ) /
        (2 : ℝ) ^ (K + r) =
      ((fineFlatIndex K r q : ℝ) + 1) / (2 : ℝ) ^ r
  rw [pow_add]
  push_cast
  field_simp [pow_ne_zero K (by norm_num : (2 : ℝ) ≠ 0),
    pow_ne_zero r (by norm_num : (2 : ℝ) ≠ 0)]
  try ring

noncomputable def brownianEntropyFineIncrementVector
    (K r : ℕ) (omega : BrownianFineSpace K) :
    Fin (2 ^ (K + r)) → ℝ :=
  fun k =>
    brownianCandidate K
        (brownianDyadicPoint ((2 : ℝ) ^ K) (K + r) (k.val + 1)) omega -
      brownianCandidate K
        (brownianDyadicPoint ((2 : ℝ) ^ K) (K + r) k.val) omega

@[fun_prop]
theorem measurable_brownianEntropyFineIncrementVector
    (K r : ℕ) :
    Measurable (brownianEntropyFineIncrementVector K r) := by
  apply measurable_pi_lambda
  intro k
  exact
    (measurable_brownianCandidate K
      (brownianDyadicPoint ((2 : ℝ) ^ K) (K + r) (k.val + 1))).sub
    (measurable_brownianCandidate K
      (brownianDyadicPoint ((2 : ℝ) ^ K) (K + r) k.val))

/-- Flat chronological reindexing agrees pointwise with the entropy increment
vector at level `K+r`. -/
theorem fineFlat_reindexed_eq_entropyFineIncrementVector
    (K r : ℕ) (omega : BrownianFineSpace K) :
    fineFlatVectorEquiv K r
        (brownianDyadicIncrementVector K r omega) =
      brownianEntropyFineIncrementVector K r omega := by
  funext k
  dsimp [fineFlatVectorEquiv]
  rw [MeasurableEquiv.coe_piCongrLeft]
  obtain ⟨q, rfl⟩ := (fineFlatEquiv K r).surjective k
  rw [Equiv.piCongrLeft_apply_apply]
  unfold brownianEntropyFineIncrementVector
  unfold brownianDyadicIncrementVector brownianDyadicIncrement
  rw [entropyFinePoint_left, entropyFinePoint_right]

private theorem fineFlatVectorEquiv_map_pi
    (K r : ℕ) (v : ℝ≥0) :
    (Measure.pi
      (fun _ : FineLevelIndex K r => gaussianReal 0 v)).map
        (fineFlatVectorEquiv K r) =
      Measure.pi
        (fun _ : Fin (2 ^ (K + r)) => gaussianReal 0 v) := by
  simpa [fineFlatVectorEquiv] using
    (measurePreserving_piCongrLeft
      (α := fun _ : Fin (2 ^ (K + r)) => ℝ)
      (fun _ : Fin (2 ^ (K + r)) => gaussianReal 0 v)
      (fineFlatEquiv K r)).map_eq

/-- Product law in the exact entropy-level chronological indexing. -/
theorem brownianEntropyFineIncrementVector_map
    (K r : ℕ) :
    (brownianFineMeasure K).map
        (brownianEntropyFineIncrementVector K r) =
      Measure.pi
        (fun _ : Fin (2 ^ (K + r)) =>
          gaussianReal 0 (dyadicVariance 0 r)) := by
  calc
    (brownianFineMeasure K).map
        (brownianEntropyFineIncrementVector K r) =
      (brownianFineMeasure K).map
        (fun omega => fineFlatVectorEquiv K r
          (brownianDyadicIncrementVector K r omega)) := by
            exact Measure.map_congr
              (Filter.Eventually.of_forall fun omega =>
                (fineFlat_reindexed_eq_entropyFineIncrementVector
                  K r omega).symm)
    _ = ((brownianFineMeasure K).map
          (brownianDyadicIncrementVector K r)).map
          (fineFlatVectorEquiv K r) := by
        exact (Measure.map_map
          (fineFlatVectorEquiv K r).measurable
          (measurable_brownianDyadicIncrementVector K r)).symm
    _ = (Measure.pi
          (fun _ : FineLevelIndex K r =>
            gaussianReal 0 (dyadicVariance 0 r))).map
          (fineFlatVectorEquiv K r) := by
        rw [brownianDyadicIncrementVector_map_allLevels]
    _ = Measure.pi
          (fun _ : Fin (2 ^ (K + r)) =>
            gaussianReal 0 (dyadicVariance 0 r)) :=
        fineFlatVectorEquiv_map_pi K r (dyadicVariance 0 r)

private theorem entropyFineMesh_eq_variance (K r : ℕ) :
    Real.toNNReal
        (brownianDyadicMesh ((2 : ℝ) ^ K) (K + r)) =
      dyadicVariance 0 r := by
  have hnonneg :
      0 ≤ brownianDyadicMesh ((2 : ℝ) ^ K) (K + r) := by
    unfold brownianDyadicMesh
    positivity
  apply NNReal.coe_injective
  rw [Real.coe_toNNReal _ hnonneg]
  change
    (2 : ℝ) ^ K / (2 : ℝ) ^ (K + r) =
      (2 : ℝ) ^ 0 / (2 : ℝ) ^ r
  rw [pow_zero, pow_add]
  field_simp [pow_ne_zero K (by norm_num : (2 : ℝ) ≠ 0),
    pow_ne_zero r (by norm_num : (2 : ℝ) ≠ 0)]

/-- The exact `DyadicBrownianOn.cell_law` expression at every fine entropy
level `m = K+r`. -/
theorem brownianCandidate_entropyFineCell_map
    (K r : ℕ) (k : Fin (2 ^ (K + r))) :
    (brownianFineMeasure K).map
        (fun omega =>
          brownianCandidate K
              (brownianDyadicPoint ((2 : ℝ) ^ K) (K + r)
                (k.val + 1)) omega -
            brownianCandidate K
              (brownianDyadicPoint ((2 : ℝ) ^ K) (K + r)
                k.val) omega) =
      gaussianReal 0
        (Real.toNNReal
          (brownianDyadicMesh ((2 : ℝ) ^ K) (K + r))) := by
  change
    (brownianFineMeasure K).map
        (fun omega => brownianEntropyFineIncrementVector K r omega k) = _
  rw [entropyFineMesh_eq_variance]
  exact vectorComponent_map_eq
    (measurable_brownianEntropyFineIncrementVector K r)
    (brownianEntropyFineIncrementVector_map K r) k

/-- The exact `DyadicBrownianOn.cell_independent` expression at every fine
entropy level `m = K+r`. -/
theorem brownianCandidate_entropyFineCell_iIndep
    (K r : ℕ) :
    iIndepFun
      (fun (k : Fin (2 ^ (K + r))) omega =>
        brownianCandidate K
            (brownianDyadicPoint ((2 : ℝ) ^ K) (K + r)
              (k.val + 1)) omega -
          brownianCandidate K
            (brownianDyadicPoint ((2 : ℝ) ^ K) (K + r)
              k.val) omega)
      (brownianFineMeasure K) := by
  change iIndepFun
    (fun k omega => brownianEntropyFineIncrementVector K r omega k)
    (brownianFineMeasure K)
  exact iIndepFun_of_vector_map_eq_pi
    (measurable_brownianEntropyFineIncrementVector K r)
    (brownianEntropyFineIncrementVector_map K r)

/-!
THEOREM LIST
* `childChronologicalMeasurableEquiv`
* `childPair_reindexed_eq_incrementVector`
* `childVectorChronologicalEquiv_map_pi`
* `brownianDyadicIncrementVector_map_allLevels`
* `brownianDyadicIncrementVector_iIndep_allLevels`
* `fineFlatEquiv`, `fineFlatVectorEquiv`
* `fineFlat_reindexed_eq_entropyFineIncrementVector`
* `brownianEntropyFineIncrementVector_map`
* `brownianCandidate_entropyFineCell_map`
* `brownianCandidate_entropyFineCell_iIndep`

CLOSES
* Item 1: the literal even/odd chronological measurable equivalence and the
  identity between the reindexed child-pair vector and level `r+1` increments.
* Item 2: the product Gaussian law for every stored level, with exact variance
  `dyadicVariance 0 r = 2^(-r)`.
* The pinned `measurePreserving_piCongrLeft` reindexing step.
* Item 3 at every fine entropy level `m = K+r`: the exact expressions required
  by `DyadicBrownianOn.cell_law` and `DyadicBrownianOn.cell_independent`.
* `DyadicBrownianOn.eval_measurable` is already supplied pointwise by
  `measurable_brownianCandidate` of `BrownianFinePath`.

UNFINISHED
* The coarse entropy levels `m < K`.  They must be identified with the
  spatially ordered `gaussianLevelOnHorizon m (K-m)` tree increments.
* `DyadicBrownianOn.continuous_ae` asks for global continuity on `ℝ`; `BrownianFinePath`
  currently states only continuity on `Icc 0 (2^K)`.
* Therefore no complete `DyadicBrownianOn` theorem is asserted in this file.
END
-/

end Ripple.Kurtz.StrongApprox.BrownianFineDyadicAllLevels

end
