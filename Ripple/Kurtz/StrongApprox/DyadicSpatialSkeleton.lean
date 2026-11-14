-- Ripple/Kurtz/StrongApprox/DyadicSpatialSkeleton.lean
import Ripple.Kurtz.StrongApprox.DyadicPoissonTree

/-!
# Spatial order for the finite dyadic Gaussian/Poisson trees

The old `dyadicLeafCell` is an arbitrary `Fintype.equivFin` enumeration.  This
file defines the canonical spatial order.  Since the outside `Sum` constructor
is the last refinement, its tag is the low bit: `inl` appends `0` and `inr`
appends `1` to the binary address already stored by the parent.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox.DyadicSpatialSkeleton

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal Nat
open Ripple.Kurtz.StrongApprox
open Ripple.Kurtz.StrongApprox.DyadicGaussianTree
open Ripple.Kurtz.StrongApprox.DyadicPoissonTree

/-! ## The canonical spatial equivalence -/

/-- Append a left bit to a level-`K` address. -/
def leftLeafIndex (K : ℕ) (j : Fin (2 ^ K)) : Fin (2 ^ (K + 1)) :=
  ⟨2 * j.val, by
    have hj := j.isLt
    rw [pow_succ]
    omega⟩

/-- Append a right bit to a level-`K` address. -/
def rightLeafIndex (K : ℕ) (j : Fin (2 ^ K)) : Fin (2 ^ (K + 1)) :=
  ⟨2 * j.val + 1, by
    have hj := j.isLt
    rw [pow_succ]
    omega⟩

/-- Spatial index of a dyadic cell.  Reading the nested constructors from the
root (innermost) to the leaf (outermost) gives the high-to-low binary digits. -/
def spatialCellIndex : (K : ℕ) → DyadicCell K → Fin (2 ^ K)
  | 0, _ => ⟨0, by norm_num⟩
  | K + 1, Sum.inl c => leftLeafIndex K (spatialCellIndex K c)
  | K + 1, Sum.inr c => rightLeafIndex K (spatialCellIndex K c)

/-- Different cells have different spatial binary addresses. -/
theorem spatialCellIndex_injective :
    ∀ K, Function.Injective (spatialCellIndex K)
  | 0 => by
      intro a b _
      exact Subsingleton.elim (α := Unit) a b
  | K + 1 => by
      intro a b h
      rcases a with a | a <;> rcases b with b | b
      · have hv := congrArg Fin.val h
        have hab : spatialCellIndex K a = spatialCellIndex K b := by
          apply Fin.ext
          simp [spatialCellIndex, leftLeafIndex] at hv
          omega
        exact congrArg
          (fun c : DyadicCell K => (Sum.inl c : DyadicCell (K + 1)))
          (spatialCellIndex_injective K hab)
      · exfalso
        have hv := congrArg Fin.val h
        simp [spatialCellIndex, leftLeafIndex, rightLeafIndex] at hv
        omega
      · exfalso
        have hv := congrArg Fin.val h
        simp [spatialCellIndex, leftLeafIndex, rightLeafIndex] at hv
        omega
      · have hv := congrArg Fin.val h
        have hab : spatialCellIndex K a = spatialCellIndex K b := by
          apply Fin.ext
          simp [spatialCellIndex, rightLeafIndex] at hv
          omega
        exact congrArg
          (fun c : DyadicCell K => (Sum.inr c : DyadicCell (K + 1)))
          (spatialCellIndex_injective K hab)

/-- The spatial index is a bijection because both finite types have `2^K`
elements. -/
theorem spatialCellIndex_bijective (K : ℕ) :
    Function.Bijective (spatialCellIndex K) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨spatialCellIndex_injective K, ?_⟩
  rw [card_dyadicCell, Fintype.card_fin]

/-- Cells at level `K` are canonically equivalent to their spatial indices. -/
noncomputable def spatialCellEquiv (K : ℕ) :
    DyadicCell K ≃ Fin (2 ^ K) :=
  Equiv.ofBijective (spatialCellIndex K)
    (spatialCellIndex_bijective K)

/-- The spatial leaf numbered `j`. -/
noncomputable def spatialLeafCell (K : ℕ)
    (j : Fin (2 ^ K)) : DyadicCell K :=
  (spatialCellEquiv K).symm j

@[simp] theorem spatialCellIndex_spatialLeafCell
    (K : ℕ) (j : Fin (2 ^ K)) :
    spatialCellIndex K (spatialLeafCell K j) = j := by
  change spatialCellEquiv K ((spatialCellEquiv K).symm j) = j
  exact (spatialCellEquiv K).apply_symm_apply j

@[simp] theorem spatialLeafCell_spatialCellIndex
    (K : ℕ) (c : DyadicCell K) :
    spatialLeafCell K (spatialCellIndex K c) = c := by
  change (spatialCellEquiv K).symm (spatialCellEquiv K c) = c
  exact (spatialCellEquiv K).symm_apply_apply c

/-- The required bijectivity statement for the leaf-order map. -/
theorem spatialLeafCell_bijective (K : ℕ) :
    Function.Bijective (spatialLeafCell K) :=
  (spatialCellEquiv K).symm.bijective

theorem spatialLeafCell_injective (K : ℕ) :
    Function.Injective (spatialLeafCell K) :=
  (spatialLeafCell_bijective K).1

/-- The even spatial child is the left child of the parent. -/
@[simp] theorem spatialLeafCell_leftLeafIndex
    (K : ℕ) (j : Fin (2 ^ K)) :
    spatialLeafCell (K + 1) (leftLeafIndex K j) =
      Sum.inl (spatialLeafCell K j) := by
  apply spatialCellIndex_injective (K + 1)
  simp [spatialCellIndex]

/-- The odd spatial child is the right child of the parent. -/
@[simp] theorem spatialLeafCell_rightLeafIndex
    (K : ℕ) (j : Fin (2 ^ K)) :
    spatialLeafCell (K + 1) (rightLeafIndex K j) =
      Sum.inr (spatialLeafCell K j) := by
  apply spatialCellIndex_injective (K + 1)
  simp [spatialCellIndex]

/-- Left spatial coordinate of a level-`r` cell on a horizon-`2^H` grid. -/
def cellLeftEndpoint (H r : ℕ) (c : DyadicCell r) : ℕ :=
  (spatialCellIndex r c).val * 2 ^ (H - r)

/-- Right spatial coordinate of a level-`r` cell on a horizon-`2^H` grid. -/
def cellRightEndpoint (H r : ℕ) (c : DyadicCell r) : ℕ :=
  ((spatialCellIndex r c).val + 1) * 2 ^ (H - r)

/-- The spatial interval represented by one cell. -/
def cellEndpoints (H r : ℕ) (c : DyadicCell r) : ℕ × ℕ :=
  (cellLeftEndpoint H r c, cellRightEndpoint H r c)

/-- The leaf numbered `j` is exactly the unit interval `[j,j+1]`. -/
theorem spatialLeafCell_endpoints (K : ℕ) (j : Fin (2 ^ K)) :
    cellEndpoints K K (spatialLeafCell K j) =
      (j.val, j.val + 1) := by
  simp [cellEndpoints, cellLeftEndpoint, cellRightEndpoint]

/-- Reindexing a finite sum by the spatial leaf equivalence changes no sum. -/
theorem sum_spatialLeafCell
    {A : Type*} [AddCommMonoid A]
    (K : ℕ) (f : DyadicCell K → A) :
    (∑ j : Fin (2 ^ K), f (spatialLeafCell K j)) =
      ∑ c : DyadicCell K, f c := by
  change
    (∑ j : Fin (2 ^ K), f ((spatialCellEquiv K).symm j)) =
      ∑ c : DyadicCell K, f c
  exact Fintype.sum_equiv (spatialCellEquiv K).symm _ _
    (fun _ => rfl)

/-! ## Spatial adjacency of Gaussian endpoints -/

/-- Consecutive spatial cells share their Gaussian endpoint.  The even case is
exactly `left child midpoint = right child midpoint`; the odd case reduces to
adjacency of the two parent cells. -/
theorem gaussianEndpoints_spatial_adjacent (H : ℕ) :
    ∀ r (x : DyadicNoiseSpace r) (j : ℕ)
      (h : j + 1 < 2 ^ r),
      (gaussianEndpoints H r x
        (spatialLeafCell r ⟨j, by omega⟩)).2 =
      (gaussianEndpoints H r x
        (spatialLeafCell r ⟨j + 1, h⟩)).1
  | 0, _x, _j, h => by norm_num at h
  | r + 1, x, j, h => by
      obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' j
      · have hq : q < 2 ^ r := by
          rw [pow_succ] at h
          omega
        let qf : Fin (2 ^ r) := ⟨q, hq⟩
        have hleft :
            spatialLeafCell (r + 1) ⟨2 * q, by
              rw [pow_succ]
              omega⟩ = Sum.inl (spatialLeafCell r qf) := by
          apply spatialCellIndex_injective (r + 1)
          apply Fin.ext
          simp [spatialCellIndex, leftLeafIndex, qf]
        have hright :
            spatialLeafCell (r + 1) ⟨2 * q + 1, by
              rw [pow_succ]
              omega⟩ = Sum.inr (spatialLeafCell r qf) := by
          apply spatialCellIndex_injective (r + 1)
          apply Fin.ext
          simp [spatialCellIndex, rightLeafIndex, qf]
        rw [hleft, hright]
        exact (gaussianLeftChild_midpoint H r x (spatialLeafCell r qf)).trans
          (gaussianRightChild_midpoint H r x
            (spatialLeafCell r qf)).symm
      · have hqnext : q + 1 < 2 ^ r := by
          rw [pow_succ] at h
          omega
        have hq : q < 2 ^ r := by omega
        let qf : Fin (2 ^ r) := ⟨q, hq⟩
        let qnext : Fin (2 ^ r) := ⟨q + 1, hqnext⟩
        have hright :
            spatialLeafCell (r + 1) ⟨2 * q + 1, by
              rw [pow_succ]
              omega⟩ = Sum.inr (spatialLeafCell r qf) := by
          apply spatialCellIndex_injective (r + 1)
          apply Fin.ext
          simp [spatialCellIndex, rightLeafIndex, qf]
        have hleft :
            spatialLeafCell (r + 1) ⟨(2 * q + 1) + 1, by
              rw [pow_succ]
              omega⟩ = Sum.inl (spatialLeafCell r qnext) := by
          apply spatialCellIndex_injective (r + 1)
          apply Fin.ext
          simp [spatialCellIndex, leftLeafIndex, qnext]
          omega
        rw [hright, hleft]
        change
          (gaussianEndpoints H r (dyadicNoiseSplit r x).1
            (spatialLeafCell r qf)).2 =
          (gaussianEndpoints H r (dyadicNoiseSplit r x).1
            (spatialLeafCell r qnext)).1
        exact gaussianEndpoints_spatial_adjacent H r
          (dyadicNoiseSplit r x).1 q hqnext

/-- The left endpoint of the first spatial cell is the root value `0`. -/
theorem gaussianEndpoints_spatial_first_left (H : ℕ) :
    ∀ r (x : DyadicNoiseSpace r),
      (gaussianEndpoints H r x
        (spatialLeafCell r ⟨0, by positivity⟩)).1 = 0
  | 0, x => by
      change (gaussianEndpoints H 0 x ()).1 = 0
      rfl
  | r + 1, x => by
      have hpos : 0 < 2 ^ r := by positivity
      let qf : Fin (2 ^ r) := ⟨0, hpos⟩
      have hcell :
          spatialLeafCell (r + 1) ⟨0, by positivity⟩ =
            Sum.inl (spatialLeafCell r qf) := by
        apply spatialCellIndex_injective (r + 1)
        apply Fin.ext
        simp [spatialCellIndex, leftLeafIndex, qf]
      rw [hcell]
      change
        (gaussianEndpoints H r (dyadicNoiseSplit r x).1
          (spatialLeafCell r qf)).1 = 0
      exact gaussianEndpoints_spatial_first_left H r
        (dyadicNoiseSplit r x).1

/-- Restriction of a depth-`r` source to the root source.  (The delivered
text used `dyadicNoiseRestrict 0 r x` here, which is ill-typed because that
function expects `DyadicNoiseSpace (0 + r)`.) -/
def dyadicRootRestrict : (r : ℕ) → DyadicNoiseSpace r → DyadicNoiseSpace 0
  | 0 => id
  | r + 1 => fun x => dyadicRootRestrict r (dyadicNoiseSplit r x).1

/-! ## Spatial unit increments and laws -/

/-- Gaussian increment on the actual unit interval `[j,j+1]`. -/
noncomputable def spatialGaussianUnitIncrement
    (K : ℕ) (j : Fin (2 ^ K)) (x : DyadicNoiseSpace K) : ℝ :=
  gaussianLevel K K x (spatialLeafCell K j)

/-- Poisson count on the actual unit interval `[j,j+1]`. -/
noncomputable def spatialPoissonUnitIncrement
    (K : ℕ) (j : Fin (2 ^ K)) (x : DyadicNoiseSpace K) : ℕ :=
  poissonLevel K K x (spatialLeafCell K j)

/-- Every spatial Gaussian leaf increment is `N(0,1)`. -/
theorem spatialGaussianUnitIncrement_map
    (K : ℕ) (j : Fin (2 ^ K)) :
    (dyadicNoiseMeasure K).map (spatialGaussianUnitIncrement K j) =
      gaussianReal 0 1 := by
  simpa [spatialGaussianUnitIncrement, dyadicVariance_self] using
    gaussianLevel_component_map K K (spatialLeafCell K j)

/-- Spatial Gaussian leaf increments are independent. -/
theorem spatialGaussianUnitIncrement_iIndep (K : ℕ) :
    iIndepFun (spatialGaussianUnitIncrement K)
      (dyadicNoiseMeasure K) := by
  simpa [spatialGaussianUnitIncrement] using
    (gaussianLevel_iIndep K K).precomp
      (spatialLeafCell_injective K)

/-- Every spatial Poisson leaf count is `Poisson(1)`. -/
theorem spatialPoissonUnitIncrement_map
    (K : ℕ) (j : Fin (2 ^ K)) :
    (dyadicNoiseMeasure K).map (spatialPoissonUnitIncrement K j) =
      poisMeasure 1 := by
  simpa [spatialPoissonUnitIncrement, dyadicVariance_self] using
    poissonLevel_component_map K K (spatialLeafCell K j)

/-- Spatial Poisson leaf counts are independent. -/
theorem spatialPoissonUnitIncrement_iIndep (K : ℕ) :
    iIndepFun (spatialPoissonUnitIncrement K)
      (dyadicNoiseMeasure K) := by
  simpa [spatialPoissonUnitIncrement] using
    (poissonLevel_iIndep K K).precomp
      (spatialLeafCell_injective K)

/-- Both spatial increment families live on the same finite Gaussian product
space.  No cross-family independence is claimed. -/
theorem coupledSpatialLeafLaws (K : ℕ) :
    iIndepFun (spatialGaussianUnitIncrement K) (dyadicNoiseMeasure K) ∧
    (∀ j, (dyadicNoiseMeasure K).map
      (spatialGaussianUnitIncrement K j) = gaussianReal 0 1) ∧
    iIndepFun (spatialPoissonUnitIncrement K) (dyadicNoiseMeasure K) ∧
    (∀ j, (dyadicNoiseMeasure K).map
      (spatialPoissonUnitIncrement K j) = poisMeasure 1) :=
  ⟨spatialGaussianUnitIncrement_iIndep K,
    spatialGaussianUnitIncrement_map K,
    spatialPoissonUnitIncrement_iIndep K,
    spatialPoissonUnitIncrement_map K⟩

/-! ## Spatial partial-sum skeletons -/

noncomputable def spatialGaussianUnitIncrementNat
    (K : ℕ) (x : DyadicNoiseSpace K) (j : ℕ) : ℝ :=
  if h : j < 2 ^ K then
    spatialGaussianUnitIncrement K ⟨j, h⟩ x
  else 0

noncomputable def spatialPoissonUnitIncrementNat
    (K : ℕ) (x : DyadicNoiseSpace K) (j : ℕ) : ℕ :=
  if h : j < 2 ^ K then
    spatialPoissonUnitIncrement K ⟨j, h⟩ x
  else 0

/-- Spatial Gaussian path at integer time `t`. -/
noncomputable def spatialGaussianSkeleton
    (K : ℕ) (x : DyadicNoiseSpace K) (t : ℕ) : ℝ :=
  ∑ j ∈ Finset.range t, spatialGaussianUnitIncrementNat K x j

/-- Spatial Poisson path at integer time `t`. -/
noncomputable def spatialPoissonSkeleton
    (K : ℕ) (x : DyadicNoiseSpace K) (t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range t, spatialPoissonUnitIncrementNat K x j

@[simp] theorem spatialGaussianSkeleton_zero
    (K : ℕ) (x : DyadicNoiseSpace K) :
    spatialGaussianSkeleton K x 0 = 0 := by
  simp [spatialGaussianSkeleton]

@[simp] theorem spatialPoissonSkeleton_zero
    (K : ℕ) (x : DyadicNoiseSpace K) :
    spatialPoissonSkeleton K x 0 = 0 := by
  simp [spatialPoissonSkeleton]

/-- Consecutive increments of the spatial Gaussian path. -/
theorem spatialGaussianSkeleton_succ_sub
    (K j : ℕ) (h : j < 2 ^ K) (x : DyadicNoiseSpace K) :
    spatialGaussianSkeleton K x (j + 1) -
        spatialGaussianSkeleton K x j =
      spatialGaussianUnitIncrement K ⟨j, h⟩ x := by
  simp [spatialGaussianSkeleton, Finset.sum_range_succ,
    spatialGaussianUnitIncrementNat, h]

/-- Consecutive increments of the spatial Poisson path. -/
theorem spatialPoissonSkeleton_succ_sub
    (K j : ℕ) (h : j < 2 ^ K) (x : DyadicNoiseSpace K) :
    spatialPoissonSkeleton K x (j + 1) -
        spatialPoissonSkeleton K x j =
      spatialPoissonUnitIncrement K ⟨j, h⟩ x := by
  simp [spatialPoissonSkeleton, Finset.sum_range_succ,
    spatialPoissonUnitIncrementNat, h]

/-! ## Root identities -/

/-- Gaussian children sum to their parent increment. -/
theorem gaussianLevel_parent_eq_children
    (K r : ℕ) (x : DyadicNoiseSpace (r + 1))
    (j : DyadicCell r) :
    gaussianLevel K r (dyadicNoiseSplit r x).1 j =
      gaussianLevel K (r + 1) x (Sum.inl j) +
        gaussianLevel K (r + 1) x (Sum.inr j) := by
  simp [gaussianLevel, dyadicRefine, gaussianHalfSplit]
  ring

/-- The sum of all level increments is the root increment. -/
theorem gaussianLevel_sum_eq_root (K : ℕ) :
    ∀ r (x : DyadicNoiseSpace r),
      (∑ c : DyadicCell r, gaussianLevel K r x c) =
        gaussianLevel K 0 (dyadicRootRestrict r x) ()
  | 0, x => by
      simp [DyadicCell, dyadicRootRestrict]
  | r + 1, x => by
      change
        (∑ c : DyadicCell r ⊕ DyadicCell r,
          gaussianLevel K (r + 1) x c) = _
      rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
      simp_rw [← gaussianLevel_parent_eq_children K r x]
      rw [gaussianLevel_sum_eq_root K r (dyadicNoiseSplit r x).1]
      simp [dyadicRootRestrict]

/-- The sum of all level counts is the root count. -/
theorem poissonLevel_sum_eq_root (K : ℕ) :
    ∀ r (x : DyadicNoiseSpace r),
      (∑ c : DyadicCell r, poissonLevel K r x c) =
        poissonLevel K 0 (dyadicRootRestrict r x) ()
  | 0, x => by
      simp [DyadicCell, dyadicRootRestrict]
  | r + 1, x => by
      change
        (∑ c : DyadicCell r ⊕ DyadicCell r,
          poissonLevel K (r + 1) x c) = _
      rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
      simp_rw [← poissonLevel_parent_eq_children K r x]
      rw [poissonLevel_sum_eq_root K r (dyadicNoiseSplit r x).1]
      simp [dyadicRootRestrict]

/-- Root Poisson count on the common source. -/
noncomputable def poissonRootCount
    (K : ℕ) (x : DyadicNoiseSpace K) : ℕ :=
  poissonLevel K 0 (dyadicRootRestrict K x) ()

/-- Right endpoint value of the root Gaussian interval. -/
noncomputable def gaussianRootEndpoint
    (K : ℕ) (x : DyadicNoiseSpace K) : ℝ :=
  (gaussianEndpoints K 0 (dyadicRootRestrict K x) ()).2

/-- The spatial Poisson path at the horizon equals the root count. -/
theorem spatialPoissonSkeleton_horizon
    (K : ℕ) (x : DyadicNoiseSpace K) :
    spatialPoissonSkeleton K x (2 ^ K) = poissonRootCount K x := by
  calc
    spatialPoissonSkeleton K x (2 ^ K) =
        ∑ j : Fin (2 ^ K), spatialPoissonUnitIncrement K j x := by
      unfold spatialPoissonSkeleton
      rw [← Fin.sum_univ_eq_sum_range]
      simp [spatialPoissonUnitIncrementNat]
    _ = ∑ c : DyadicCell K, poissonLevel K K x c := by
      simpa [spatialPoissonUnitIncrement] using
        sum_spatialLeafCell K (fun c => poissonLevel K K x c)
    _ = poissonLevel K 0 (dyadicRootRestrict K x) () :=
      poissonLevel_sum_eq_root K K x
    _ = poissonRootCount K x := rfl

/-- The spatial Gaussian path at the horizon equals the root endpoint value. -/
theorem spatialGaussianSkeleton_horizon
    (K : ℕ) (x : DyadicNoiseSpace K) :
    spatialGaussianSkeleton K x (2 ^ K) =
      gaussianRootEndpoint K x := by
  calc
    spatialGaussianSkeleton K x (2 ^ K) =
        ∑ j : Fin (2 ^ K), spatialGaussianUnitIncrement K j x := by
      unfold spatialGaussianSkeleton
      rw [← Fin.sum_univ_eq_sum_range]
      simp [spatialGaussianUnitIncrementNat]
    _ = ∑ c : DyadicCell K, gaussianLevel K K x c := by
      simpa [spatialGaussianUnitIncrement] using
        sum_spatialLeafCell K (fun c => gaussianLevel K K x c)
    _ = gaussianLevel K 0 (dyadicRootRestrict K x) () :=
      gaussianLevel_sum_eq_root K K x
    _ = gaussianRootEndpoint K x := by
      have h := gaussianEndpoints_sub_eq_level K 0
        (dyadicRootRestrict K x) ()
      simpa [gaussianRootEndpoint, gaussianEndpoints] using h.symm

/-! ## The Gaussian tree value at each spatial integer point -/

/-- Actual Gaussian-tree endpoint at spatial integer `t`.  Inside the horizon,
`0` is the root left endpoint and a positive `t` is the right endpoint of leaf
`t-1`; outside the horizon it is extended constantly by the root endpoint. -/
noncomputable def gaussianSpatialPoint
    (K : ℕ) (x : DyadicNoiseSpace K) (t : ℕ) : ℝ :=
  if hzero : t = 0 then 0
  else if ht : t ≤ 2 ^ K then
    (gaussianEndpoints K K x
      (spatialLeafCell K ⟨t - 1, by omega⟩)).2
  else gaussianRootEndpoint K x

@[simp] theorem gaussianSpatialPoint_zero
    (K : ℕ) (x : DyadicNoiseSpace K) :
    gaussianSpatialPoint K x 0 = 0 := by
  simp [gaussianSpatialPoint]

@[simp] theorem gaussianSpatialPoint_succ
    (K j : ℕ) (h : j < 2 ^ K) (x : DyadicNoiseSpace K) :
    gaussianSpatialPoint K x (j + 1) =
      (gaussianEndpoints K K x
        (spatialLeafCell K ⟨j, h⟩)).2 := by
  simp [gaussianSpatialPoint, h]

/-- Consecutive spatial tree values differ by the corresponding leaf
increment. -/
theorem gaussianSpatialPoint_succ_sub
    (K j : ℕ) (h : j < 2 ^ K) (x : DyadicNoiseSpace K) :
    gaussianSpatialPoint K x (j + 1) - gaussianSpatialPoint K x j =
      spatialGaussianUnitIncrement K ⟨j, h⟩ x := by
  cases j with
  | zero =>
      rw [gaussianSpatialPoint_succ K 0 h x,
        gaussianSpatialPoint_zero]
      have hleft := gaussianEndpoints_spatial_first_left K K x
      calc
        (gaussianEndpoints K K x
            (spatialLeafCell K ⟨0, h⟩)).2 - 0 =
            (gaussianEndpoints K K x
              (spatialLeafCell K ⟨0, h⟩)).2 -
            (gaussianEndpoints K K x
              (spatialLeafCell K ⟨0, h⟩)).1 := by
                rw [hleft]
        _ = gaussianLevel K K x (spatialLeafCell K ⟨0, h⟩) :=
          gaussianEndpoints_sub_eq_level K K x
            (spatialLeafCell K ⟨0, h⟩)
        _ = spatialGaussianUnitIncrement K ⟨0, h⟩ x := rfl
  | succ q =>
      have hq : q < 2 ^ K := by omega
      rw [gaussianSpatialPoint_succ K (q + 1) h x,
        gaussianSpatialPoint_succ K q hq x]
      have hadj := gaussianEndpoints_spatial_adjacent K K x q h
      rw [hadj]
      simpa [spatialGaussianUnitIncrement] using
        gaussianEndpoints_sub_eq_level K K x
          (spatialLeafCell K ⟨q + 1, h⟩)

/-- The spatial partial-sum skeleton is literally the Gaussian tree path at
all integer points of the horizon.  K13 can use this theorem directly; no
ordered-leaf adapter premise remains. -/
theorem spatialGaussianSkeleton_eq_treePoint
    (K t : ℕ) (ht : t ≤ 2 ^ K) (x : DyadicNoiseSpace K) :
    spatialGaussianSkeleton K x t = gaussianSpatialPoint K x t := by
  revert ht
  induction t with
  | zero =>
      intro _
      simp
  | succ t ih =>
      intro ht
      have hlt : t < 2 ^ K := Nat.lt_of_succ_le ht
      have hprev := ih (Nat.le_of_lt hlt)
      have hs := spatialGaussianSkeleton_succ_sub K t hlt x
      have hp := gaussianSpatialPoint_succ_sub K t hlt x
      linarith

/-- Endpoint form at the full horizon. -/
theorem gaussianSpatialPoint_horizon
    (K : ℕ) (x : DyadicNoiseSpace K) :
    gaussianSpatialPoint K x (2 ^ K) = gaussianRootEndpoint K x := by
  calc
    gaussianSpatialPoint K x (2 ^ K) =
        spatialGaussianSkeleton K x (2 ^ K) :=
      (spatialGaussianSkeleton_eq_treePoint K (2 ^ K) le_rfl x).symm
    _ = gaussianRootEndpoint K x :=
      spatialGaussianSkeleton_horizon K x

/-!
THEOREM LIST
* `spatialCellIndex_injective`, `spatialCellIndex_bijective`
* `spatialLeafCell_bijective`, `spatialLeafCell_leftLeafIndex`,
  `spatialLeafCell_rightLeafIndex`, `spatialLeafCell_endpoints`
* `gaussianEndpoints_spatial_adjacent`,
  `gaussianEndpoints_spatial_first_left`
* `spatialGaussianUnitIncrement_map`,
  `spatialGaussianUnitIncrement_iIndep`
* `spatialPoissonUnitIncrement_map`,
  `spatialPoissonUnitIncrement_iIndep`, `coupledSpatialLeafLaws`
* `spatialGaussianSkeleton_succ_sub`,
  `spatialPoissonSkeleton_succ_sub`
* `gaussianLevel_parent_eq_children`, `gaussianLevel_sum_eq_root`,
  `poissonLevel_sum_eq_root`
* `spatialPoissonSkeleton_horizon`,
  `spatialGaussianSkeleton_horizon`
* `gaussianSpatialPoint_succ_sub`,
  `spatialGaussianSkeleton_eq_treePoint`,
  `gaussianSpatialPoint_horizon`

CLOSES
* Item 1: canonical binary spatial order, bijection, recursive left/right
  formulas, and the literal leaf interval `[j,j+1]`.
* Item 2: spatial Poisson and Gaussian skeletons on the same product space,
  independent unit laws, and both root identities.
* Item 3: consecutive leaf endpoints agree by the midpoint recursion, and the
  Gaussian partial-sum skeleton equals the tree endpoint value at every
  integer point in the horizon.

UNFINISHED
* No mathematical item is intentionally omitted.
END
-/

end Ripple.Kurtz.StrongApprox.DyadicSpatialSkeleton

end
