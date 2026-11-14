-- Ripple/Kurtz/StrongApprox/DyadicSpatialChainBridge.lean
import Mathlib
import Ripple.Kurtz.StrongApprox.DyadicSpatialSkeleton
import Ripple.Kurtz.StrongApprox.DyadicPathChain

noncomputable section

namespace Ripple.Kurtz.StrongApprox.DyadicSpatialChainBridge

open Set Finset
open scoped NNReal Nat BigOperators
open Ripple.Kurtz.StrongApprox
open DyadicGaussianTree DyadicPoissonTree
open DyadicSpatialSkeleton

theorem reassociateNoise_heq (r d : ℕ) (x : DyadicNoiseSpace (r + (d + 1))) :
    HEq (reassociateNoise r d x) x := by
  unfold reassociateNoise
  simp

theorem spatialDescendant_zero_heq (r : ℕ) (c : DyadicCell r) (j : Fin (2 ^ 0)) :
    HEq (spatialDescendant r 0 c j) c := by
  simp [spatialDescendant]

theorem spatialDescendant_left_heq (r d : ℕ) (c : DyadicCell r)
    (j : Fin (2 ^ (d + 1))) (h : j.val < 2 ^ d) :
    HEq (spatialDescendant r (d + 1) c j)
      (spatialDescendant (r + 1) d (Sum.inl c) ⟨j.val, h⟩) := by
  rw [spatialDescendant, dif_pos h]
  simp

theorem spatialDescendant_right_heq (r d : ℕ) (c : DyadicCell r)
    (j : Fin (2 ^ (d + 1))) (h : ¬ j.val < 2 ^ d) (hj : j.val - 2 ^ d < 2 ^ d) :
    HEq (spatialDescendant r (d + 1) c j)
      (spatialDescendant (r + 1) d (Sum.inr c) ⟨j.val - 2 ^ d, hj⟩) := by
  rw [spatialDescendant, dif_neg h]
  simp

theorem index_val_of_heq {n m : ℕ} (h : n = m) {a : DyadicCell n}
    {b : DyadicCell m} (hab : HEq a b) :
    (spatialCellIndex n a).val = (spatialCellIndex m b).val := by
  subst h
  cases hab
  rfl

theorem spatialDescendant_index (d : ℕ) :
    ∀ (r : ℕ) (c : DyadicCell r) (j : Fin (2 ^ d)),
      (spatialCellIndex (r + d) (spatialDescendant r d c j)).val =
        (spatialCellIndex r c).val * 2 ^ d + j.val := by
  induction d with
  | zero =>
      intro r c j
      have hj : j.val = 0 := by
        have := j.isLt
        simpa using this
      rw [hj]
      have := index_val_of_heq (by simp : r + 0 = r) (spatialDescendant_zero_heq r c j)
      simpa using this
  | succ d ih =>
      intro r c j
      by_cases h : j.val < 2 ^ d
      · have hh := index_val_of_heq (by omega : r + (d + 1) = r + 1 + d)
          (spatialDescendant_left_heq r d c j h)
        rw [hh, ih (r + 1) (Sum.inl c) ⟨j.val, h⟩]
        simp [spatialCellIndex, leftLeafIndex, pow_succ]
        ring
      · have hj : j.val - 2 ^ d < 2 ^ d := by
          have hjTop : j.val < 2 ^ (d + 1) := j.isLt
          have h2 : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
          omega
        have hh := index_val_of_heq (by omega : r + (d + 1) = r + 1 + d)
          (spatialDescendant_right_heq r d c j h hj)
        rw [hh, ih (r + 1) (Sum.inr c) ⟨j.val - 2 ^ d, hj⟩]
        simp [spatialCellIndex, rightLeafIndex]
        obtain ⟨k, hk⟩ : ∃ k, j.val = 2 ^ d + k := ⟨j.val - 2 ^ d, by omega⟩
        rw [hk, pow_succ]
        have : 2 ^ d + k - 2 ^ d = k := by omega
        rw [this]
        ring

/-- The leaf order of `DyadicPathChain` is the spatial order of
`DyadicSpatialSkeleton`. -/
theorem spatialDescendant_eq_spatialLeafCell (K : ℕ) (j : Fin (2 ^ K)) :
    (cast (by rw [Nat.zero_add]) (spatialDescendant 0 K () j) : DyadicCell K) =
      spatialLeafCell K j := by
  apply spatialCellIndex_injective K
  apply Fin.ext
  rw [spatialCellIndex_spatialLeafCell]
  have h1 := spatialDescendant_index K 0 () j
  have h0 : (spatialCellIndex 0 ()).val = 0 := rfl
  rw [h0] at h1
  have hc : HEq (cast (by rw [Nat.zero_add]) (spatialDescendant 0 K () j) :
      DyadicCell K) (spatialDescendant 0 K () j) := cast_heq _ _
  rw [index_val_of_heq (Nat.zero_add K).symm hc, h1]
  simp

/-- `SpatialLeafOrderAgreement` of `DyadicPathChain` with the canonical leaf
order, i.e. the PathChain leaf order is `spatialLeafCell`. -/
theorem spatialLeafOrder_agree (K : ℕ) (j : Fin (2 ^ K)) :
    (cast (by rw [Nat.zero_add]) (spatialDescendant 0 K () j) : DyadicCell K) =
      spatialLeafCell K j :=
  spatialDescendant_eq_spatialLeafCell K j

/-! ## Level-function transport along equal indices -/

theorem poissonLevel_heq {K K' : ℕ} (hK : K = K') {n m : ℕ} (h : n = m)
    {x : DyadicNoiseSpace n} {y : DyadicNoiseSpace m} (hxy : HEq x y)
    {a : DyadicCell n} {b : DyadicCell m} (hab : HEq a b) :
    poissonLevel K n x a = poissonLevel K' m y b := by
  subst hK
  subst h
  cases hxy
  cases hab
  rfl

theorem gaussianLevel_heq {K K' : ℕ} (hK : K = K') {n m : ℕ} (h : n = m)
    {x : DyadicNoiseSpace n} {y : DyadicNoiseSpace m} (hxy : HEq x y)
    {a : DyadicCell n} {b : DyadicCell m} (hab : HEq a b) :
    gaussianLevel K n x a = gaussianLevel K' m y b := by
  subst hK
  subst h
  cases hxy
  cases hab
  rfl

/-- Leaf count number `j` below `c` (zero outside the subtree). -/
def poissonLeaf (r d : ℕ) (x : DyadicNoiseSpace (r + d)) (c : DyadicCell r)
    (j : ℕ) : ℕ :=
  if h : j < 2 ^ d then
    poissonLevel (r + d) (r + d) x (spatialDescendant r d c ⟨j, h⟩)
  else 0

/-- Leaf Gaussian increment number `j` below `c`. -/
def gaussianLeaf (r d : ℕ) (x : DyadicNoiseSpace (r + d)) (c : DyadicCell r)
    (j : ℕ) : ℝ :=
  if h : j < 2 ^ d then
    gaussianLevel (r + d) (r + d) x (spatialDescendant r d c ⟨j, h⟩)
  else 0

theorem poissonLeaf_left (r d : ℕ) (x : DyadicNoiseSpace (r + (d + 1)))
    (c : DyadicCell r) {j : ℕ} (hj : j < 2 ^ d) :
    poissonLeaf r (d + 1) x c j =
      poissonLeaf (r + 1) d (reassociateNoise r d x) (Sum.inl c) j := by
  have hj' : j < 2 ^ (d + 1) := by rw [pow_succ]; omega
  unfold poissonLeaf
  rw [dif_pos hj', dif_pos hj]
  exact poissonLevel_heq (by omega) (by omega) (reassociateNoise_heq r d x).symm
    (spatialDescendant_left_heq r d c ⟨j, hj'⟩ hj)

theorem poissonLeaf_right (r d : ℕ) (x : DyadicNoiseSpace (r + (d + 1)))
    (c : DyadicCell r) {j : ℕ} (hj : j < 2 ^ d) :
    poissonLeaf r (d + 1) x c (2 ^ d + j) =
      poissonLeaf (r + 1) d (reassociateNoise r d x) (Sum.inr c) j := by
  have hj' : 2 ^ d + j < 2 ^ (d + 1) := by rw [pow_succ]; omega
  have hnot : ¬ (2 ^ d + j < 2 ^ d) := by omega
  have hsub : (2 ^ d + j) - 2 ^ d < 2 ^ d := by omega
  unfold poissonLeaf
  rw [dif_pos hj', dif_pos hj]
  refine poissonLevel_heq (by omega) (by omega) (reassociateNoise_heq r d x).symm ?_
  have h := spatialDescendant_right_heq r d c ⟨2 ^ d + j, hj'⟩ hnot hsub
  have e : (⟨(2 ^ d + j) - 2 ^ d, hsub⟩ : Fin (2 ^ d)) = ⟨j, hj⟩ :=
    Fin.ext (by simp)
  simpa [e] using h

theorem gaussianLeaf_left (r d : ℕ) (x : DyadicNoiseSpace (r + (d + 1)))
    (c : DyadicCell r) {j : ℕ} (hj : j < 2 ^ d) :
    gaussianLeaf r (d + 1) x c j =
      gaussianLeaf (r + 1) d (reassociateNoise r d x) (Sum.inl c) j := by
  have hj' : j < 2 ^ (d + 1) := by rw [pow_succ]; omega
  unfold gaussianLeaf
  rw [dif_pos hj', dif_pos hj]
  exact gaussianLevel_heq (by omega) (by omega) (reassociateNoise_heq r d x).symm
    (spatialDescendant_left_heq r d c ⟨j, hj'⟩ hj)

theorem gaussianLeaf_right (r d : ℕ) (x : DyadicNoiseSpace (r + (d + 1)))
    (c : DyadicCell r) {j : ℕ} (hj : j < 2 ^ d) :
    gaussianLeaf r (d + 1) x c (2 ^ d + j) =
      gaussianLeaf (r + 1) d (reassociateNoise r d x) (Sum.inr c) j := by
  have hj' : 2 ^ d + j < 2 ^ (d + 1) := by rw [pow_succ]; omega
  have hnot : ¬ (2 ^ d + j < 2 ^ d) := by omega
  have hsub : (2 ^ d + j) - 2 ^ d < 2 ^ d := by omega
  unfold gaussianLeaf
  rw [dif_pos hj', dif_pos hj]
  refine gaussianLevel_heq (by omega) (by omega) (reassociateNoise_heq r d x).symm ?_
  have h := spatialDescendant_right_heq r d c ⟨2 ^ d + j, hj'⟩ hnot hsub
  have e : (⟨(2 ^ d + j) - 2 ^ d, hsub⟩ : Fin (2 ^ d)) = ⟨j, hj⟩ :=
    Fin.ext (by simp)
  simpa [e] using h

theorem horizonNoise_zero_heq (r : ℕ) (x : DyadicNoiseSpace (r + 0)) :
    HEq (horizonNoise r 0 x) x := by
  unfold horizonNoise
  simp

/-! ## Aggregates and partial sums -/

theorem horizonCount_eq_sum_leaf (d : ℕ) :
    ∀ (r : ℕ) (x : DyadicNoiseSpace (r + d)) (c : DyadicCell r),
      horizonCount r d x c = ∑ j ∈ Finset.range (2 ^ d), poissonLeaf r d x c j := by
  induction d with
  | zero =>
      intro r x c
      simp only [pow_zero, Finset.range_one, Finset.sum_singleton]
      unfold horizonCount poissonLeaf
      simp only [pow_zero, Nat.lt_one_iff, dif_pos]
      exact poissonLevel_heq rfl (by simp) (horizonNoise_zero_heq r x)
        (spatialDescendant_zero_heq r c ⟨0, by simp⟩).symm
  | succ d ih =>
      intro r x c
      have hsplit : horizonCount r (d + 1) x c =
          horizonCount (r + 1) d (reassociateNoise r d x) (Sum.inl c) +
            horizonCount (r + 1) d (reassociateNoise r d x) (Sum.inr c) := by
        have h := poissonLevel_parent_eq_children (r + (d + 1)) r
          (horizonChildSource r d x) c
        have e : r + (d + 1) = r + 1 + d := by omega
        unfold horizonCount
        rw [horizonNoise_succ]
        rw [h]
        unfold horizonChildSource
        rw [e]
      rw [hsplit, ih (r + 1) (reassociateNoise r d x) (Sum.inl c),
        ih (r + 1) (reassociateNoise r d x) (Sum.inr c)]
      have h2 : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
      rw [h2, Finset.sum_range_add]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        exact (poissonLeaf_left r d x c (Finset.mem_range.mp hj)).symm
      · apply Finset.sum_congr rfl
        intro j hj
        exact (poissonLeaf_right r d x c (Finset.mem_range.mp hj)).symm

theorem horizonGaussian_eq_sum_leaf (d : ℕ) :
    ∀ (r : ℕ) (x : DyadicNoiseSpace (r + d)) (c : DyadicCell r),
      horizonGaussian r d x c = ∑ j ∈ Finset.range (2 ^ d), gaussianLeaf r d x c j := by
  induction d with
  | zero =>
      intro r x c
      simp only [pow_zero, Finset.range_one, Finset.sum_singleton]
      unfold horizonGaussian gaussianLeaf
      simp only [pow_zero, Nat.lt_one_iff, dif_pos]
      exact gaussianLevel_heq rfl (by simp) (horizonNoise_zero_heq r x)
        (spatialDescendant_zero_heq r c ⟨0, by simp⟩).symm
  | succ d ih =>
      intro r x c
      have hsplit : horizonGaussian r (d + 1) x c =
          horizonGaussian (r + 1) d (reassociateNoise r d x) (Sum.inl c) +
            horizonGaussian (r + 1) d (reassociateNoise r d x) (Sum.inr c) := by
        have h := gaussianLevel_parent_eq_children (r + (d + 1)) r
          (horizonChildSource r d x) c
        have e : r + (d + 1) = r + 1 + d := by omega
        unfold horizonGaussian
        rw [horizonNoise_succ]
        rw [h]
        unfold horizonChildSource
        rw [e]
      rw [hsplit, ih (r + 1) (reassociateNoise r d x) (Sum.inl c),
        ih (r + 1) (reassociateNoise r d x) (Sum.inr c)]
      have h2 : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
      rw [h2, Finset.sum_range_add]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        exact (gaussianLeaf_left r d x c (Finset.mem_range.mp hj)).symm
      · apply Finset.sum_congr rfl
        intro j hj
        exact (gaussianLeaf_right r d x c (Finset.mem_range.mp hj)).symm


theorem spatialPoissonPartial_eq_sum (d : ℕ) :
    ∀ (r : ℕ) (x : DyadicNoiseSpace (r + d)) (c : DyadicCell r) (t : ℕ),
      t ≤ 2 ^ d →
      spatialPoissonPartial r d x c t =
        ∑ j ∈ Finset.range t, poissonLeaf r d x c j := by
  induction d with
  | zero =>
      intro r x c t ht
      have htCases : t = 0 ∨ t = 1 := by simpa [Nat.le_one_iff_eq_zero_or_eq_one] using ht
      rcases htCases with rfl | rfl
      · simp [spatialPoissonPartial]
      · have h := horizonCount_eq_sum_leaf 0 r x c
        simpa [spatialPoissonPartial] using h
  | succ d ih =>
      intro r x c t ht
      by_cases hleft : t ≤ 2 ^ d
      · simp only [spatialPoissonPartial, hleft, if_true]
        rw [ih (r + 1) (reassociateNoise r d x) (Sum.inl c) t hleft]
        apply Finset.sum_congr rfl
        intro j hj
        exact (poissonLeaf_left r d x c
          (lt_of_lt_of_le (Finset.mem_range.mp hj) hleft)).symm
      · have hhalf : 2 ^ d ≤ t := le_of_not_ge hleft
        have hres : t - 2 ^ d ≤ 2 ^ d := by
          have h2 : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
          omega
        simp only [spatialPoissonPartial, hleft, if_false]
        rw [ih (r + 1) (reassociateNoise r d x) (Sum.inr c) (t - 2 ^ d) hres,
          horizonCount_eq_sum_leaf d (r + 1) (reassociateNoise r d x) (Sum.inl c)]
        obtain ⟨k, hk⟩ : ∃ k, t = 2 ^ d + k := ⟨t - 2 ^ d, by omega⟩
        rw [hk, Finset.sum_range_add]
        have hk' : 2 ^ d + k - 2 ^ d = k := by omega
        rw [hk']
        have hk2 : k ≤ 2 ^ d := by omega
        congr 1
        · apply Finset.sum_congr rfl
          intro j hj
          exact (poissonLeaf_left r d x c (Finset.mem_range.mp hj)).symm
        · apply Finset.sum_congr rfl
          intro j hj
          exact (poissonLeaf_right r d x c
            (lt_of_lt_of_le (Finset.mem_range.mp hj) hk2)).symm

theorem spatialGaussianPartial_eq_sum (d : ℕ) :
    ∀ (r : ℕ) (x : DyadicNoiseSpace (r + d)) (c : DyadicCell r) (t : ℕ),
      t ≤ 2 ^ d →
      spatialGaussianPartial r d x c t =
        ∑ j ∈ Finset.range t, gaussianLeaf r d x c j := by
  induction d with
  | zero =>
      intro r x c t ht
      have htCases : t = 0 ∨ t = 1 := by simpa [Nat.le_one_iff_eq_zero_or_eq_one] using ht
      rcases htCases with rfl | rfl
      · simp [spatialGaussianPartial]
      · have h := horizonGaussian_eq_sum_leaf 0 r x c
        simpa [spatialGaussianPartial] using h
  | succ d ih =>
      intro r x c t ht
      by_cases hleft : t ≤ 2 ^ d
      · simp only [spatialGaussianPartial, hleft, if_true]
        rw [ih (r + 1) (reassociateNoise r d x) (Sum.inl c) t hleft]
        apply Finset.sum_congr rfl
        intro j hj
        exact (gaussianLeaf_left r d x c
          (lt_of_lt_of_le (Finset.mem_range.mp hj) hleft)).symm
      · have hhalf : 2 ^ d ≤ t := le_of_not_ge hleft
        have hres : t - 2 ^ d ≤ 2 ^ d := by
          have h2 : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
          omega
        simp only [spatialGaussianPartial, hleft, if_false]
        rw [ih (r + 1) (reassociateNoise r d x) (Sum.inr c) (t - 2 ^ d) hres,
          horizonGaussian_eq_sum_leaf d (r + 1) (reassociateNoise r d x) (Sum.inl c)]
        obtain ⟨k, hk⟩ : ∃ k, t = 2 ^ d + k := ⟨t - 2 ^ d, by omega⟩
        rw [hk, Finset.sum_range_add]
        have hk' : 2 ^ d + k - 2 ^ d = k := by omega
        rw [hk']
        have hk2 : k ≤ 2 ^ d := by omega
        congr 1
        · apply Finset.sum_congr rfl
          intro j hj
          exact (gaussianLeaf_left r d x c (Finset.mem_range.mp hj)).symm
        · apply Finset.sum_congr rfl
          intro j hj
          exact (gaussianLeaf_right r d x c
            (lt_of_lt_of_le (Finset.mem_range.mp hj) hk2)).symm

/-! ## The skeletons of `DyadicSpatialSkeleton` are the `DyadicPathChain` ones -/

theorem rootSource_heq (K : ℕ) (x : DyadicNoiseSpace K) :
    HEq (rootSource K x) x := cast_heq _ _

theorem leaf_cell_heq (K : ℕ) (j : Fin (2 ^ K)) :
    HEq (spatialDescendant 0 K () j) (spatialLeafCell K j) := by
  have h := spatialDescendant_eq_spatialLeafCell K j
  exact (cast_heq _ _).symm.trans (heq_of_eq h)

theorem spatialPoissonSkeleton_agree (K : ℕ) (x : DyadicNoiseSpace K)
    {t : ℕ} (ht : t ≤ 2 ^ K) :
    Ripple.Kurtz.StrongApprox.spatialPoissonSkeleton K x t =
      DyadicSpatialSkeleton.spatialPoissonSkeleton K x t := by
  unfold Ripple.Kurtz.StrongApprox.spatialPoissonSkeleton
    DyadicSpatialSkeleton.spatialPoissonSkeleton
  rw [spatialPoissonPartial_eq_sum K 0 (rootSource K x) () t ht]
  apply Finset.sum_congr rfl
  intro j hj
  have hjK : j < 2 ^ K := lt_of_lt_of_le (Finset.mem_range.mp hj) ht
  unfold poissonLeaf spatialPoissonUnitIncrementNat
  rw [dif_pos hjK, dif_pos hjK]
  exact poissonLevel_heq (by omega) (by omega) (rootSource_heq K x)
    (leaf_cell_heq K ⟨j, hjK⟩)

theorem spatialGaussianSkeleton_agree (K : ℕ) (x : DyadicNoiseSpace K)
    {t : ℕ} (ht : t ≤ 2 ^ K) :
    Ripple.Kurtz.StrongApprox.spatialGaussianSkeleton K x t =
      DyadicSpatialSkeleton.spatialGaussianSkeleton K x t := by
  unfold Ripple.Kurtz.StrongApprox.spatialGaussianSkeleton
    DyadicSpatialSkeleton.spatialGaussianSkeleton
  rw [spatialGaussianPartial_eq_sum K 0 (rootSource K x) () t ht]
  apply Finset.sum_congr rfl
  intro j hj
  have hjK : j < 2 ^ K := lt_of_lt_of_le (Finset.mem_range.mp hj) ht
  unfold gaussianLeaf spatialGaussianUnitIncrementNat
  rw [dif_pos hjK, dif_pos hjK]
  exact gaussianLevel_heq (by omega) (by omega) (rootSource_heq K x)
    (leaf_cell_heq K ⟨j, hjK⟩)

/-- **K13 for the committed spatial skeletons**, with no
`LandedSkeletonSpatialAgreement` premise. -/
theorem spatialSkeleton_path_chain_committed (K : ℕ)
    (x : DyadicNoiseSpace K) {t : ℕ} (ht : t ≤ 2 ^ K) :
    |(DyadicSpatialSkeleton.spatialPoissonSkeleton K x t : ℝ) - (t : ℝ) -
        DyadicSpatialSkeleton.spatialGaussianSkeleton K x t| ≤
      2 * |horizonError 0 K (rootSource K x) ()| +
        2 * boundaryCorrectionAbs 0 K (rootSource K x) () t := by
  rw [← spatialPoissonSkeleton_agree K x ht, ← spatialGaussianSkeleton_agree K x ht]
  exact spatialSkeleton_path_chain K x ht

/-- The same with the K08 root bound substituted. -/
theorem spatialSkeleton_path_chain_committed_with_root (K : ℕ)
    (x : DyadicNoiseSpace K) {t : ℕ} (ht : t ≤ 2 ^ K) :
    |(DyadicSpatialSkeleton.spatialPoissonSkeleton K x t : ℝ) - (t : ℝ) -
        DyadicSpatialSkeleton.spatialGaussianSkeleton K x t| ≤
      2 * (1 + 2 * ((horizonNoise 0 K (rootSource K x)) ()) ^ 2) +
        2 * boundaryCorrectionAbs 0 K (rootSource K x) () t := by
  rw [← spatialPoissonSkeleton_agree K x ht, ← spatialGaussianSkeleton_agree K x ht]
  exact spatialSkeleton_path_chain_with_root K x ht

end Ripple.Kurtz.StrongApprox.DyadicSpatialChainBridge
end
