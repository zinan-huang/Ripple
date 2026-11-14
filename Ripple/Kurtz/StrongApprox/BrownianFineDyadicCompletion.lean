-- Ripple/Kurtz/StrongApprox/BrownianFineDyadicCompletion.lean
import Ripple.Kurtz.StrongApprox.BrownianFineDyadicAllLevels
import Ripple.Kurtz.StrongApprox.DyadicSpatialChainBridge

/-!
# Completion of the finite-horizon Brownian construction

Declarations of `BrownianFineDyadicAllLevels` used here:
* `brownianCandidate_entropyFineCell_map`;
* `brownianCandidate_entropyFineCell_iIndep`.

Declarations of `BrownianFinePath` used here:
* `brownianCandidate`, `measurable_brownianCandidate`;
* `brownianCandidate_natCast`;
* `continuousOn_brownianCandidate`;
* `brownianFineMeasure_map_fst`.

The coarse proof uses the tree-level product law
`gaussianLevel_measurePreserving` through `horizonGaussian`; it does not
reprove the Gaussian block-sum law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal NNReal BigOperators Nat Topology

namespace Ripple.Kurtz.StrongApprox.BrownianFineDyadicCompletion

open BrownianFinePath BrownianFineDyadicAllLevels
open FineSchauderSeries DyadicGaussianTree DyadicSpatialSkeleton
open DyadicSpatialChainBridge

/-! ## Global clamping -/

/-- Projection of the real line onto the construction horizon. -/
def brownianClamp (K : ℕ) (t : ℝ) : ℝ :=
  max 0 (min t ((2 : ℝ) ^ K))

@[fun_prop]
theorem continuous_brownianClamp (K : ℕ) :
    Continuous (brownianClamp K) := by
  unfold brownianClamp
  fun_prop

theorem brownianClamp_mem (K : ℕ) (t : ℝ) :
    brownianClamp K t ∈ Icc (0 : ℝ) ((2 : ℝ) ^ K) := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by positivity) (min_le_right _ _)

@[simp] theorem brownianClamp_eq_of_mem
    (K : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) ((2 : ℝ) ^ K)) :
    brownianClamp K t = t := by
  unfold brownianClamp
  rw [min_eq_left ht.2, max_eq_right ht.1]

/-- The total path is the finite-horizon candidate composed with clamping. -/
noncomputable def brownianPath
    (K : ℕ) (t : ℝ) (omega : BrownianFineSpace K) : ℝ :=
  brownianCandidate K (brownianClamp K t) omega

@[simp] theorem brownianPath_eq_candidate_of_mem
    (K : ℕ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) ((2 : ℝ) ^ K))
    (omega : BrownianFineSpace K) :
    brownianPath K t omega = brownianCandidate K t omega := by
  rw [brownianPath, brownianClamp_eq_of_mem K ht]

@[fun_prop]
theorem measurable_brownianPath (K : ℕ) (t : ℝ) :
    Measurable (brownianPath K t) := by
  simpa [brownianPath] using
    measurable_brownianCandidate K (brownianClamp K t)

/-- Clamping turns horizon continuity into global continuity, pointwise. -/
theorem continuous_brownianPath
    (K : ℕ) (omega : BrownianFineSpace K) :
    Continuous (fun t => brownianPath K t omega) := by
  change Continuous
    ((fun s => brownianCandidate K s omega) ∘ brownianClamp K)
  have hcont :
      ContinuousOn (fun s => brownianCandidate K s omega)
        (Icc (0 : ℝ) ((2 : ℝ) ^ K)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      continuousOn_brownianCandidate K omega
  exact hcont.comp_continuous
    (continuous_brownianClamp K) (brownianClamp_mem K)

private theorem brownianDyadicPoint_mem_horizon
    (K m q : ℕ) (hq : q ≤ 2 ^ m) :
    brownianDyadicPoint ((2 : ℝ) ^ K) m q ∈
      Icc (0 : ℝ) ((2 : ℝ) ^ K) := by
  unfold brownianDyadicPoint
  have hp : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  constructor
  · positivity
  · rw [div_le_iff₀ hp]
    have hqR : (q : ℝ) ≤ (2 : ℝ) ^ m := by
      exact_mod_cast hq
    exact mul_le_mul_of_nonneg_left hqR (by positivity)

/-- Every entropy-grid increment is unchanged by the clamp. -/
@[simp] theorem brownianPath_dyadicIncrement_eq_candidate
    (K m : ℕ) (k : Fin (2 ^ m))
    (omega : BrownianFineSpace K) :
    brownianPath K
          (brownianDyadicPoint ((2 : ℝ) ^ K) m (k.val + 1)) omega -
        brownianPath K
          (brownianDyadicPoint ((2 : ℝ) ^ K) m k.val) omega =
      brownianCandidate K
          (brownianDyadicPoint ((2 : ℝ) ^ K) m (k.val + 1)) omega -
        brownianCandidate K
          (brownianDyadicPoint ((2 : ℝ) ^ K) m k.val) omega := by
  have hkRight : k.val + 1 ≤ 2 ^ m :=
    Nat.succ_le_iff.mpr k.isLt
  have hkLeft : k.val ≤ 2 ^ m := k.isLt.le
  rw [brownianPath_eq_candidate_of_mem K
      (brownianDyadicPoint_mem_horizon K m (k.val + 1) hkRight),
    brownianPath_eq_candidate_of_mem K
      (brownianDyadicPoint_mem_horizon K m k.val hkLeft)]

/-! ## Coarse tree levels -/

/-- Reassociation only changes the parenthesization of the depth index. -/
private theorem reassociateNoise_measurePreserving
    (r d : ℕ) :
    MeasurePreserving (reassociateNoise r d)
      (dyadicNoiseMeasure (r + (d + 1)))
      (dyadicNoiseMeasure ((r + 1) + d)) := by
  have h : r + (d + 1) = (r + 1) + d := by omega
  have hfun : reassociateNoise r d =
      fun x => cast (congrArg DyadicNoiseSpace h) x := by
    funext x
    apply eq_of_heq
    exact (reassociateNoise_heq r d x).trans (cast_heq _ x).symm
  rw [hfun]
  clear hfun
  generalize (r + 1) + d = b at h ⊢
  subst h
  exact MeasurePreserving.id _

/-- The recursively exposed level-`r` source has the correct marginal law. -/
private theorem horizonNoise_measurePreserving :
    ∀ r d : ℕ,
      MeasurePreserving (horizonNoise r d)
        (dyadicNoiseMeasure (r + d)) (dyadicNoiseMeasure r)
  | r, 0 => by
      simpa [horizonNoise] using
        (MeasurePreserving.id (dyadicNoiseMeasure r))
  | r, d + 1 => by
      have hchild :
          MeasurePreserving
            (fun x : DyadicNoiseSpace (r + (d + 1)) =>
              horizonNoise (r + 1) d (reassociateNoise r d x))
            (dyadicNoiseMeasure (r + (d + 1)))
            (dyadicNoiseMeasure (r + 1)) := by
        simpa [Function.comp_def] using
          (horizonNoise_measurePreserving (r + 1) d).comp
            (reassociateNoise_measurePreserving r d)
      have hfst :
          MeasurePreserving
            (fun p : DyadicNoiseSpace r × DyadicFreshSpace r => p.1)
            ((dyadicNoiseMeasure r).prod (dyadicFreshMeasure r))
            (dyadicNoiseMeasure r) := measurePreserving_fst
      have hdrop :
          MeasurePreserving
            (fun x : DyadicNoiseSpace (r + 1) =>
              (dyadicNoiseSplit r x).1)
            (dyadicNoiseMeasure (r + 1))
            (dyadicNoiseMeasure r) :=
        hfst.comp (dyadicNoiseSplit_measurePreserving r)
      have h := hdrop.comp hchild
      simpa [horizonNoise, Function.comp_def] using h

/-- Exact joint Gaussian law of the chronological coarse-tree increments. -/
private theorem horizonGaussian_measurePreserving
    (r d : ℕ) :
    MeasurePreserving (horizonGaussian r d)
      (dyadicNoiseMeasure (r + d))
      (Measure.pi fun _ : DyadicCell r =>
        gaussianReal 0 (dyadicVariance (r + d) r)) := by
  simpa [horizonGaussian, Function.comp_def] using
    (gaussianLevel_measurePreserving (r + d) r).comp
      (horizonNoise_measurePreserving r d)

private theorem horizonGaussian_component_map
    (r d : ℕ) (c : DyadicCell r) :
    (dyadicNoiseMeasure (r + d)).map
        (fun x => horizonGaussian r d x c) =
      gaussianReal 0 (dyadicVariance (r + d) r) :=
  vectorComponent_map_eq
    (horizonGaussian_measurePreserving r d).measurable
    (horizonGaussian_measurePreserving r d).map_eq c

private theorem horizonGaussian_iIndep
    (r d : ℕ) :
    iIndepFun (fun c x => horizonGaussian r d x c)
      (dyadicNoiseMeasure (r + d)) :=
  iIndepFun_of_vector_map_eq_pi
    (horizonGaussian_measurePreserving r d).measurable
    (horizonGaussian_measurePreserving r d).map_eq

/-- Global leaf number `q` inside chronological coarse cell `k`. -/
def coarseLeafIndex
    (m d : ℕ) (k : Fin (2 ^ m)) (q : Fin (2 ^ d)) :
    Fin (2 ^ (m + d)) :=
  ⟨k.val * 2 ^ d + q.val, by
    have hfirst :
        k.val * 2 ^ d + q.val < (k.val + 1) * 2 ^ d := by
      calc
        k.val * 2 ^ d + q.val <
            k.val * 2 ^ d + 2 ^ d :=
          Nat.add_lt_add_left q.isLt _
        _ = (k.val + 1) * 2 ^ d := by ring
    have hblock :
        (k.val + 1) * 2 ^ d ≤ 2 ^ m * 2 ^ d :=
      Nat.mul_le_mul_right (2 ^ d) (Nat.succ_le_iff.mpr k.isLt)
    calc
      k.val * 2 ^ d + q.val < 2 ^ m * 2 ^ d :=
        hfirst.trans_le hblock
      _ = 2 ^ (m + d) := by rw [pow_add]⟩

private theorem spatialDescendant_coarseLeaf
    (m d : ℕ) (k : Fin (2 ^ m)) (q : Fin (2 ^ d)) :
    spatialDescendant m d (spatialLeafCell m k) q =
      spatialLeafCell (m + d) (coarseLeafIndex m d k q) := by
  apply spatialCellIndex_injective (m + d)
  apply Fin.ext
  rw [spatialDescendant_index,
    spatialCellIndex_spatialLeafCell,
    spatialCellIndex_spatialLeafCell]
  rfl

private theorem gaussianLeaf_eq_spatialUnit
    (m d : ℕ) (x : DyadicNoiseSpace (m + d))
    (k : Fin (2 ^ m)) (q : Fin (2 ^ d)) :
    gaussianLeaf m d x (spatialLeafCell m k) q.val =
      spatialGaussianUnitIncrement (m + d)
        (coarseLeafIndex m d k q) x := by
  unfold gaussianLeaf spatialGaussianUnitIncrement
  rw [dif_pos q.isLt, spatialDescendant_coarseLeaf]

/-- A coarse tree increment is the sum of its consecutive spatial leaves. -/
private theorem horizonGaussian_eq_coarseSum
    (m d : ℕ) (x : DyadicNoiseSpace (m + d))
    (k : Fin (2 ^ m)) :
    horizonGaussian m d x (spatialLeafCell m k) =
      ∑ q : Fin (2 ^ d),
        spatialGaussianUnitIncrement (m + d)
          (coarseLeafIndex m d k q) x := by
  rw [horizonGaussian_eq_sum_leaf d m x (spatialLeafCell m k)]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro q _
  exact gaussianLeaf_eq_spatialUnit m d x k q

/-- Difference of the committed skeleton at consecutive coarse endpoints. -/
private theorem spatialGaussianSkeleton_block_sub
    (m d : ℕ) (x : DyadicNoiseSpace (m + d))
    (k : Fin (2 ^ m)) :
    DyadicSpatialSkeleton.spatialGaussianSkeleton (m + d) x
          ((k.val + 1) * 2 ^ d) -
        DyadicSpatialSkeleton.spatialGaussianSkeleton (m + d) x
          (k.val * 2 ^ d) =
      ∑ q : Fin (2 ^ d),
        spatialGaussianUnitIncrement (m + d)
          (coarseLeafIndex m d k q) x := by
  unfold DyadicSpatialSkeleton.spatialGaussianSkeleton
  have hsplit :
      (k.val + 1) * 2 ^ d = k.val * 2 ^ d + 2 ^ d := by ring
  rw [hsplit, Finset.sum_range_add, add_sub_cancel_left]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro q _
  have hlt : k.val * 2 ^ d + q.val < 2 ^ (m + d) :=
    (coarseLeafIndex m d k q).isLt
  rw [DyadicSpatialSkeleton.spatialGaussianUnitIncrementNat,
    dif_pos hlt]
  have hfin :
      (⟨k.val * 2 ^ d + q.val, hlt⟩ : Fin (2 ^ (m + d))) =
        coarseLeafIndex m d k q := by
    apply Fin.ext
    rfl
  rw [hfin]

private theorem coarseDyadicPoint_left
    (m d : ℕ) (k : Fin (2 ^ m)) :
    brownianDyadicPoint ((2 : ℝ) ^ (m + d)) m k.val =
      ((k.val * 2 ^ d : ℕ) : ℝ) := by
  unfold brownianDyadicPoint
  rw [pow_add]
  push_cast
  field_simp [pow_ne_zero m (by norm_num : (2 : ℝ) ≠ 0)]
  try ring

private theorem coarseDyadicPoint_right
    (m d : ℕ) (k : Fin (2 ^ m)) :
    brownianDyadicPoint ((2 : ℝ) ^ (m + d)) m (k.val + 1) =
      (((k.val + 1) * 2 ^ d : ℕ) : ℝ) := by
  unfold brownianDyadicPoint
  rw [pow_add]
  push_cast
  field_simp [pow_ne_zero m (by norm_num : (2 : ℝ) ≠ 0)]
  try ring

private theorem coarseMesh_eq_variance (m d : ℕ) :
    Real.toNNReal
        (brownianDyadicMesh ((2 : ℝ) ^ (m + d)) m) =
      dyadicVariance (m + d) m := by
  apply NNReal.coe_injective
  change
    (Real.toNNReal
      ((2 : ℝ) ^ (m + d) / (2 : ℝ) ^ m) : ℝ) =
      (2 : ℝ) ^ (m + d) / (2 : ℝ) ^ m
  rw [Real.coe_toNNReal _ (by positivity)]

/-- The entropy coarse-cell increment is exactly its tree increment. -/
@[simp] theorem brownianPath_coarseCell_eq_horizonGaussian
    (m d : ℕ) (k : Fin (2 ^ m))
    (omega : BrownianFineSpace (m + d)) :
    brownianPath (m + d)
          (brownianDyadicPoint ((2 : ℝ) ^ (m + d)) m
            (k.val + 1)) omega -
        brownianPath (m + d)
          (brownianDyadicPoint ((2 : ℝ) ^ (m + d)) m
            k.val) omega =
      horizonGaussian m d omega.1 (spatialLeafCell m k) := by
  rw [coarseDyadicPoint_right, coarseDyadicPoint_left]
  have hkRight : (k.val + 1) * 2 ^ d ≤ 2 ^ (m + d) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right (2 ^ d)
      (Nat.succ_le_iff.mpr k.isLt)
  have hkLeft : k.val * 2 ^ d ≤ 2 ^ (m + d) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right (2 ^ d) k.isLt.le
  have hrightMem :
      ((((k.val + 1) * 2 ^ d : ℕ) : ℝ)) ∈
        Icc (0 : ℝ) ((2 : ℝ) ^ (m + d)) := by
    constructor
    · positivity
    · exact_mod_cast hkRight
  have hleftMem :
      (((k.val * 2 ^ d : ℕ) : ℝ)) ∈
        Icc (0 : ℝ) ((2 : ℝ) ^ (m + d)) := by
    constructor
    · positivity
    · exact_mod_cast hkLeft
  calc
    brownianPath (m + d)
          (((k.val + 1) * 2 ^ d : ℕ) : ℝ) omega -
        brownianPath (m + d)
          ((k.val * 2 ^ d : ℕ) : ℝ) omega =
      brownianCandidate (m + d)
          (((k.val + 1) * 2 ^ d : ℕ) : ℝ) omega -
        brownianCandidate (m + d)
          ((k.val * 2 ^ d : ℕ) : ℝ) omega := by
            rw [brownianPath_eq_candidate_of_mem (m + d) hrightMem,
              brownianPath_eq_candidate_of_mem (m + d) hleftMem]
    _ = DyadicSpatialSkeleton.spatialGaussianSkeleton (m + d)
          omega.1 ((k.val + 1) * 2 ^ d) -
        DyadicSpatialSkeleton.spatialGaussianSkeleton (m + d)
          omega.1 (k.val * 2 ^ d) := by
            rw [brownianCandidate_natCast (m + d)
                ((k.val + 1) * 2 ^ d) hkRight,
              brownianCandidate_natCast (m + d)
                (k.val * 2 ^ d) hkLeft]
    _ = ∑ q : Fin (2 ^ d),
        spatialGaussianUnitIncrement (m + d)
          (coarseLeafIndex m d k q) omega.1 :=
      spatialGaussianSkeleton_block_sub m d omega.1 k
    _ = horizonGaussian m d omega.1 (spatialLeafCell m k) :=
      (horizonGaussian_eq_coarseSum m d omega.1 k).symm

/-- Coarse entropy-cell marginal law. -/
theorem brownianPath_entropyCoarseCell_map
    (m d : ℕ) (k : Fin (2 ^ m)) :
    (brownianFineMeasure (m + d)).map
        (fun omega =>
          brownianPath (m + d)
              (brownianDyadicPoint ((2 : ℝ) ^ (m + d)) m
                (k.val + 1)) omega -
            brownianPath (m + d)
              (brownianDyadicPoint ((2 : ℝ) ^ (m + d)) m
                k.val) omega) =
      gaussianReal 0
        (Real.toNNReal
          (brownianDyadicMesh ((2 : ℝ) ^ (m + d)) m)) := by
  let g : DyadicNoiseSpace (m + d) → ℝ := fun x =>
    horizonGaussian m d x (spatialLeafCell m k)
  have hg : Measurable g :=
    (measurable_pi_apply (spatialLeafCell m k)).comp
      (horizonGaussian_measurePreserving m d).measurable
  have hfun :
      (fun omega : BrownianFineSpace (m + d) =>
        brownianPath (m + d)
            (brownianDyadicPoint ((2 : ℝ) ^ (m + d)) m
              (k.val + 1)) omega -
          brownianPath (m + d)
            (brownianDyadicPoint ((2 : ℝ) ^ (m + d)) m
              k.val) omega) =
        (fun omega => g omega.1) := by
    funext omega
    exact brownianPath_coarseCell_eq_horizonGaussian m d k omega
  rw [hfun]
  calc
    (brownianFineMeasure (m + d)).map (fun omega => g omega.1) =
        (dyadicNoiseMeasure (m + d)).map g := by
      simpa [brownianFineMeasure] using
        (map_comp_fst (dyadicNoiseMeasure (m + d))
          (fineGaussianMeasure (m + d)) hg)
    _ = gaussianReal 0 (dyadicVariance (m + d) m) :=
      horizonGaussian_component_map m d (spatialLeafCell m k)
    _ = gaussianReal 0
        (Real.toNNReal
          (brownianDyadicMesh ((2 : ℝ) ^ (m + d)) m)) := by
      rw [coarseMesh_eq_variance]

/-- Coarse entropy-cell independence. -/
theorem brownianPath_entropyCoarseCell_iIndep
    (m d : ℕ) :
    iIndepFun
      (fun (k : Fin (2 ^ m)) omega =>
        brownianPath (m + d)
            (brownianDyadicPoint ((2 : ℝ) ^ (m + d)) m
              (k.val + 1)) omega -
          brownianPath (m + d)
            (brownianDyadicPoint ((2 : ℝ) ^ (m + d)) m
              k.val) omega)
      (brownianFineMeasure (m + d)) := by
  have htree :
      iIndepFun
        (fun (k : Fin (2 ^ m)) x =>
          horizonGaussian m d x (spatialLeafCell m k))
        (dyadicNoiseMeasure (m + d)) :=
    (horizonGaussian_iIndep m d).precomp
      (spatialLeafCell_injective m)
  have hprod :=
    iIndepFun_comp_fst (fineGaussianMeasure (m + d)) htree
  simpa only [brownianFineMeasure,
    brownianPath_coarseCell_eq_horizonGaussian] using hprod

/-! ## Every entropy level and the final interface -/

/-- Exact Gaussian cell law at every entropy level. -/
theorem brownianPath_cell_map
    (K m : ℕ) (k : Fin (2 ^ m)) :
    (brownianFineMeasure K).map
        (fun omega =>
          brownianPath K
              (brownianDyadicPoint ((2 : ℝ) ^ K) m
                (k.val + 1)) omega -
            brownianPath K
              (brownianDyadicPoint ((2 : ℝ) ^ K) m
                k.val) omega) =
      gaussianReal 0
        (Real.toNNReal
          (brownianDyadicMesh ((2 : ℝ) ^ K) m)) := by
  by_cases hmK : m < K
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmK.le
    exact brownianPath_entropyCoarseCell_map m d k
  · have hKm : K ≤ m := Nat.le_of_not_gt hmK
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hKm
    simpa only [brownianPath_dyadicIncrement_eq_candidate] using
      brownianCandidate_entropyFineCell_map K r k

/-- Exact independence of every finite entropy-level increment family. -/
theorem brownianPath_cell_iIndep
    (K m : ℕ) :
    iIndepFun
      (fun (k : Fin (2 ^ m)) omega =>
        brownianPath K
            (brownianDyadicPoint ((2 : ℝ) ^ K) m
              (k.val + 1)) omega -
          brownianPath K
            (brownianDyadicPoint ((2 : ℝ) ^ K) m
              k.val) omega)
      (brownianFineMeasure K) := by
  by_cases hmK : m < K
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmK.le
    exact brownianPath_entropyCoarseCell_iIndep m d
  · have hKm : K ≤ m := Nat.le_of_not_gt hmK
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hKm
    simpa only [brownianPath_dyadicIncrement_eq_candidate] using
      brownianCandidate_entropyFineCell_iIndep K r

/-- The clamped path is a complete `DyadicBrownianOn` input on `[0,2^K]`. -/
theorem brownianPath_dyadicBrownianOn (K : ℕ) :
    DyadicBrownianOn (brownianFineMeasure K)
      (brownianPath K) ((2 : ℝ) ^ K) where
  eval_measurable := measurable_brownianPath K
  continuous_ae :=
    Filter.Eventually.of_forall (continuous_brownianPath K)
  cell_law := brownianPath_cell_map K
  cell_independent := brownianPath_cell_iIndep K

/-!
THEOREM LIST
* `continuous_brownianClamp`, `brownianClamp_mem`
* `brownianPath_eq_candidate_of_mem`
* `measurable_brownianPath`, `continuous_brownianPath`
* `brownianPath_dyadicIncrement_eq_candidate`
* `brownianPath_coarseCell_eq_horizonGaussian`
* `brownianPath_entropyCoarseCell_map`
* `brownianPath_entropyCoarseCell_iIndep`
* `brownianPath_cell_map`, `brownianPath_cell_iIndep`
* `brownianPath_dyadicBrownianOn`

CLOSES
* Item 1: clamped global path, pointwise global continuity, measurable
  evaluations, and agreement with `brownianCandidate` on the horizon.
* Item 2: all coarse levels `m < K`, using the existing Gaussian-tree product
  law and the spatial descendant adapter.
* Item 3: all four fields of `DyadicBrownianOn`.

UNFINISHED
* Item 4: the `hOsc` producer on a common tree × fine-Gaussian × uniform-position
  source, its two measure-preserving projections, and the no-premise
  continuous-time KMT theorem.  No statement about that three-factor source is
  asserted in this file.
END
-/

end Ripple.Kurtz.StrongApprox.BrownianFineDyadicCompletion

end
