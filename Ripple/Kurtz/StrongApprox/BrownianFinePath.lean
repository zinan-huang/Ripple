-- Ripple/Kurtz/StrongApprox/BrownianFinePath.lean
import Ripple.Kurtz.StrongApprox.FineSchauderSeries
import Ripple.Kurtz.StrongApprox.DyadicConditionalPoissonPath

/-!
# Brownian candidate on the spatial horizon

`FineSchauderSeries` supplies:
* FineSchauderSeries.fineGaussianMeasure_isProbabilityMeasure
* FineSchauderSeries.measurable_fineSchauderLimit
* FineSchauderSeries.continuousOn_fineSchauderLimit
* FineSchauderSeries.fineSchauderLimit_natCast_zero
* FineSchauderSeries.fineSchauderSeries_ae

The tree supplies the committed integer skeleton via
DyadicSpatialSkeleton.spatialGaussianSkeleton.  `DyadicConditionalPoissonPath` supplies the
measurability of its unit-increment coordinates, in
DyadicConditionalPoissonPath.measurable_spatialGaussianUnitIncrementNat.

We use the two-factor independent product, tree × fine Gaussian.
The independent uniform-position factor of `DyadicConditionalPoissonPath` is not included: it can
be appended later without changing the tree or fine marginals.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace Ripple.Kurtz.StrongApprox.BrownianFinePath

open DyadicGaussianTree DyadicSpatialSkeleton
open FineSchauderSeries DyadicConditionalPoissonPath

/-- Independent tree increments and all fine Gaussian coordinates. -/
abbrev BrownianFineSpace (K : ℕ) :=
  DyadicNoiseSpace K × FineNoiseSpace K

noncomputable def brownianFineMeasure (K : ℕ) :
    Measure (BrownianFineSpace K) :=
  (dyadicNoiseMeasure K).prod (fineGaussianMeasure K)

instance brownianFineMeasure_isProbabilityMeasure (K : ℕ) :
    IsProbabilityMeasure (brownianFineMeasure K) := by
  unfold brownianFineMeasure
  infer_instance

theorem brownianFineMeasure_map_fst (K : ℕ) :
    (brownianFineMeasure K).map Prod.fst =
      dyadicNoiseMeasure K := by
  unfold brownianFineMeasure
  rw [Measure.map_fst_prod, measure_univ, one_smul]

theorem brownianFineMeasure_map_snd (K : ℕ) :
    (brownianFineMeasure K).map Prod.snd =
      fineGaussianMeasure K := by
  unfold brownianFineMeasure
  rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- Exact preservation of every measurable event on the original tree. -/
theorem brownianFineMeasure_treeEvent
    (K : ℕ) {A : Set (DyadicNoiseSpace K)}
    (hA : MeasurableSet A) :
    brownianFineMeasure K (Prod.fst ⁻¹' A) =
      dyadicNoiseMeasure K A := by
  rw [← Measure.map_apply measurable_fst hA,
    brownianFineMeasure_map_fst]

/-- A saturated linear ramp: 0 before j, t-j on [j,j+1], 1 after j+1. -/
def clippedRamp (j : ℕ) (t : ℝ) : ℝ :=
  min 1 (max 0 (t - j))

@[fun_prop]
theorem continuous_clippedRamp (j : ℕ) :
    Continuous (clippedRamp j) := by
  unfold clippedRamp
  fun_prop

private theorem clippedRamp_nat_of_lt
    (i j : ℕ) (h : i < j) :
    clippedRamp i (j : ℝ) = 1 := by
  have hcast : (1 : ℝ) ≤ (j : ℝ) - (i : ℝ) := by
    have hh : (i : ℝ) + 1 ≤ (j : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr h
    linarith
  unfold clippedRamp
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ (j : ℝ) - i)]
  exact min_eq_left hcast

private theorem clippedRamp_nat_of_le
    (i j : ℕ) (h : j ≤ i) :
    clippedRamp i (j : ℝ) = 0 := by
  have hcast : (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast h
  unfold clippedRamp
  rw [max_eq_left (by linarith : (j : ℝ) - i ≤ 0)]
  norm_num

/-- Linear interpolation of the committed integer Gaussian skeleton.
Each spatial leaf increment is spread uniformly over its own unit cell. -/
noncomputable def coarseGaussianInterpolation
    (K : ℕ) (x : DyadicNoiseSpace K) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (2 ^ K),
    spatialGaussianUnitIncrementNat K x i * clippedRamp i t

@[fun_prop]
theorem measurable_coarseGaussianInterpolation
    (K : ℕ) (t : ℝ) :
    Measurable (fun x : DyadicNoiseSpace K =>
      coarseGaussianInterpolation K x t) := by
  unfold coarseGaussianInterpolation
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_spatialGaussianUnitIncrementNat K i).mul measurable_const

@[fun_prop]
theorem continuous_coarseGaussianInterpolation
    (K : ℕ) (x : DyadicNoiseSpace K) :
    Continuous (coarseGaussianInterpolation K x) := by
  unfold coarseGaussianInterpolation
  exact continuous_finset_sum _ fun i _ =>
    continuous_const.mul (continuous_clippedRamp i)

/-- At every committed integer, the ramp sum telescopes to the skeleton.
This includes the right endpoint j = 2^K. -/
theorem coarseGaussianInterpolation_natCast
    (K j : ℕ) (hj : j ≤ 2 ^ K) (x : DyadicNoiseSpace K) :
    coarseGaussianInterpolation K x (j : ℝ) =
      DyadicSpatialSkeleton.spatialGaussianSkeleton K x j := by
  unfold coarseGaussianInterpolation
  conv_lhs =>
    rw [← Nat.add_sub_of_le hj, Finset.sum_range_add]
  have hfirst :
      (∑ i ∈ Finset.range j,
        spatialGaussianUnitIncrementNat K x i * clippedRamp i (j : ℝ)) =
      ∑ i ∈ Finset.range j, spatialGaussianUnitIncrementNat K x i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [clippedRamp_nat_of_lt i j (Finset.mem_range.mp hi)]
    ring
  have hsecond :
      (∑ i ∈ Finset.range (2 ^ K - j),
        spatialGaussianUnitIncrementNat K x (j + i) *
          clippedRamp (j + i) (j : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [clippedRamp_nat_of_le (j + i) j (Nat.le_add_right j i)]
    ring
  rw [hfirst, hsecond, add_zero]
  rfl

/-- The fine series is already totalized to zero off its convergence event. -/
noncomputable def brownianCandidate
    (K : ℕ) (t : ℝ) (ω : BrownianFineSpace K) : ℝ :=
  coarseGaussianInterpolation K ω.1 t +
    fineSchauderLimit K ω.2 t

@[fun_prop]
theorem measurable_brownianCandidate (K : ℕ) (t : ℝ) :
    Measurable (brownianCandidate K t) := by
  unfold brownianCandidate
  exact ((measurable_coarseGaussianInterpolation K t).comp
    measurable_fst).add
    ((measurable_fineSchauderLimit K t).comp measurable_snd)

/-- Pointwise integer pinning, with no exceptional set. -/
theorem brownianCandidate_natCast
    (K j : ℕ) (hj : j ≤ 2 ^ K) (ω : BrownianFineSpace K) :
    brownianCandidate K (j : ℝ) ω =
      DyadicSpatialSkeleton.spatialGaussianSkeleton K ω.1 j := by
  rw [brownianCandidate,
    coarseGaussianInterpolation_natCast K j hj ω.1,
    fineSchauderLimit_natCast_zero K j ω.2, add_zero]

/-- Continuous on [0,2^K] for every sample, in particular almost surely.
The zero-off-event convention in `FineSchauderSeries` makes the stronger assertion valid. -/
theorem continuousOn_brownianCandidate
    (K : ℕ) (ω : BrownianFineSpace K) :
    ContinuousOn (fun t => brownianCandidate K t ω)
      (Icc (0 : ℝ) (2 ^ K : ℕ)) := by
  change ContinuousOn
    (fun t => coarseGaussianInterpolation K ω.1 t +
      fineSchauderLimit K ω.2 t)
    (Icc (0 : ℝ) (2 ^ K : ℕ))
  exact (continuous_coarseGaussianInterpolation K ω.1).continuousOn.add
    (continuousOn_fineSchauderLimit K ω.2)

/-- The requested almost-sure continuity statement. -/
theorem continuousOn_brownianCandidate_ae (K : ℕ) :
    ∀ᵐ ω ∂brownianFineMeasure K,
      ContinuousOn (fun t => brownianCandidate K t ω)
        (Icc (0 : ℝ) (2 ^ K : ℕ)) :=
  Filter.Eventually.of_forall (continuousOn_brownianCandidate K)

/-!
THEOREM LIST
* brownianFineMeasure_map_fst, brownianFineMeasure_map_snd
* brownianFineMeasure_treeEvent
* clippedRamp_nat_of_lt, clippedRamp_nat_of_le
* measurable_coarseGaussianInterpolation
* continuous_coarseGaussianInterpolation
* coarseGaussianInterpolation_natCast
* measurable_brownianCandidate
* brownianCandidate_natCast
* continuousOn_brownianCandidate
* continuousOn_brownianCandidate_ae

CLOSES
* Item 1: two-factor independent source and exact tree marginal.
* Item 2: linear interpolation plus fine series, integer pinning,
  point-evaluation measurability and even pointwise continuity on the horizon.

UNFINISHED
* Item 3: independence and the joint Gaussian law of all fine dyadic
  increment vectors. No dyadic-increment law is asserted in this file.
* Attaching the `DyadicConditionalPoissonPath` uniform positions as a third independent factor.
-/

end Ripple.Kurtz.StrongApprox.BrownianFinePath
