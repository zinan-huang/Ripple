-- Ripple/Kurtz/StrongApprox/ContinuousEndpointTail.lean
import Ripple.Kurtz.StrongApprox.ContinuousFiniteHorizonKMT
import Ripple.Kurtz.StrongApprox.DyadicBridgeError
import Ripple.Kurtz.StrongApprox.BrownianEntropyModulus

/-!
# A horizon-endpoint tail uniform in the dyadic depth

The root Poisson count is the Poisson quantile of the root standard normal.
`root_bridgeError_le` is the exact bridge to
`PoissonQuantileBound.poisson_quantile_bound`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Nat

namespace Ripple.Kurtz.StrongApprox.ContinuousEndpointTail

open DyadicGaussianTree DyadicPoissonTree
open DyadicSpatialSkeleton DyadicFiniteHorizonUnion
open ContinuousFiniteHorizonKMT

/-- Additive endpoint shift, independent of the depth. -/
def continuousEndpointShift : ℝ := 1

/-- Endpoint-tail prefactor, independent of the depth. -/
def continuousEndpointPrefactor : ℝ := 2

/-- Endpoint-tail exponential rate, independent of the depth. -/
def continuousEndpointRate : ℝ := 1 / 4

/-- The recursively retained root source has its original one-coordinate law. -/
private theorem dyadicRootRestrict_measurePreserving :
    ∀ K : ℕ,
      MeasurePreserving (dyadicRootRestrict K)
        (dyadicNoiseMeasure K) (dyadicNoiseMeasure 0)
  | 0 => by
      simpa [dyadicRootRestrict] using
        (MeasurePreserving.id (dyadicNoiseMeasure 0))
  | K + 1 => by
      have hfirst :
          MeasurePreserving
            (fun p : DyadicNoiseSpace K × DyadicFreshSpace K => p.1)
            ((dyadicNoiseMeasure K).prod (dyadicFreshMeasure K))
            (dyadicNoiseMeasure K) :=
        measurePreserving_fst
      have h :=
        (dyadicRootRestrict_measurePreserving K).comp
          (hfirst.comp (dyadicNoiseSplit_measurePreserving K))
      simpa [dyadicRootRestrict, Function.comp_def] using h

/-- The tree projection from the common continuous KMT source. -/
private theorem continuousKMTTree_measurePreserving (K : ℕ) :
    MeasurePreserving
      (fun omega : ContinuousKMTSpace K => omega.1.1)
      (continuousKMTMeasure K) (dyadicNoiseMeasure K) :=
  ⟨measurable_fst.comp measurable_fst,
    continuousKMTMeasure_map_tree K⟩

/-- Evaluation of the unique level-zero coordinate. -/
private theorem dyadicRootEval_measurePreserving :
    MeasurePreserving
      (fun x : DyadicNoiseSpace 0 => x ())
      (dyadicNoiseMeasure 0) (gaussianReal 0 1) := by
  simpa [dyadicNoiseMeasure] using
    (measurePreserving_eval
      (fun _ : DyadicNoise 0 => gaussianReal 0 1) ())

/-- The standard normal which drives the root quantile coupling. -/
noncomputable def continuousKMTRootNormal
    (K : ℕ) (omega : ContinuousKMTSpace K) : ℝ :=
  dyadicRootRestrict K omega.1.1 ()

/-- The root coordinate is standard normal under every depth-`K` law. -/
theorem continuousKMTRootNormal_measurePreserving (K : ℕ) :
    MeasurePreserving (continuousKMTRootNormal K)
      (continuousKMTMeasure K) (gaussianReal 0 1) := by
  have h :=
    dyadicRootEval_measurePreserving.comp
      ((dyadicRootRestrict_measurePreserving K).comp
        (continuousKMTTree_measurePreserving K))
  simpa [continuousKMTRootNormal, Function.comp_def] using h

@[fun_prop]
theorem measurable_continuousKMTRootNormal (K : ℕ) :
    Measurable (continuousKMTRootNormal K) :=
  (continuousKMTRootNormal_measurePreserving K).measurable

theorem continuousKMTRootNormal_map (K : ℕ) :
    (continuousKMTMeasure K).map (continuousKMTRootNormal K) =
      gaussianReal 0 1 :=
  (continuousKMTRootNormal_measurePreserving K).map_eq

/-- The endpoint error written with the natural dyadic horizon. -/
noncomputable def continuousKMTEndpointError
    (K : ℕ) (omega : ContinuousKMTSpace K) : ℝ :=
  (continuousKMTPoisson K ((2 ^ K : ℕ) : ℝ) omega : ℝ) -
    ((2 ^ K : ℕ) : ℝ) -
      continuousKMTBrownian K ((2 ^ K : ℕ) : ℝ) omega

/-- The path endpoint error is literally the level-zero bridge error. -/
theorem continuousKMTEndpointError_eq_rootBridge
    (K : ℕ) (omega : ContinuousKMTSpace K) :
    continuousKMTEndpointError K omega =
      bridgeError K 0 (dyadicRootRestrict K omega.1.1) () := by
  unfold continuousKMTEndpointError
  rw [continuousKMTPoisson_natCast K (2 ^ K) omega,
    continuousKMTBrownian_natCast K (2 ^ K)
      (by simp [dyadicHorizon]) omega,
    spatialPoissonSkeleton_horizon K omega.1.1,
    spatialGaussianSkeleton_horizon K omega.1.1]
  simp [poissonRootCount, gaussianRootEndpoint, bridgeError,
    poissonLevel, gaussianLevel, gaussianEndpoints, dyadicVariance]
  try rfl

/-- Pointwise Tusnády root bound at the continuous KMT endpoint. -/
theorem continuousKMTEndpointError_abs_le
    (K : ℕ) (omega : ContinuousKMTSpace K) :
    |continuousKMTEndpointError K omega| ≤
      1 + 2 * (continuousKMTRootNormal K omega) ^ 2 := by
  rw [continuousKMTEndpointError_eq_rootBridge]
  simpa [continuousKMTRootNormal] using
    (root_bridgeError_le K
      (dyadicRootRestrict K omega.1.1) ())

/-- A one-dimensional Gaussian-square tail in the exact form needed below. -/
private theorem continuousKMTRootNormal_square_tail
    (K : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (continuousKMTMeasure K).real
        {omega | x <
          2 * (continuousKMTRootNormal K omega) ^ 2} ≤
      2 * Real.exp (-(x / 4)) := by
  let threshold : ℝ := Real.sqrt (x / 2)
  have hhalf : 0 ≤ x / 2 := by positivity
  have hthreshold : 0 ≤ threshold := by
    dsimp [threshold]
    positivity
  have hsubset :
      {omega | x <
          2 * (continuousKMTRootNormal K omega) ^ 2} ⊆
        {omega | threshold <
          |continuousKMTRootNormal K omega|} := by
    intro omega hbad
    have hbad' : x < 2 * (continuousKMTRootNormal K omega) ^ 2 := hbad
    have hne : continuousKMTRootNormal K omega ≠ 0 := by
      intro hzero
      have hneg : x < 0 := by simpa [hzero] using hbad'
      linarith
    have habs : 0 < |continuousKMTRootNormal K omega| :=
      abs_pos.mpr hne
    dsimp [threshold]
    show Real.sqrt (x / 2) < |continuousKMTRootNormal K omega|
    rw [Real.sqrt_lt' habs, sq_abs]
    linarith
  have htail := gaussian_abs_tail_le
    (P := continuousKMTMeasure K)
    (X := continuousKMTRootNormal K)
    (variance := (1 : ℝ≥0))
    (x := threshold)
    (measurable_continuousKMTRootNormal K)
    (continuousKMTRootNormal_map K)
    (by norm_num)
    hthreshold
  calc
    (continuousKMTMeasure K).real
        {omega | x <
          2 * (continuousKMTRootNormal K omega) ^ 2} ≤
      (continuousKMTMeasure K).real
        {omega | threshold <
          |continuousKMTRootNormal K omega|} :=
      measureReal_mono hsubset
    _ ≤ 2 * Real.exp (-(x / 4)) := by
      change
        ((continuousKMTMeasure K)
          {omega | threshold <
            |continuousKMTRootNormal K omega|}).toReal ≤ _
      calc
        ((continuousKMTMeasure K)
            {omega | threshold <
              |continuousKMTRootNormal K omega|}).toReal ≤
          (ENNReal.ofReal
            (2 * Real.exp
              (-(threshold ^ 2) /
                (2 * ((1 : ℝ≥0) : ℝ))))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top htail
        _ = 2 * Real.exp (-(x / 4)) := by
          rw [ENNReal.toReal_ofReal (by positivity)]
          dsimp [threshold]
          rw [Real.sq_sqrt hhalf]
          congr 1
          ring

/-- Uniform endpoint tail in terms of the named error. -/
theorem continuousKMTEndpointError_tail
    (K : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (continuousKMTMeasure K).real
        {omega | continuousEndpointShift + x <
          |continuousKMTEndpointError K omega|} ≤
      continuousEndpointPrefactor *
        Real.exp (-(continuousEndpointRate * x)) := by
  have hsubset :
      {omega | continuousEndpointShift + x <
          |continuousKMTEndpointError K omega|} ⊆
        {omega | x <
          2 * (continuousKMTRootNormal K omega) ^ 2} := by
    intro omega hbad
    have hroot := continuousKMTEndpointError_abs_le K omega
    have hbad' : continuousEndpointShift + x <
        |continuousKMTEndpointError K omega| := hbad
    unfold continuousEndpointShift at hbad'
    have hstrict := hbad'.trans_le hroot
    show x < 2 * (continuousKMTRootNormal K omega) ^ 2
    linarith
  calc
    (continuousKMTMeasure K).real
        {omega | continuousEndpointShift + x <
          |continuousKMTEndpointError K omega|} ≤
      (continuousKMTMeasure K).real
        {omega | x <
          2 * (continuousKMTRootNormal K omega) ^ 2} :=
      measureReal_mono hsubset
    _ ≤ 2 * Real.exp (-(x / 4)) :=
      continuousKMTRootNormal_square_tail K hx
    _ = continuousEndpointPrefactor *
        Real.exp (-(continuousEndpointRate * x)) := by
      unfold continuousEndpointPrefactor continuousEndpointRate
      congr 1
      ring

/-- Requested endpoint theorem, stated directly with `Y` and `W`. -/
theorem continuousKMTHorizonEndpoint_tail
    (K : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (continuousKMTMeasure K).real
        {omega | continuousEndpointShift + x <
          |(continuousKMTPoisson K ((2 ^ K : ℕ) : ℝ) omega : ℝ) -
            ((2 ^ K : ℕ) : ℝ) -
              continuousKMTBrownian K
                ((2 ^ K : ℕ) : ℝ) omega|} ≤
      continuousEndpointPrefactor *
        Real.exp (-(continuousEndpointRate * x)) := by
  simpa [continuousKMTEndpointError] using
    (continuousKMTEndpointError_tail K hx)

/-!
THEOREM LIST
* `continuousKMTRootNormal_measurePreserving`
* `measurable_continuousKMTRootNormal`
* `continuousKMTRootNormal_map`
* `continuousKMTEndpointError_eq_rootBridge`
* `continuousKMTEndpointError_abs_le`
* `continuousKMTEndpointError_tail`
* `continuousKMTHorizonEndpoint_tail`

UNFINISHED
* No mathematical part of item 2 is intentionally omitted.
END
-/

end Ripple.Kurtz.StrongApprox.ContinuousEndpointTail

end
