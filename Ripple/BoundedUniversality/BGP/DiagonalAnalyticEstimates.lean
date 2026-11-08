import Ripple.BoundedUniversality.BGP.SelectorMUCycleInvariant
import Ripple.BoundedUniversality.BGP.SelectorReplicatorSettledEstimates

/-!
Ripple.BoundedUniversality.BGP.DiagonalAnalyticEstimates
------------------------------------
Projection layer for the diagonal analytic data used by the shifted Ripple.BoundedUniversality
headline:

* `hoff`: carry only the diagonal pointwise self-hold estimate consumed by the
  headline;
* `hnextWrite`: project the existing next-write start+mix residual to the exact
  `δnext`/window estimate expected by the headline;
* `hutube_win`: carry the direct diagonal write-window `UTube` premise.

The namespace still provides `ofEstimates` so older full residual surfaces can
be projected into this narrower record when needed.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance Filter
open scoped Topology

namespace SelectorMUHoffFieldIntegralEstimate

/-- The settled `hoff` field-integral residual is definitionally the same
estimate as the cycle-local residual, with the family-indexed halt-constant
predicate unfolded. -/
def toCycleHoffFieldIntegralEstimate
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : SelectorMUHoffFieldIntegralEstimate sol) :
    SelectorMUCycleHoffFieldIntegralEstimate sol where
  hfieldInt := by
    intro w j henc_const t ht
    simpa [selectorMUHaltEncConstW] using res.hfieldInt w j henc_const t ht

end SelectorMUHoffFieldIntegralEstimate

namespace SelectorMUHoffSplitMiddleEnvelopeEstimate

/-- Phase-split settled `hoff` caps discharge the cycle-local `hoff` residual. -/
def toCycleHoffFieldIntegralEstimate
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : SelectorMUHoffSplitMiddleEnvelopeEstimate sol)
    (boxInputs : MUReplicatorBoxHypotheses eta heta Mcy κ₀ g₀ sol) :
    SelectorMUCycleHoffFieldIntegralEstimate sol :=
  (res.toFieldIntegralEstimate boxInputs).toCycleHoffFieldIntegralEstimate

end SelectorMUHoffSplitMiddleEnvelopeEstimate

namespace SelectorMUHoffSplitMiddleEnvelopeNoSplitEstimate

/-- No-split settled `hoff` caps discharge the cycle-local `hoff` residual. -/
def toCycleHoffFieldIntegralEstimate
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : SelectorMUHoffSplitMiddleEnvelopeNoSplitEstimate sol)
    (boxInputs : MUReplicatorBoxHypotheses eta heta Mcy κ₀ g₀ sol) :
    SelectorMUCycleHoffFieldIntegralEstimate sol :=
  (res.toFieldIntegralEstimate boxInputs).toCycleHoffFieldIntegralEstimate

end SelectorMUHoffSplitMiddleEnvelopeNoSplitEstimate

namespace SelectorMUHoffSplitMiddleEnvelopeFieldCapNoSplitEstimate

/-- Field-cap settled `hoff` residuals discharge the cycle-local `hoff`
residual. -/
def toCycleHoffFieldIntegralEstimate
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : SelectorMUHoffSplitMiddleEnvelopeFieldCapNoSplitEstimate sol)
    (boxInputs : MUReplicatorBoxHypotheses eta heta Mcy κ₀ g₀ sol) :
    SelectorMUCycleHoffFieldIntegralEstimate sol :=
  res.toNoSplitEstimate.toCycleHoffFieldIntegralEstimate boxInputs

end SelectorMUHoffSplitMiddleEnvelopeFieldCapNoSplitEstimate

namespace SelectorMUWriteFullUTubeEstimate

/-- Projection to the headline's direct write-window `UTube` premise. -/
theorem diag_hutube_win
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : SelectorMUWriteFullUTubeEstimate sol) :
    ∀ w j, ∀ t ∈ Ico (selectorMUWriteStartTime j) (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t) :=
  res.hutube_win

end SelectorMUWriteFullUTubeEstimate

namespace MUReplicatorNextWriteStartMixEstimate

/-- The `δnext` sequence used by the headline is exactly the sum of the
next-start and moving-mix radii in the settled residual. -/
def headlineδnext
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartMixEstimate sol) : ℕ → ℕ → ℝ :=
  res.δnext

/-- Vanishing of the headline `δnext`. -/
theorem diag_hδnext
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartMixEstimate sol) :
    ∀ w, Tendsto ((res.headlineδnext) w) atTop (𝓝 0) :=
  res.hδnext

/-- Nonnegativity of the headline `δnext`. -/
theorem diag_hδnext_nonneg
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartMixEstimate sol) :
    ∀ w j, 0 ≤ (res.headlineδnext) w j :=
  res.hδnext_nonneg

/-- Projection to the headline's next-write window halt-coordinate estimate. -/
theorem diag_hnextWrite
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartMixEstimate sol) :
    ∀ w j, ∀ t ∈ Icc (selectorMUNextWriteStart j) (selectorMUNextRead j),
      |(sol w).z t haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
          (res.headlineδnext) w j :=
  res.p_hnextWrite

end MUReplicatorNextWriteStartMixEstimate

/-- A compact package matching exactly the diagonal analytic arguments consumed
by the shifted headline theorem.

The warm-gain family is indexed by `wg`, and the headline only ever queries the
solution word `w = wg`.  The package therefore carries diagonal projections
instead of full `∀ w` settled residuals. -/
structure DiagonalAnalyticEstimates
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ : ℚ} (g₀ : ℕ → ℚ)
    (solByWarmGain : (wg : ℕ) → MUReplicatorSolFamily eta heta Mcy κ₀ (g₀ wg)) where
  hutube_win :
    ∀ wg j, ∀ t ∈ Ico (selectorMUWriteStartTime j) (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg wg j) (((solByWarmGain wg) wg).u t)
  p_hoff :
    ∀ wg j, selectorMUHaltEncConst (solMUReplStaticCfg wg) j → ∀ t ∈
      Icc (selectorMUInterReadStart j) (selectorMUNextWriteStart j),
        |((solByWarmGain wg) wg).z t haltCoordU -
          ((solByWarmGain wg) wg).z (selectorMUInterReadStart j) haltCoordU| ≤
            selectorReplicatorHoldEnvelope j
  δnext : ℕ → ℕ → ℝ
  hδnext : ∀ wg, Tendsto (δnext wg) atTop (𝓝 0)
  hδnext_nonneg : ∀ wg j, 0 ≤ δnext wg j
  hnextWrite :
    ∀ wg j, ∀ t ∈ Icc (selectorMUNextWriteStart j) (selectorMUNextRead j),
      |((solByWarmGain wg) wg).z t haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg wg (j + 2)) haltCoordU| ≤
          δnext wg j

namespace DiagonalAnalyticEstimates

/-- Compatibility constructor from the older full residual surfaces. -/
def ofEstimates
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ : ℚ} {g₀ : ℕ → ℚ}
    {solByWarmGain : (wg : ℕ) → MUReplicatorSolFamily eta heta Mcy κ₀ (g₀ wg)}
    (fullUTube : ∀ wg, SelectorMUWriteFullUTubeEstimate (solByWarmGain wg))
    (hoffIntegral : ∀ wg, SelectorMUHoffFieldIntegralEstimate (solByWarmGain wg))
    (nextWrite : ∀ wg, MUReplicatorNextWriteStartMixEstimate (solByWarmGain wg)) :
    DiagonalAnalyticEstimates g₀ solByWarmGain where
  hutube_win := by
    intro wg
    exact (fullUTube wg).diag_hutube_win wg
  p_hoff := by
    intro wg j henc t ht
    simpa [selectorMUHaltEncConstW] using
      (hoffIntegral wg).p_hoff wg j henc t ht
  δnext := fun wg => (nextWrite wg).headlineδnext wg
  hδnext := by
    intro wg
    exact (nextWrite wg).diag_hδnext wg
  hδnext_nonneg := by
    intro wg j
    exact (nextWrite wg).diag_hδnext_nonneg wg j
  hnextWrite := by
    intro wg
    exact (nextWrite wg).diag_hnextWrite wg

end DiagonalAnalyticEstimates

/-- **Parameter-generic diagonal analytic discharge record** (the NW consumer-flip
carrier, Q4149 Step 1).  Identical fields to `DiagonalAnalyticEstimates`,
but the warm-gain family may vary its gate parameters with the family index
(`pByWarmGain : ℕ → DynGateParams`) — the word-coupled headline family
`bgpSolFamNW` uses `bgpParamsNW wg`, which the constant-parameter
legacy record cannot type.  Additive: the legacy record and its `ofEstimates`
compatibility constructor are untouched.  The NW instantiation and the direct
diagonal constructor live with the NW producers (they reference the headline
family, which is defined downstream of this file). -/
structure DiagonalAnalyticEstimatesP
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ : ℚ}
    (pByWarmGain : ℕ → DynGateParams)
    (g₀ : ℕ → ℚ)
    (solByWarmGain : (wg : ℕ) →
      MUReplicatorSolFamilyP (pByWarmGain wg) eta heta Mcy κ₀ (g₀ wg)) where
  hutube_win :
    ∀ wg j, ∀ t ∈ Ico (selectorMUWriteStartTime j) (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg wg j) (((solByWarmGain wg) wg).u t)
  p_hoff :
    ∀ wg j, selectorMUHaltEncConst (solMUReplStaticCfg wg) j → ∀ t ∈
      Icc (selectorMUInterReadStart j) (selectorMUNextWriteStart j),
        |((solByWarmGain wg) wg).z t haltCoordU -
          ((solByWarmGain wg) wg).z (selectorMUInterReadStart j) haltCoordU| ≤
            selectorReplicatorHoldEnvelope j
  δnext : ℕ → ℕ → ℝ
  hδnext : ∀ wg, Tendsto (δnext wg) atTop (𝓝 0)
  hδnext_nonneg : ∀ wg j, 0 ≤ δnext wg j
  hnextWrite :
    ∀ wg j, ∀ t ∈ Icc (selectorMUNextWriteStart j) (selectorMUNextRead j),
      |((solByWarmGain wg) wg).z t haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg wg (j + 2)) haltCoordU| ≤
          δnext wg j

section ArbitraryParamSentinel

/-- Arbitrary-parameter sentinel (Q4138 gate 4): the P record must be
constructible at a FRESH parameter family — if this only compiled because
something unified the parameters with a concrete instance, it would fail. -/
example
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ : ℚ}
    {pF : ℕ → DynGateParams} {g₀ : ℕ → ℚ}
    {solF : (wg : ℕ) →
      MUReplicatorSolFamilyP (pF wg) eta heta Mcy κ₀ (g₀ wg)}
    (R : DiagonalAnalyticEstimatesP pF g₀ solF) :
    ∀ wg j, 0 ≤ R.δnext wg j :=
  R.hδnext_nonneg

end ArbitraryParamSentinel

end Ripple.BoundedUniversality.BGP
