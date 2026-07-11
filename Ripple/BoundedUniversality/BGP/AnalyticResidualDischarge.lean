import Ripple.BoundedUniversality.BGP.SelectorMUCycleInvariant
import Ripple.BoundedUniversality.BGP.SelectorReplicatorSettledResidual

/-!
Ripple.BoundedUniversality.BGP.AnalyticResidualDischarge
------------------------------------
Projection layer for the diagonal analytic data used by the shifted Ripple.BoundedUniversality
headline:

* `hoff`: carry only the diagonal pointwise self-hold estimate consumed by the
  headline;
* `hnextWrite`: project the existing next-write start+mix residual to the exact
  `δnext`/window estimate expected by the headline;
* `hutube_win`: carry the direct diagonal write-window `UTube` premise.

The namespace still provides `ofResiduals` so older full residual surfaces can
be projected into this narrower record when needed.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance Filter
open scoped Topology

namespace SelectorMUHoffFieldIntegralResidual

/-- The settled `hoff` field-integral residual is definitionally the same
estimate as the cycle-local residual, with the family-indexed halt-constant
predicate unfolded. -/
def toCycleHoffFieldIntegralResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : SelectorMUHoffFieldIntegralResidual sol) :
    SelectorMUCycleHoffFieldIntegralResidual sol where
  hfieldInt := by
    intro w j henc_const t ht
    simpa [selectorMUHaltEncConstW] using res.hfieldInt w j henc_const t ht

end SelectorMUHoffFieldIntegralResidual

namespace SelectorMUHoffSplitMiddleEnvelopeResidual

/-- Phase-split settled `hoff` caps discharge the cycle-local `hoff` residual. -/
def toCycleHoffFieldIntegralResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : SelectorMUHoffSplitMiddleEnvelopeResidual sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    SelectorMUCycleHoffFieldIntegralResidual sol :=
  (res.toFieldIntegralResidual boxInputs).toCycleHoffFieldIntegralResidual

end SelectorMUHoffSplitMiddleEnvelopeResidual

namespace SelectorMUHoffSplitMiddleEnvelopeNoSplitResidual

/-- No-split settled `hoff` caps discharge the cycle-local `hoff` residual. -/
def toCycleHoffFieldIntegralResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : SelectorMUHoffSplitMiddleEnvelopeNoSplitResidual sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    SelectorMUCycleHoffFieldIntegralResidual sol :=
  (res.toFieldIntegralResidual boxInputs).toCycleHoffFieldIntegralResidual

end SelectorMUHoffSplitMiddleEnvelopeNoSplitResidual

namespace SelectorMUHoffSplitMiddleEnvelopeFieldCapNoSplitResidual

/-- Field-cap settled `hoff` residuals discharge the cycle-local `hoff`
residual. -/
def toCycleHoffFieldIntegralResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : SelectorMUHoffSplitMiddleEnvelopeFieldCapNoSplitResidual sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    SelectorMUCycleHoffFieldIntegralResidual sol :=
  res.toNoSplitResidual.toCycleHoffFieldIntegralResidual boxInputs

end SelectorMUHoffSplitMiddleEnvelopeFieldCapNoSplitResidual

namespace SelectorMUWriteFullUTubeResidual

/-- Projection to the headline's direct write-window `UTube` premise. -/
theorem headline_hutube_win
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : SelectorMUWriteFullUTubeResidual sol) :
    ∀ w j, ∀ t ∈ Ico (selectorMUWriteStartTime j) (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t) :=
  res.hutube_win

end SelectorMUWriteFullUTubeResidual

namespace MUReplicatorNextWriteStartMixResidual

/-- The `δnext` sequence used by the headline is exactly the sum of the
next-start and moving-mix radii in the settled residual. -/
def headlineδnext
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartMixResidual sol) : ℕ → ℕ → ℝ :=
  res.δnext

/-- Vanishing of the headline `δnext`. -/
theorem headline_hδnext
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartMixResidual sol) :
    ∀ w, Tendsto ((res.headlineδnext) w) atTop (𝓝 0) :=
  res.hδnext

/-- Nonnegativity of the headline `δnext`. -/
theorem headline_hδnext_nonneg
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartMixResidual sol) :
    ∀ w j, 0 ≤ (res.headlineδnext) w j :=
  res.hδnext_nonneg

/-- Projection to the headline's next-write window halt-coordinate estimate. -/
theorem headline_hnextWrite
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartMixResidual sol) :
    ∀ w j, ∀ t ∈ Icc (selectorMUNextWriteStart j) (selectorMUNextRead j),
      |(sol w).z t haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
          (res.headlineδnext) w j :=
  res.p_hnextWrite

end MUReplicatorNextWriteStartMixResidual

/-- A compact package matching exactly the diagonal analytic arguments consumed
by the shifted headline theorem.

The warm-gain family is indexed by `wg`, and the headline only ever queries the
solution word `w = wg`.  The package therefore carries diagonal projections
instead of full `∀ w` settled residuals. -/
structure Paper3AnalyticResidualDischarge
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

namespace Paper3AnalyticResidualDischarge

/-- Compatibility constructor from the older full residual surfaces. -/
def ofResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ : ℚ} {g₀ : ℕ → ℚ}
    {solByWarmGain : (wg : ℕ) → MUReplicatorSolFamily eta heta Mcy κ₀ (g₀ wg)}
    (fullUTube : ∀ wg, SelectorMUWriteFullUTubeResidual (solByWarmGain wg))
    (hoffIntegral : ∀ wg, SelectorMUHoffFieldIntegralResidual (solByWarmGain wg))
    (nextWrite : ∀ wg, MUReplicatorNextWriteStartMixResidual (solByWarmGain wg)) :
    Paper3AnalyticResidualDischarge g₀ solByWarmGain where
  hutube_win := by
    intro wg
    exact (fullUTube wg).headline_hutube_win wg
  p_hoff := by
    intro wg j henc t ht
    simpa [selectorMUHaltEncConstW] using
      (hoffIntegral wg).p_hoff wg j henc t ht
  δnext := fun wg => (nextWrite wg).headlineδnext wg
  hδnext := by
    intro wg
    exact (nextWrite wg).headline_hδnext wg
  hδnext_nonneg := by
    intro wg j
    exact (nextWrite wg).headline_hδnext_nonneg wg j
  hnextWrite := by
    intro wg
    exact (nextWrite wg).headline_hnextWrite wg

end Paper3AnalyticResidualDischarge

/-- **Parameter-generic diagonal analytic discharge record** (the NW consumer-flip
carrier, Q4149 Step 1).  Identical fields to `Paper3AnalyticResidualDischarge`,
but the warm-gain family may vary its gate parameters with the family index
(`pByWarmGain : ℕ → DynGateParams`) — the word-coupled headline family
`paper3HeadlineSolFamNW` uses `bgpParamsNW wg`, which the constant-parameter
legacy record cannot type.  Additive: the legacy record and its `ofResiduals`
compatibility constructor are untouched.  The NW instantiation and the direct
diagonal constructor live with the NW producers (they reference the headline
family, which is defined downstream of this file). -/
structure Paper3AnalyticResidualDischargeP
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
    (R : Paper3AnalyticResidualDischargeP pF g₀ solF) :
    ∀ wg j, 0 ≤ R.δnext wg j :=
  R.hδnext_nonneg

end ArbitraryParamSentinel

end Ripple.BoundedUniversality.BGP
