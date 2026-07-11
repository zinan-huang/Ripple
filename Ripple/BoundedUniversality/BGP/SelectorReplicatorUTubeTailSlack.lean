import Ripple.BoundedUniversality.BGP.SelectorReplicatorSettledResidual

/-!
# Settled-tail u-tube slack adapter

The settled u-drift estimate is additive.  It preserves the exact `r_LE_U`
tail tube only when the write-hold endpoint has enough slack to absorb that
drift.  This file records the non-circular adapter explicitly.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance UniversalMachine
open scoped BigOperators Topology Real

/-- Tail tube from endpoint slack and the settled u-drift estimate. -/
theorem selectorMU_hutube_tail_of_hold_slack
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (cfg : ℕ → UConf) (j : ℕ)
    (Bzu : ℝ) (hBzu0 : 0 ≤ Bzu)
    (hdom : ∀ t : ℝ, 0 ≤ t → t ∈ selectorSchedule.domain)
    (hzu : ∀ i, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
      |sol.z t i - sol.u t i| ≤ Bzu)
    (hhold_slack : ∀ i,
      |sol.u (selectorMUWriteHoldTime j) i -
          stackMachineEncodingU.enc (cfg j) i| +
        δuSettled Bzu j ≤ r_LE_U) :
    ∀ t ∈ Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j),
      UTube r_LE_U (cfg j) (sol.u t) := by
  intro t ht i
  have hdrift :=
    u_drift_on_settled_window sol j i hBzu0 hdom (hzu i) t ht
  have htri :
      |sol.u t i - stackMachineEncodingU.enc (cfg j) i| ≤
        |sol.u t i - sol.u (selectorMUWriteHoldTime j) i| +
          |sol.u (selectorMUWriteHoldTime j) i -
            stackMachineEncodingU.enc (cfg j) i| := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      abs_add_le
        (sol.u t i - sol.u (selectorMUWriteHoldTime j) i)
        (sol.u (selectorMUWriteHoldTime j) i -
          stackMachineEncodingU.enc (cfg j) i)
  calc
    |sol.u t i - stackMachineEncodingU.enc (cfg j) i|
        ≤ |sol.u t i - sol.u (selectorMUWriteHoldTime j) i| +
          |sol.u (selectorMUWriteHoldTime j) i -
            stackMachineEncodingU.enc (cfg j) i| := htri
    _ ≤ δuSettled Bzu j +
          |sol.u (selectorMUWriteHoldTime j) i -
            stackMachineEncodingU.enc (cfg j) i| := by
      exact add_le_add hdrift le_rfl
    _ = |sol.u (selectorMUWriteHoldTime j) i -
            stackMachineEncodingU.enc (cfg j) i| +
          δuSettled Bzu j := by ring
    _ ≤ r_LE_U := hhold_slack i

/-- Residual package for converting settled-tail endpoint slack into the exact
tail `UTube` field required by `SelectorMUWriteFullUTubeResidual`. -/
structure SelectorMUWriteTailSlackResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  Bzu : ℕ → ℕ → ℝ
  hBzu0 : ∀ w j, 0 ≤ Bzu w j
  hzu_tail : ∀ w j i, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j),
    |(sol w).z t i - (sol w).u t i| ≤ Bzu w j
  hhold_slack : ∀ w j i,
    |(sol w).u (selectorMUWriteHoldTime j) i -
        stackMachineEncodingU.enc (solMUReplStaticCfg w j) i| +
      δuSettled (Bzu w j) j ≤ r_LE_U

namespace SelectorMUWriteTailSlackResidual

/-- Project a tail-slack residual to the exact settled-tail `UTube`. -/
theorem hutube_tail
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (R : SelectorMUWriteTailSlackResidual sol) :
    ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t) := by
  intro w j
  exact selectorMU_hutube_tail_of_hold_slack (sol w)
    (fun j => solMUReplStaticCfg w j) j
    (R.Bzu w j) (R.hBzu0 w j)
    (fun t ht => selectorSchedule_domain_of_nonneg_structural t ht)
    (R.hzu_tail w j) (R.hhold_slack w j)

end SelectorMUWriteTailSlackResidual

/-- Full write-window `UTube` residual produced from a prefix tube and an
explicit tail-slack residual. -/
structure SelectorMUWriteFullUTubeSlackResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  prefixTube : SelectorMUWritePrefixUTubeResidual sol
  tailSlack : SelectorMUWriteTailSlackResidual sol

namespace SelectorMUWriteFullUTubeSlackResidual

/-- Forget the slack-shaped full write-window residual to the legacy exact
full-window `UTube` surface. -/
def toFullUTubeResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (R : SelectorMUWriteFullUTubeSlackResidual sol) :
    SelectorMUWriteFullUTubeResidual sol where
  prefixTube := R.prefixTube
  hutube_tail := R.tailSlack.hutube_tail

end SelectorMUWriteFullUTubeSlackResidual

end Ripple.BoundedUniversality.BGP
