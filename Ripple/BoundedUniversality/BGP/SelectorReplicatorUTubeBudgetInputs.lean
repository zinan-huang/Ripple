import Ripple.BoundedUniversality.BGP.SelectorReplicatorUTubeBudget

/-!
# Coarse u-tube budget input package

This file names the analytic inputs consumed by
`selectorMUCoarseUTubeBudget_of_current_depth_prefix`.  The constructor in
`SelectorReplicatorUTubeBudget` discharges structural depth and radius
bookkeeping; this package keeps the remaining recurrence, hold, and cap
obligations explicit.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance Filter
open scoped BigOperators Topology

/-- Analytic input package for the prefix coarse `u`-tube budget. -/
structure SelectorMUCoarseUTubeBudgetInputs
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀)
    (cfg : ℕ → UConf) (w : ℕ) where
  η : ℕ → Fin d_U → ℝ
  W0 : Fin d_U → ℝ
  εhold : ℝ
  hη_nonneg : ∀ j i, 0 ≤ η j i
  hη_tendsto_zero : ∀ i, Tendsto (fun j => η j i) atTop (𝓝 0)
  hinit :
    MUWeighted_repl (sol w) (fun j => stackMachineEncodingU.enc (cfg j))
      (B_U : ℝ) (MachineInstance.depthU cfg)
      (selectorMUWboundPrefix W0 (MachineInstance.depthU cfg) η) 0
  hrecur :
    ∀ j,
      MUWeighted_repl (sol w) (fun j => stackMachineEncodingU.enc (cfg j))
        (B_U : ℝ) (MachineInstance.depthU cfg)
        (selectorMUWboundPrefix W0 (MachineInstance.depthU cfg) η) j →
      MURecur_repl (sol w) (fun j => stackMachineEncodingU.enc (cfg j))
        (B_U : ℝ) (selectorMUCoarseDelta cfg) η j
  hhold :
    ∀ j i, ∀ t ∈ Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
      |(sol w).u t i - (sol w).u (selectorMUWriteStartTime j) i| ≤ εhold
  hcap : ∀ j i,
    selectorMUWboundPrefix W0 (MachineInstance.depthU cfg) η j i ≤
      (r_LE_U - εhold) * (B_U : ℝ) ^ MachineInstance.depthU cfg j i

namespace SelectorMUCoarseUTubeBudgetInputs

/-- Project the explicit analytic input package to the existing coarse budget
surface. -/
def toBudget
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    {cfg : ℕ → UConf} {w : ℕ}
    (R : SelectorMUCoarseUTubeBudgetInputs sol cfg w)
    (hcfg_step : ∀ j, M_U.step (cfg j) = cfg (j + 1)) :
    SelectorMUCoarseUTubeBudget sol cfg w :=
  selectorMUCoarseUTubeBudget_of_current_depth_prefix
    hcfg_step R.η R.W0 R.εhold R.hη_nonneg R.hη_tendsto_zero
    R.hinit R.hrecur R.hhold R.hcap

end SelectorMUCoarseUTubeBudgetInputs

end Ripple.BoundedUniversality.BGP
