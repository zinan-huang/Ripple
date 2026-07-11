import Ripple.BoundedUniversality.BGP.SelectorReplicatorUTubeBudgetInputs
import Ripple.BoundedUniversality.BGP.SelectorReplicatorUTubeTailSlack

/-!
# Coupled prefix/tail u-tube budget inputs

The settled-tail `u` drift is additive, so the prefix budget must reserve the
tail drift at the write-hold endpoint.  This file records that coupling as a
single residual input surface and projects it back to the existing split
`SelectorMUWriteFullUTubeSlackResidual` interface.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance Filter
open scoped BigOperators Topology

/-- Prefix coarse budget inputs strengthened with the exact settled-tail reserve
needed by `SelectorMUWriteTailSlackResidual`. -/
structure SelectorMUCoarseUTubeBudgetSettledTailInputs
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
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
  Bzu : ℕ → ℝ
  hBzu0 : ∀ j, 0 ≤ Bzu j
  hzu_tail : ∀ j i, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j),
    |(sol w).z t i - (sol w).u t i| ≤ Bzu j
  hcap_tail : ∀ j i,
    selectorMUWboundPrefix W0 (MachineInstance.depthU cfg) η j i ≤
      (r_LE_U - εhold - δuSettled (Bzu j) j) *
        (B_U : ℝ) ^ MachineInstance.depthU cfg j i

/-- Cap algebra for the coupled prefix/tail reserve.

This bridges the prefix-sum budget theorem to the stronger cap that reserves
the settled-tail `u` drift.  The analytic content remains exactly the
summability of weighted defects and the scalar total-reserve inequality. -/
theorem selectorMUWboundPrefix_coupled_tail_cap_of_tsum_cap
    (W0 : Fin d_U → ℝ) (dep : ℕ → Fin d_U → ℤ)
    (η : ℕ → Fin d_U → ℝ) (εhold : ℝ) (Bzu : ℕ → ℝ)
    (hTnonneg : ∀ m i, 0 ≤ weightedDefect (B_U : ℝ) dep η m i)
    (hTsum : ∀ i, Summable (fun m => weightedDefect (B_U : ℝ) dep η m i))
    (hcap_tsum : ∀ j i,
      W0 i + (∑' m, weightedDefect (B_U : ℝ) dep η m i) ≤
        (r_LE_U - εhold - δuSettled (Bzu j) j) *
          (B_U : ℝ) ^ dep j i) :
    ∀ j i,
      selectorMUWboundPrefix W0 dep η j i ≤
        (r_LE_U - εhold - δuSettled (Bzu j) j) *
          (B_U : ℝ) ^ dep j i := by
  intro j i
  have hprefix_raw :=
    WboundPrefix_le_cap W0 (B_U : ℝ) dep η i
      (fun m => hTnonneg m i) (hTsum i) j
  have hprefix :
      selectorMUWboundPrefix W0 dep η j i ≤
        W0 i + (∑' m, weightedDefect (B_U : ℝ) dep η m i) := by
    simpa [selectorMUWboundPrefix] using hprefix_raw
  exact hprefix.trans (hcap_tsum j i)

/-- Normalized version of
`selectorMUWboundPrefix_coupled_tail_cap_of_tsum_cap`. -/
theorem selectorMUWboundPrefix_coupled_tail_cap_of_tsum_normalized
    (W0 : Fin d_U → ℝ) (dep : ℕ → Fin d_U → ℤ)
    (η : ℕ → Fin d_U → ℝ) (εhold : ℝ) (Bzu : ℕ → ℝ)
    (hTnonneg : ∀ m i, 0 ≤ weightedDefect (B_U : ℝ) dep η m i)
    (hTsum : ∀ i, Summable (fun m => weightedDefect (B_U : ℝ) dep η m i))
    (hnorm_tsum : ∀ j i,
      (W0 i + (∑' m, weightedDefect (B_U : ℝ) dep η m i)) /
          (B_U : ℝ) ^ dep j i ≤
        r_LE_U - εhold - δuSettled (Bzu j) j) :
    ∀ j i,
      selectorMUWboundPrefix W0 dep η j i ≤
        (r_LE_U - εhold - δuSettled (Bzu j) j) *
          (B_U : ℝ) ^ dep j i := by
  refine selectorMUWboundPrefix_coupled_tail_cap_of_tsum_cap
    W0 dep η εhold Bzu hTnonneg hTsum ?_
  intro j i
  have hpow_pos : 0 < (B_U : ℝ) ^ dep j i :=
    zpow_pos (by norm_num [B_U] : (0 : ℝ) < (B_U : ℝ)) _
  exact (div_le_iff₀ hpow_pos).mp (hnorm_tsum j i)

/-- Coupled-tail cap from a geometric weighted-defect comparison. -/
theorem selectorMUWboundPrefix_coupled_tail_cap_of_geometric
    (W0 : Fin d_U → ℝ) (dep : ℕ → Fin d_U → ℤ)
    (η : ℕ → Fin d_U → ℝ) (εhold : ℝ) (Bzu : ℕ → ℝ)
    {C q : Fin d_U → ℝ}
    (hTnonneg : ∀ m i, 0 ≤ weightedDefect (B_U : ℝ) dep η m i)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hgeom : ∀ i j, ‖weightedDefect (B_U : ℝ) dep η j i‖ ≤ C i * (q i) ^ j)
    (hcap_tsum : ∀ j i,
      W0 i + (∑' m, weightedDefect (B_U : ℝ) dep η m i) ≤
        (r_LE_U - εhold - δuSettled (Bzu j) j) *
          (B_U : ℝ) ^ dep j i) :
    ∀ j i,
      selectorMUWboundPrefix W0 dep η j i ≤
        (r_LE_U - εhold - δuSettled (Bzu j) j) *
          (B_U : ℝ) ^ dep j i := by
  refine selectorMUWboundPrefix_coupled_tail_cap_of_tsum_cap
    W0 dep η εhold Bzu hTnonneg ?_ hcap_tsum
  intro i
  exact weightedDefect_summable_of_geometric (B_U : ℝ) dep η i
    (hq0 i) (hq1 i) (hgeom i)

namespace SelectorMUCoarseUTubeBudgetSettledTailInputs

/-- The coupled-tail cap implies the ordinary prefix cap needed by the prefix
u-tube budget. -/
theorem hcap_weak
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → UConf} {w : ℕ}
    (inp : SelectorMUCoarseUTubeBudgetSettledTailInputs sol cfg w) :
    ∀ j i,
      selectorMUWboundPrefix inp.W0 (MachineInstance.depthU cfg) inp.η j i ≤
        (r_LE_U - inp.εhold) *
          (B_U : ℝ) ^ MachineInstance.depthU cfg j i := by
  intro j i
  have htail_nonneg : 0 ≤ δuSettled (inp.Bzu j) j := by
    dsimp [δuSettled]
    exact mul_nonneg (inp.hBzu0 j)
      (mul_nonneg (by positivity) (Real.exp_pos _).le)
  have hpow_nonneg : 0 ≤ (B_U : ℝ) ^ MachineInstance.depthU cfg j i :=
    zpow_nonneg (by norm_num [B_U] : (0 : ℝ) ≤ (B_U : ℝ)) _
  exact le_trans (inp.hcap_tail j i) <| by
    apply mul_le_mul_of_nonneg_right _ hpow_nonneg
    linarith

/-- Forget the stronger coupled-tail package to the ordinary prefix-budget
input package. -/
def toSelectorMUCoarseUTubeBudgetInputs
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → UConf} {w : ℕ}
    (inp : SelectorMUCoarseUTubeBudgetSettledTailInputs sol cfg w) :
    SelectorMUCoarseUTubeBudgetInputs sol cfg w where
  η := inp.η
  W0 := inp.W0
  εhold := inp.εhold
  hη_nonneg := inp.hη_nonneg
  hη_tendsto_zero := inp.hη_tendsto_zero
  hinit := inp.hinit
  hrecur := inp.hrecur
  hhold := inp.hhold
  hcap := inp.hcap_weak

/-- The strengthened cap gives the write-hold endpoint slack required to absorb
the settled-tail drift. -/
theorem writeHold_slack
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → UConf} {w : ℕ}
    (inp : SelectorMUCoarseUTubeBudgetSettledTailInputs sol cfg w)
    (hcfg_step : ∀ j, M_U.step (cfg j) = cfg (j + 1)) :
    ∀ j i,
      |(sol w).u (selectorMUWriteHoldTime j) i - stackMachineEncodingU.enc (cfg j) i| +
        δuSettled (inp.Bzu j) j ≤ r_LE_U := by
  intro j i
  let dep := MachineInstance.depthU cfg
  let Wbound := selectorMUWboundPrefix inp.W0 dep inp.η
  have hweighted :
      (B_U : ℝ) ^ dep j i *
          |(sol w).u (selectorMUWriteStartTime j) i -
            stackMachineEncodingU.enc (cfg j) i| ≤
        Wbound j i := by
    have hweighted_all :
        ∀ j,
          MUWeighted_repl (sol w) (fun j : ℕ => stackMachineEncodingU.enc (cfg j))
            (B_U : ℝ) dep Wbound j := by
      exact
        MUWeighted_all_of_init_step_repl (sol w)
          (fun j : ℕ => stackMachineEncodingU.enc (cfg j))
          selectorMU_B_U_real_gt_one dep (selectorMUCoarseDelta cfg) inp.η Wbound
          (selectorMUCurrentDepthStep_concrete hcfg_step)
          (selectorMUWboundPrefix_step inp.W0 dep inp.η)
          (by simpa [dep, Wbound] using inp.hinit)
          (by
            intro j hw
            simpa [dep, Wbound] using inp.hrecur j (by simpa [dep, Wbound] using hw))
    simpa [MUWeighted_repl, muBoundaryError_repl, selectorMUWriteStartTime, dep, Wbound] using
      hweighted_all j i
  have hpow_pos : 0 < (B_U : ℝ) ^ dep j i :=
    zpow_pos (by norm_num [B_U] : (0 : ℝ) < (B_U : ℝ)) _
  have hstart :
      |(sol w).u (selectorMUWriteStartTime j) i -
          stackMachineEncodingU.enc (cfg j) i| ≤
        Wbound j i / (B_U : ℝ) ^ dep j i := by
    rw [le_div_iff₀ hpow_pos]
    simpa [dep, Wbound, mul_comm] using hweighted
  have hcapdiv :
      Wbound j i / (B_U : ℝ) ^ dep j i ≤
        r_LE_U - inp.εhold - δuSettled (inp.Bzu j) j := by
    rw [div_le_iff₀ hpow_pos]
    simpa [dep, Wbound, mul_comm, mul_left_comm, mul_assoc] using inp.hcap_tail j i
  have hhold := inp.hhold j i (selectorMUWriteHoldTime j)
    ⟨selectorMUWriteStart_le_hold j, le_rfl⟩
  have htri :
      |(sol w).u (selectorMUWriteHoldTime j) i -
          stackMachineEncodingU.enc (cfg j) i| ≤
        |(sol w).u (selectorMUWriteStartTime j) i -
          stackMachineEncodingU.enc (cfg j) i| + inp.εhold := by
    have heq :
        (sol w).u (selectorMUWriteHoldTime j) i -
            stackMachineEncodingU.enc (cfg j) i =
          ((sol w).u (selectorMUWriteStartTime j) i -
            stackMachineEncodingU.enc (cfg j) i) +
          ((sol w).u (selectorMUWriteHoldTime j) i -
            (sol w).u (selectorMUWriteStartTime j) i) := by
      ring
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add le_rfl hhold)
  linarith

end SelectorMUCoarseUTubeBudgetSettledTailInputs

/-- All word-indexed inputs needed to build the full write-window `u`-tube with
the prefix reserve and settled-tail slack coupled. -/
structure SelectorMUWriteFullUTubeCoupledTailInputs
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  wordInputs : ∀ w,
    SelectorMUCoarseUTubeBudgetSettledTailInputs sol
      (fun j : ℕ => solMUReplStaticCfg w j) w

namespace SelectorMUWriteFullUTubeCoupledTailInputs

/-- Project coupled prefix/tail inputs to the split full-window slack residual. -/
def toFullUTubeSlackResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (R : SelectorMUWriteFullUTubeCoupledTailInputs sol) :
    SelectorMUWriteFullUTubeSlackResidual sol where
  prefixTube := by
    refine { coarseUTube := ?_ }
    intro w
    exact (R.wordInputs w).toSelectorMUCoarseUTubeBudgetInputs.toBudget
      (solMUReplStaticCfg_step w)
  tailSlack := by
    refine
      { Bzu := fun w j => (R.wordInputs w).Bzu j
        hBzu0 := ?_
        hzu_tail := ?_
        hhold_slack := ?_ }
    · intro w j
      exact (R.wordInputs w).hBzu0 j
    · intro w j i t ht
      exact (R.wordInputs w).hzu_tail j i t ht
    · intro w j i
      exact (R.wordInputs w).writeHold_slack (solMUReplStaticCfg_step w) j i

end SelectorMUWriteFullUTubeCoupledTailInputs

end Ripple.BoundedUniversality.BGP
