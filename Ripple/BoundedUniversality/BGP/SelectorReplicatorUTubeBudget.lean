import Ripple.BoundedUniversality.BGP.SelectorReplicatorUTubeMU
import Ripple.BoundedUniversality.BGP.SelectorBudget
import Ripple.BoundedUniversality.BGP.SelectorStackDepthSemantics

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorUTubeBudget
-----------------------------------------
Non-circular budget bridges for the P4 coarse `u`-tube.

This file deliberately does not manufacture the final `solMURepl` budget.  It
records the pieces that are dischargeable from the existing infrastructure:

* current structural depth obeys the `coordDelta` recurrence, using the proved
  concrete stack-depth semantics bridge;
* the prefix `Wbound` has the required one-step budget monotonicity;
* any scaled cap on that prefix budget gives the radius inequality consumed by
  `SelectorMUCoarseUTubeBudget`.

The remaining missing producer is the analytic recurrence/summability package:
`hrecur`, together with a concrete super-exponential `η` and the cap proving
`Wbound / B_U^dep + εhold <= r_LE_U` for all cycles.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open MachineInstance
open Filter Set
open Turing.PartrecToTM2
open scoped BigOperators
open scoped Topology

/-- Actual list depth is nonnegative on every universal-machine coordinate. -/
theorem selectorMU_depthU_nonneg (cfg : ℕ → UConf) :
    ∀ (j : ℕ) (i : Fin d_U), 0 ≤ MachineInstance.depthU cfg j i := by
  intro j i
  fin_cases i <;>
    simp [MachineInstance.depthU, MachineInstance.depthCoordU,
      MachineInstance.coordStackIndexU, MachineInstance.coordStackKindU,
      MachineInstance.mainStackCoordU, MachineInstance.revStackCoordU,
      MachineInstance.auxStackCoordU, MachineInstance.dataStackCoordU]

/--
The concrete current-depth schema satisfies the coarse depth recurrence,
provided the public stack-depth step semantics has been proved for `M_U.step`.
-/
theorem selectorMUCurrentDepthStep_of_stack_semantics
    (hsem : SelectorStackDepthStepSemanticsU)
    {cfg : ℕ → UConf} (hcfg_step : ∀ j, M_U.step (cfg j) = cfg (j + 1)) :
    SelectorMUCurrentDepthStep cfg := by
  intro j i
  fin_cases i
  · have h := hsem (cfg j) (MachineInstance.stackIndexU K'.main)
    rw [hcfg_step j] at h
    simpa [SelectorMUCurrentDepthStep, selectorMUCoarseDelta,
      MachineInstance.depthU, MachineInstance.depthCoordU,
      MachineInstance.stackMachineEncodingU, MachineInstance.indexedStackU,
      MachineInstance.stackCoordFinU, MachineInstance.stackKindOfIndexU,
      MachineInstance.stackCoordU, MachineInstance.mainStackCoordU,
      MachineInstance.coordStackIndexU, MachineInstance.coordStackKindU,
      StackMachineEncoding.coordDelta, StackMachineEncoding.stackDelta] using h
  · have h := hsem (cfg j) (MachineInstance.stackIndexU K'.rev)
    rw [hcfg_step j] at h
    simpa [SelectorMUCurrentDepthStep, selectorMUCoarseDelta,
      MachineInstance.depthU, MachineInstance.depthCoordU,
      MachineInstance.stackMachineEncodingU, MachineInstance.indexedStackU,
      MachineInstance.stackCoordFinU, MachineInstance.stackKindOfIndexU,
      MachineInstance.stackCoordU, MachineInstance.revStackCoordU,
      MachineInstance.coordStackIndexU, MachineInstance.coordStackKindU,
      StackMachineEncoding.coordDelta, StackMachineEncoding.stackDelta] using h
  · have h := hsem (cfg j) (MachineInstance.stackIndexU K'.aux)
    rw [hcfg_step j] at h
    simpa [SelectorMUCurrentDepthStep, selectorMUCoarseDelta,
      MachineInstance.depthU, MachineInstance.depthCoordU,
      MachineInstance.stackMachineEncodingU, MachineInstance.indexedStackU,
      MachineInstance.stackCoordFinU, MachineInstance.stackKindOfIndexU,
      MachineInstance.stackCoordU, MachineInstance.auxStackCoordU,
      MachineInstance.coordStackIndexU, MachineInstance.coordStackKindU,
      StackMachineEncoding.coordDelta, StackMachineEncoding.stackDelta] using h
  · have h := hsem (cfg j) (MachineInstance.stackIndexU K'.stack)
    rw [hcfg_step j] at h
    simpa [SelectorMUCurrentDepthStep, selectorMUCoarseDelta,
      MachineInstance.depthU, MachineInstance.depthCoordU,
      MachineInstance.stackMachineEncodingU, MachineInstance.indexedStackU,
      MachineInstance.stackCoordFinU, MachineInstance.stackKindOfIndexU,
      MachineInstance.stackCoordU, MachineInstance.dataStackCoordU,
      MachineInstance.coordStackIndexU, MachineInstance.coordStackKindU,
      StackMachineEncoding.coordDelta, StackMachineEncoding.stackDelta] using h
  · change MachineInstance.depthU cfg (j + 1) MachineInstance.ctrlCoordU =
      MachineInstance.depthU cfg j MachineInstance.ctrlCoordU -
        selectorMUCoarseDelta cfg j MachineInstance.ctrlCoordU
    have hidx :
        MachineInstance.stackMachineEncodingU.coordStackIndex
          MachineInstance.ctrlCoordU = none := by
      simp [MachineInstance.stackMachineEncodingU]
    rw [MachineInstance.depthU_reset cfg (j + 1) MachineInstance.ctrlCoordU hidx,
      MachineInstance.depthU_reset cfg j MachineInstance.ctrlCoordU hidx]
    simp [selectorMUCoarseDelta, StackMachineEncoding.coordDelta, hidx]
  · change MachineInstance.depthU cfg (j + 1) MachineInstance.haltCoordU =
      MachineInstance.depthU cfg j MachineInstance.haltCoordU -
        selectorMUCoarseDelta cfg j MachineInstance.haltCoordU
    have hidx :
        MachineInstance.stackMachineEncodingU.coordStackIndex
          MachineInstance.haltCoordU = none := by
      simp [MachineInstance.stackMachineEncodingU]
    rw [MachineInstance.depthU_reset cfg (j + 1) MachineInstance.haltCoordU hidx,
      MachineInstance.depthU_reset cfg j MachineInstance.haltCoordU hidx]
    simp [selectorMUCoarseDelta, StackMachineEncoding.coordDelta, hidx]

/-- Concrete current-depth recurrence for any orbit advancing by `M_U.step`. -/
theorem selectorMUCurrentDepthStep_concrete
    {cfg : ℕ → UConf} (hcfg_step : ∀ j, M_U.step (cfg j) = cfg (j + 1)) :
    SelectorMUCurrentDepthStep cfg :=
  selectorMUCurrentDepthStep_of_stack_semantics
    selectorStackDepthStepSemanticsU_proved hcfg_step

/-- Prefix-budget specialization at the universal base. -/
def selectorMUWboundPrefix
    (W0 : Fin d_U → ℝ) (dep : ℕ → Fin d_U → ℤ)
    (η : ℕ → Fin d_U → ℝ) : ℕ → Fin d_U → ℝ :=
  WboundPrefix W0 (B_U : ℝ) dep η

/-- The prefix budget discharges the carried `hWstep` field. -/
theorem selectorMUWboundPrefix_step
    (W0 : Fin d_U → ℝ) (dep : ℕ → Fin d_U → ℤ)
    (η : ℕ → Fin d_U → ℝ) :
    ∀ j i,
      selectorMUWboundPrefix W0 dep η j i +
          (B_U : ℝ) ^ dep (j + 1) i * η j i ≤
        selectorMUWboundPrefix W0 dep η (j + 1) i := by
  simpa [selectorMUWboundPrefix] using
    (WboundPrefix_step W0 (B_U : ℝ) dep η)

/--
A scaled cap on the prefix budget is exactly the radius inequality needed by
`SelectorMUCoarseUTubeBudget`.
-/
theorem selectorMU_hradius_of_scaled_cap
    (W0 : Fin d_U → ℝ) (dep : ℕ → Fin d_U → ℤ)
    (η : ℕ → Fin d_U → ℝ) (εhold : ℝ)
    (hcap : ∀ j i,
      selectorMUWboundPrefix W0 dep η j i ≤
        (r_LE_U - εhold) * (B_U : ℝ) ^ dep j i) :
    ∀ j i,
      selectorMUWboundPrefix W0 dep η j i / (B_U : ℝ) ^ dep j i + εhold ≤
        r_LE_U := by
  intro j i
  have hpow_pos : 0 < (B_U : ℝ) ^ dep j i :=
    zpow_pos (by norm_num [B_U] : (0 : ℝ) < (B_U : ℝ)) _
  have hdiv :
      selectorMUWboundPrefix W0 dep η j i / (B_U : ℝ) ^ dep j i ≤
        r_LE_U - εhold := by
    rw [div_le_iff₀ hpow_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcap j i
  linarith

/--
Build the concrete P4 coarse u-tube budget from actual list depths and the
prefix reserve.

This discharges the structural fields of `SelectorMUCoarseUTubeBudget`
(`dep`, `hdep_step`, `hdep_nonneg`, `Wbound`, `hWstep`, and `hradius`).  The
remaining inputs are exactly the analytic weighted recurrence, the super-decay
defect family, the hold bound, and the scaled cap.
-/
def selectorMUCoarseUTubeBudget_of_current_depth_prefix
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {M : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta M κ₀ g₀}
    {cfg : ℕ → UConf} {w : ℕ}
    (hcfg_step : ∀ j, M_U.step (cfg j) = cfg (j + 1))
    (η : ℕ → Fin d_U → ℝ) (W0 : Fin d_U → ℝ) (εhold : ℝ)
    (hη_nonneg : ∀ (j : ℕ) (i : Fin d_U), 0 ≤ η j i)
    (hη_tendsto_zero : ∀ i, Tendsto (fun j : ℕ => η j i) atTop (𝓝 0))
    (hinit :
      MUWeighted_repl (sol w) (fun j : ℕ => stackMachineEncodingU.enc (cfg j))
        (B_U : ℝ) (MachineInstance.depthU cfg)
        (selectorMUWboundPrefix W0 (MachineInstance.depthU cfg) η) 0)
    (hrecur :
      ∀ (j : ℕ),
        MUWeighted_repl (sol w) (fun j : ℕ => stackMachineEncodingU.enc (cfg j))
          (B_U : ℝ) (MachineInstance.depthU cfg)
          (selectorMUWboundPrefix W0 (MachineInstance.depthU cfg) η) j →
          MURecur_repl (sol w) (fun j : ℕ => stackMachineEncodingU.enc (cfg j))
            (B_U : ℝ) (selectorMUCoarseDelta cfg) η j)
    (hhold :
      ∀ (j : ℕ) (i : Fin d_U),
        ∀ t ∈ Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
        |(sol w).u t i - (sol w).u (selectorMUWriteStartTime j) i| ≤ εhold)
    (hcap : ∀ j i,
      selectorMUWboundPrefix W0 (MachineInstance.depthU cfg) η j i ≤
        (r_LE_U - εhold) * (B_U : ℝ) ^ MachineInstance.depthU cfg j i) :
    SelectorMUCoarseUTubeBudget sol cfg w where
  dep := MachineInstance.depthU cfg
  η := η
  Wbound := selectorMUWboundPrefix W0 (MachineInstance.depthU cfg) η
  εhold := εhold
  hdep_step := selectorMUCurrentDepthStep_concrete hcfg_step
  hdep_nonneg := selectorMU_depthU_nonneg cfg
  hη_nonneg := hη_nonneg
  hη_tendsto_zero := hη_tendsto_zero
  hinit := hinit
  hrecur := hrecur
  hWstep := selectorMUWboundPrefix_step W0 (MachineInstance.depthU cfg) η
  hhold := hhold
  hradius := selectorMU_hradius_of_scaled_cap W0 (MachineInstance.depthU cfg) η εhold hcap

#print axioms selectorMU_depthU_nonneg
#print axioms selectorMUCurrentDepthStep_of_stack_semantics
#print axioms selectorMUCurrentDepthStep_concrete
#print axioms selectorMUWboundPrefix
#print axioms selectorMUWboundPrefix_step
#print axioms selectorMU_hradius_of_scaled_cap
#print axioms selectorMUCoarseUTubeBudget_of_current_depth_prefix

end Ripple.BoundedUniversality.BGP
