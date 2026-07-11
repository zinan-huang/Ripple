import Ripple.BoundedUniversality.BGP.SelectorReplicatorUTube
import Ripple.BoundedUniversality.BGP.SelectorReplicatorSettledFinal
import Ripple.BoundedUniversality.BGP.SelectorStackOpDischarge

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorUTubeMU
------------------------------------
P4-coarse wiring for the constructed `solMURepl` rail.

This file instantiates the clean F7 `SelectorReplicatorUTube` shell at the
universal-machine base `B_U`, with the per-cycle exponent
`coordDelta (cfg j) i`.  The genuinely deep analytic inputs are isolated in
`SelectorMUCoarseUTubeBudget`: the per-coordinate recurrence, the super-decay
eta radii, and the satisfiable weighted budget.

Closed here:
* `coordMultiplier` is weakened to the `B_U ^ coordDelta` product form.
* the delta-driven depth schema is exposed through `selectorMUCoarseDepthFrom`;
* F7 gives all-cycle select-window `UTube`;
* the right endpoint `selectorMUWriteHoldTime j` is recovered by the same
  weighted-to-radius algebra, so it can feed the old `hutube_write` shape.

Carried, because no current file proves it for `solMURepl`:
* the constructed-solution `MURecur_repl` with the new per-cycle analog error
  `η`;
* bounded/super-decaying `η` and the corresponding `Wbound` radius inequality;
* equality between direct list-depth `MachineInstance.depthU cfg j i` and the
  delta recurrence, unless one supplies `SelectorStackDepthStepSemanticsU`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Filter Set MachineInstance
open scoped Topology

/-- The concrete universal base is strictly larger than one. -/
theorem selectorMU_B_U_real_gt_one : (1 : ℝ) < (B_U : ℝ) := by
  norm_num [B_U]

/-- The per-cycle, per-coordinate depth increment used by the P4-coarse budget. -/
def selectorMUCoarseDelta (cfg : ℕ → UConf) (j : ℕ) (i : Fin d_U) : ℤ :=
  stackMachineEncodingU.coordDelta (cfg j) i

/--
The delta-generated depth schema.  This is the satisfiable replacement for the
old future-budget `D - j`: it is driven only by the current configuration's
`coordDelta`.
-/
def selectorMUCoarseDepthFrom (cfg : ℕ → UConf) (d0 : Fin d_U → ℤ) :
    ℕ → Fin d_U → ℤ :=
  contractDepthU stackMachineEncodingU cfg d0

/-- The delta-generated schema has exactly the recurrence F7 needs. -/
theorem selectorMUCoarseDepthFrom_step
    (cfg : ℕ → UConf) (d0 : Fin d_U → ℤ) (j : ℕ) (i : Fin d_U) :
    selectorMUCoarseDepthFrom cfg d0 (j + 1) i =
      selectorMUCoarseDepthFrom cfg d0 j i - selectorMUCoarseDelta cfg j i := by
  exact contractDepthU_step stackMachineEncodingU cfg d0 j i

/--
Product-form weakening of the branch diagonal multiplier to `B_U ^ coordDelta`.
This is the usable form of the requested `coordMultiplier ≤ B_U^coordDelta`.
-/
theorem selectorMU_coordMultiplier_error_le_BUpow_coordDelta
    (cfg : ℕ → UConf) (j : ℕ) (i : Fin d_U) (x : Fin d_U → ℝ) :
    stackMachineEncodingU.coordMultiplier (cfg j) i *
        |x i - stackMachineEncodingU.enc (cfg j) i| ≤
      (B_U : ℝ) ^ selectorMUCoarseDelta cfg j i *
        |x i - stackMachineEncodingU.enc (cfg j) i| := by
  simpa [selectorMUCoarseDelta] using
    stackMachineEncodingU.coordMultiplier_error_le_zpow (cfg j) i x

/--
Current-list-depth recurrence, separated from the generated schema.

For stack coordinates this is exactly the public semantic bridge currently
carried by `SelectorStackOpDischarge`; reset coordinates are depth zero.  This
is the missing discharge needed to identify `selectorMUCoarseDepthFrom` with
the actual list lengths rather than merely the delta-generated debt.
-/
def SelectorMUCurrentDepthStep (cfg : ℕ → UConf) : Prop :=
  ∀ (j : ℕ) (i : Fin d_U),
    MachineInstance.depthU cfg (j + 1) i =
      MachineInstance.depthU cfg j i - selectorMUCoarseDelta cfg j i

/--
The P4-coarse budget package consumed by F7.

The fields are intentionally over one word `w` and one abstract solution family:
all expensive `solMURepl` whnf work is avoided until the final theorem is
instantiated by the caller.
-/
structure SelectorMUCoarseUTubeBudget
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {M : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta M κ₀ g₀)
    (cfg : ℕ → UConf) (w : ℕ) where
  dep : ℕ → Fin d_U → ℤ
  η : ℕ → Fin d_U → ℝ
  Wbound : ℕ → Fin d_U → ℝ
  εhold : ℝ
  hdep_step :
    ∀ (j : ℕ) (i : Fin d_U), dep (j + 1) i = dep j i - selectorMUCoarseDelta cfg j i
  hdep_nonneg : ∀ (j : ℕ) (i : Fin d_U), 0 ≤ dep j i
  hη_nonneg : ∀ (j : ℕ) (i : Fin d_U), 0 ≤ η j i
  hη_tendsto_zero : ∀ i, Tendsto (fun j : ℕ => η j i) atTop (𝓝 0)
  hinit :
    MUWeighted_repl (sol w) (fun j : ℕ => stackMachineEncodingU.enc (cfg j))
      (B_U : ℝ) dep Wbound 0
  hrecur :
    ∀ (j : ℕ),
      MUWeighted_repl (sol w) (fun j : ℕ => stackMachineEncodingU.enc (cfg j))
        (B_U : ℝ) dep Wbound j →
        MURecur_repl (sol w) (fun j : ℕ => stackMachineEncodingU.enc (cfg j))
          (B_U : ℝ) (selectorMUCoarseDelta cfg) η j
  hWstep :
    ∀ (j : ℕ) (i : Fin d_U),
      Wbound j i + (B_U : ℝ) ^ dep (j + 1) i * η j i ≤ Wbound (j + 1) i
  hhold :
    ∀ (j : ℕ) (i : Fin d_U),
      ∀ t ∈ Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
      |(sol w).u t i - (sol w).u (selectorMUWriteStartTime j) i| ≤ εhold
  hradius :
    ∀ (j : ℕ) (i : Fin d_U), Wbound j i / (B_U : ℝ) ^ dep j i + εhold ≤ r_LE_U

namespace SelectorMUCoarseUTubeBudget

theorem weighted_all
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {M : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta M κ₀ g₀}
    {cfg : ℕ → UConf} {w : ℕ}
    (budget : SelectorMUCoarseUTubeBudget sol cfg w) :
    ∀ (j : ℕ),
      MUWeighted_repl (sol w) (fun j : ℕ => stackMachineEncodingU.enc (cfg j))
        (B_U : ℝ) budget.dep budget.Wbound j :=
  MUWeighted_all_of_init_step_repl (sol w)
    (fun j : ℕ => stackMachineEncodingU.enc (cfg j))
    selectorMU_B_U_real_gt_one budget.dep (selectorMUCoarseDelta cfg)
    budget.η budget.Wbound budget.hdep_step budget.hWstep budget.hinit budget.hrecur

private theorem hold_literal
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {M : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta M κ₀ g₀}
    {cfg : ℕ → UConf} {w : ℕ}
    (budget : SelectorMUCoarseUTubeBudget sol cfg w) :
    ∀ (j : ℕ) (i : Fin d_U), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + Real.pi / 2),
      |(sol w).u t i -
        (sol w).u (2 * Real.pi * (j : ℝ) + Real.pi / 6) i| ≤ budget.εhold := by
  intro j i t ht
  simpa [selectorMUWriteStartTime, selectorMUWriteHoldTime] using budget.hhold j i t ht

/-- All-cycle P4-coarse tube on the select window, open at the right endpoint. -/
theorem coarse_utube_all
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {M : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta M κ₀ g₀}
    {cfg : ℕ → UConf} {w : ℕ}
    (budget : SelectorMUCoarseUTubeBudget sol cfg w) :
    ∀ (j : ℕ), ∀ t ∈ Ico (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
      UTube r_LE_U (cfg j) ((sol w).u t) := by
  intro j t ht
  have hF7 :=
    selector_MU_utube_all_repl (sol w) cfg selectorMU_B_U_real_gt_one
      budget.dep budget.Wbound
      (budget.weighted_all) budget.hold_literal budget.hradius
  exact hF7 j t (by
    simpa [selectorMUWriteStartTime, selectorMUWriteHoldTime] using ht)

/-- The weighted boundary estimate at the left edge, with named write-time syntax. -/
theorem weighted_at_write_start
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {M : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta M κ₀ g₀}
    {cfg : ℕ → UConf} {w : ℕ}
    (budget : SelectorMUCoarseUTubeBudget sol cfg w) (j : ℕ) :
    ∀ i,
      (B_U : ℝ) ^ budget.dep j i *
          |(sol w).u (selectorMUWriteStartTime j) i -
            stackMachineEncodingU.enc (cfg j) i| ≤ budget.Wbound j i := by
  intro i
  simpa [MUWeighted_repl, muBoundaryError_repl, selectorMUWriteStartTime] using
    budget.weighted_all j i

/-- The right endpoint `selectorMUWriteHoldTime j`, needed by the old `hutube_write` field. -/
theorem coarse_utube_write_hold
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {M : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta M κ₀ g₀}
    {cfg : ℕ → UConf} {w : ℕ}
    (budget : SelectorMUCoarseUTubeBudget sol cfg w) :
    ∀ (j : ℕ), UTube r_LE_U (cfg j) ((sol w).u (selectorMUWriteHoldTime j)) := by
  intro j
  refine weighted_boundary_to_radius_repl (sol w)
    (stackMachineEncodingU.enc (cfg j)) selectorMU_B_U_real_gt_one
    (budget.dep j) (budget.Wbound j)
    (a := selectorMUWriteStartTime j) (t := selectorMUWriteHoldTime j)
    (εhold := budget.εhold) (ρ := r_LE_U) ?_ (budget.hradius j)
    (budget.weighted_at_write_start j)
  intro i
  exact budget.hhold j i (selectorMUWriteHoldTime j)
    ⟨selectorMUWriteStart_le_hold j, le_rfl⟩

/-- Coordinatewise form of `coarse_utube_write_hold`, matching `hutube_write`. -/
theorem hutube_write_of_coarse
    {p : DynGateParams}
    {eta : ℚ} {heta : 0 < eta} {M : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta M κ₀ g₀}
    {cfg : ℕ → UConf} {w : ℕ}
    (budget : SelectorMUCoarseUTubeBudget sol cfg w) :
    ∀ (j : ℕ) (i : Fin d_U),
      |(sol w).u (selectorMUWriteHoldTime j) i -
        stackMachineEncodingU.enc (cfg j) i| ≤ r_LE_U := by
  intro j i
  exact budget.coarse_utube_write_hold j i

end SelectorMUCoarseUTubeBudget

/--
Settled-facts wrapper: for the `cfg` stored in `MUReplicatorSettledFacts`, the
coarse tube follows from the P4-coarse budget package.
-/
theorem solMURepl_coarse_utube_all
    {eta : ℚ} {heta : 0 < eta} {M : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta M κ₀ g₀}
    (settled : MUReplicatorSettledFacts sol) (w : ℕ)
    (budget : SelectorMUCoarseUTubeBudget sol (fun j : ℕ => settled.cfg w j) w) :
    ∀ (j : ℕ), ∀ t ∈ Ico (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
      UTube r_LE_U (settled.cfg w j) ((sol w).u t) :=
  budget.coarse_utube_all

/-- Endpoint wrapper for the `hutube_write` time in `MUReplicatorSettledFacts`. -/
theorem solMURepl_coarse_hutube_write
    {eta : ℚ} {heta : 0 < eta} {M : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta M κ₀ g₀}
    (settled : MUReplicatorSettledFacts sol) (w : ℕ)
    (budget : SelectorMUCoarseUTubeBudget sol (fun j : ℕ => settled.cfg w j) w) :
    ∀ (j : ℕ) (i : Fin d_U),
      |(sol w).u (selectorMUWriteHoldTime j) i -
        stackMachineEncodingU.enc (settled.cfg w j) i| ≤ r_LE_U :=
  budget.hutube_write_of_coarse

#print axioms selectorMU_B_U_real_gt_one
#print axioms selectorMUCoarseDelta
#print axioms selectorMUCoarseDepthFrom
#print axioms selectorMUCoarseDepthFrom_step
#print axioms selectorMU_coordMultiplier_error_le_BUpow_coordDelta
#print axioms SelectorMUCurrentDepthStep
#print axioms SelectorMUCoarseUTubeBudget
#print axioms SelectorMUCoarseUTubeBudget.weighted_all
#print axioms SelectorMUCoarseUTubeBudget.coarse_utube_all
#print axioms SelectorMUCoarseUTubeBudget.weighted_at_write_start
#print axioms SelectorMUCoarseUTubeBudget.coarse_utube_write_hold
#print axioms SelectorMUCoarseUTubeBudget.hutube_write_of_coarse
#print axioms solMURepl_coarse_utube_all
#print axioms solMURepl_coarse_hutube_write

end Ripple.BoundedUniversality.BGP
