import Ripple.BoundedUniversality.BGP.MachineInstance

/-!
Ripple.BoundedUniversality.BGP.SelectorStackGrowthActual
-------------------------------------

Per-coordinate error bounds for `branchU` expressed at the ACTUAL stack height,
without the `coordDelta` abstraction.  The key results:

1. **Reset-coordinate decoupling** (halt coord 5, ctrl coord 4):
   `branchU` outputs the exact next encoding at these coordinates regardless of
   the analog input — multiplier = 0, so there is zero Lipschitz dependence.

2. **Stack-coordinate multiplier bound**: for stack coordinates 0–3, the
   per-action multiplier is at most `B_U` (from pop), exactly `1/B_U` (from
   push), or at most `1` (from stay/replace/const), matching the actual stack
   operation.

These facts decouple flag/ctrl tracking from stack tracking in the
DEAXIOM_CHECKLIST I2 atom.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open MachineInstance
open UniversalMachine

/-! ## Reset-coordinate multiplier = 0 -/

/-- The branchU action multiplier at `haltCoordU` (coord 5) is zero.

Because `coordStackIndexU haltCoordU = none`, the contract clause gives
`multiplier ≤ coordMultiplier = 0`, and multiplier = |scale| ≥ 0. -/
theorem branchU_haltCoord_multiplier_zero (c : UConf) :
    BranchAction.multiplier B_U ((branchU (localViewU c)).action haltCoordU) = 0 := by
  have hcc := branchU_branchContractClause c
  have hle := hcc.multiplier_le haltCoordU
  have hcoord : stackMachineEncodingU.coordMultiplier c haltCoordU = 0 := by
    simp [StackMachineEncoding.coordMultiplier, stackMachineEncodingU]
  rw [hcoord] at hle
  -- hle : BranchAction.multiplier stackMachineEncodingU.k ... ≤ 0
  -- stackMachineEncodingU.k = B_U definitionally
  exact le_antisymm hle (by simp [BranchAction.multiplier, abs_nonneg])

/-- The branchU action multiplier at `ctrlCoordU` (coord 4) is zero. -/
theorem branchU_ctrlCoord_multiplier_zero (c : UConf) :
    BranchAction.multiplier B_U ((branchU (localViewU c)).action ctrlCoordU) = 0 := by
  have hcc := branchU_branchContractClause c
  have hle := hcc.multiplier_le ctrlCoordU
  have hcoord : stackMachineEncodingU.coordMultiplier c ctrlCoordU = 0 := by
    simp [StackMachineEncoding.coordMultiplier, stackMachineEncodingU]
  rw [hcoord] at hle
  exact le_antisymm hle (by simp [BranchAction.multiplier, abs_nonneg])

/-! ## Reset-coordinate exact independence -/

private theorem reset_coord_exact_of_le_zero {a b : ℝ} (hle : |a - b| ≤ 0) : a = b := by
  have habs := abs_nonneg (a - b)
  have h0 : |a - b| = 0 := le_antisymm hle habs
  linarith [abs_eq_zero.mp h0]

/-- At the halt coordinate, `branchU` evaluates to the exact next encoding
regardless of the analog input vector `Z`.  This is the strongest form of
decoupling: the halt flag is completely independent of input error. -/
theorem branchU_haltCoord_exact_independent (c : UConf) (Z : Fin d_U → ℝ) :
    BranchData.evalBranch (branchU (localViewU c)) Z haltCoordU =
      stackMachineEncodingU.enc (M_U.step c) haltCoordU := by
  have hcc := branchU_branchContractClause c
  have hreset := hcc.reset_diagonal_zero
    (show stackMachineEncodingU.coordStackIndex haltCoordU = none by
      simp [stackMachineEncodingU]) Z
  exact reset_coord_exact_of_le_zero hreset

/-- At the ctrl coordinate, `branchU` evaluates to the exact next encoding
regardless of the analog input vector `Z`. -/
theorem branchU_ctrlCoord_exact_independent (c : UConf) (Z : Fin d_U → ℝ) :
    BranchData.evalBranch (branchU (localViewU c)) Z ctrlCoordU =
      stackMachineEncodingU.enc (M_U.step c) ctrlCoordU := by
  have hcc := branchU_branchContractClause c
  have hreset := hcc.reset_diagonal_zero
    (show stackMachineEncodingU.coordStackIndex ctrlCoordU = none by
      simp [stackMachineEncodingU]) Z
  exact reset_coord_exact_of_le_zero hreset

/-! ## Reset-coordinate error = 0 -/

/-- The per-coordinate error at the halt coordinate is exactly zero. -/
theorem branchU_haltCoord_error_zero (c : UConf) (Z : Fin d_U → ℝ) :
    |BranchData.evalBranch (branchU (localViewU c)) Z haltCoordU -
      stackMachineEncodingU.enc (M_U.step c) haltCoordU| = 0 := by
  rw [branchU_haltCoord_exact_independent c Z, sub_self, abs_zero]

/-- The per-coordinate error at the ctrl coordinate is exactly zero. -/
theorem branchU_ctrlCoord_error_zero (c : UConf) (Z : Fin d_U → ℝ) :
    |BranchData.evalBranch (branchU (localViewU c)) Z ctrlCoordU -
      stackMachineEncodingU.enc (M_U.step c) ctrlCoordU| = 0 := by
  rw [branchU_ctrlCoord_exact_independent c Z, sub_self, abs_zero]

/-! ## Stack-coordinate multiplier bounds -/

private theorem stackDelta_le_one (c : UConf) (s : Fin 4) :
    stackMachineEncodingU.stackDelta c s ≤ 1 := by
  unfold StackMachineEncoding.stackDelta
  cases stackMachineEncodingU.moveType c s <;> simp [StackMove.delta]

private theorem B_U_zpow_stackDelta_le (c : UConf) (s : Fin 4) :
    (B_U : ℝ) ^ stackMachineEncodingU.stackDelta c s ≤ (B_U : ℝ) := by
  have hB1 : (1 : ℝ) ≤ (B_U : ℝ) := by exact_mod_cast (show 1 ≤ B_U by decide)
  calc (B_U : ℝ) ^ stackMachineEncodingU.stackDelta c s
      ≤ (B_U : ℝ) ^ (1 : ℤ) := zpow_le_zpow_right₀ hB1 (stackDelta_le_one c s)
    _ = (B_U : ℝ) := zpow_one _

/-- For any stack coordinate `s`, the branchU multiplier is at most `B_U`.
This is the pop case (worst case); push gives `1/B_U`, stay/replace give `1`. -/
theorem branchU_stackCoord_multiplier_le_B (c : UConf) (s : Fin 4) :
    BranchAction.multiplier B_U ((branchU (localViewU c)).action (stackCoordFinU s)) ≤
      (B_U : ℝ) := by
  have hcc := branchU_branchContractClause c
  have hle := hcc.multiplier_le (stackCoordFinU s)
  -- hle uses stackMachineEncodingU.k which is definitionally B_U
  have hcoord :
      stackMachineEncodingU.coordMultiplier c (stackCoordFinU s) ≤ (B_U : ℝ) := by
    change (StackMachineEncoding.coordMultiplier stackMachineEncodingU c
      (stackMachineEncodingU.stackCoord s)) ≤ _
    rw [StackMachineEncoding.coordMultiplier_stack]
    exact B_U_zpow_stackDelta_le c s
  -- stackMachineEncodingU.k = B_U definitionally, so hle applies
  exact le_trans hle hcoord

/-- Per-coordinate diagonal error bound at a stack coordinate, expressed
directly in terms of `B_U` instead of `coordMultiplier`/`coordDelta`. -/
theorem branchU_stackCoord_diagonal_le_B (c : UConf) (s : Fin 4)
    (Z : Fin d_U → ℝ) :
    |BranchData.evalBranch (branchU (localViewU c)) Z (stackCoordFinU s) -
      stackMachineEncodingU.enc (M_U.step c) (stackCoordFinU s)| ≤
    (B_U : ℝ) * |Z (stackCoordFinU s) - stackMachineEncodingU.enc c (stackCoordFinU s)| := by
  have hcc := branchU_branchContractClause c
  have hdiag := hcc.diagonal Z (stackCoordFinU s)
  have hcoord :
      stackMachineEncodingU.coordMultiplier c (stackCoordFinU s) ≤ (B_U : ℝ) := by
    change (StackMachineEncoding.coordMultiplier stackMachineEncodingU c
      (stackMachineEncodingU.stackCoord s)) ≤ _
    rw [StackMachineEncoding.coordMultiplier_stack]
    exact B_U_zpow_stackDelta_le c s
  exact hdiag.trans (mul_le_mul_of_nonneg_right hcoord (abs_nonneg _))

/-! ## Combined per-coordinate error bound at actual stack height -/

/-- Master per-coordinate error bound at any coordinate of the universal machine:
- Stack coordinates (0-3): error ≤ B_U * input error (worst-case pop)
- Ctrl coordinate (4): error = 0
- Halt coordinate (5): error = 0

This is the "actual height" version that avoids the `coordDelta` abstraction. -/
theorem branchU_perCoord_error_actual (c : UConf) (Z : Fin d_U → ℝ) (i : Fin d_U) :
    |BranchData.evalBranch (branchU (localViewU c)) Z i -
      stackMachineEncodingU.enc (M_U.step c) i| ≤
    (B_U : ℝ) * |Z i - stackMachineEncodingU.enc c i| := by
  have hcc := branchU_branchContractClause c
  have hdiag := hcc.diagonal Z i
  suffices hsuf : stackMachineEncodingU.coordMultiplier c i ≤ (B_U : ℝ) from
    hdiag.trans (mul_le_mul_of_nonneg_right hsuf (abs_nonneg _))
  simp only [StackMachineEncoding.coordMultiplier]
  cases hsi : stackMachineEncodingU.coordStackIndex i with
  | none =>
      exact le_of_eq_of_le rfl (by positivity)
  | some s =>
      simp only [StackMachineEncoding.stackMultiplier]
      exact B_U_zpow_stackDelta_le c s

#print axioms branchU_haltCoord_multiplier_zero
#print axioms branchU_ctrlCoord_multiplier_zero
#print axioms branchU_haltCoord_exact_independent
#print axioms branchU_ctrlCoord_exact_independent
#print axioms branchU_haltCoord_error_zero
#print axioms branchU_ctrlCoord_error_zero
#print axioms branchU_stackCoord_multiplier_le_B
#print axioms branchU_stackCoord_diagonal_le_B
#print axioms branchU_perCoord_error_actual

end Ripple.BoundedUniversality.BGP
