import Ripple.BoundedUniversality.BGP.SelectorReplicatorUTubeBudget
import Ripple.BoundedUniversality.BGP.SelectorStackGrowthOne

/-!
Ripple.BoundedUniversality.BGP.SelectorDepthBound
-----------------------------
A4 producer (A1): the per-cycle stack-depth growth bound `H(j) ≤ H(0) + j`.

`uniform_reserve_forall_w_of_warmup` (SelectorForallW) needs the preloaded-height
bound `H_N(j+1) ≤ N + j` with `N = |w|` (the preload). Since one universal-machine
step changes each stack length by at most one (`StackMove.delta ∈ {−1, 0, +1}`,
so `coordDelta ≥ −1`), the depth grows by at most one per cycle, giving
`H(j) ≤ H(0) + j`. Taking `N := H(0) + 1` yields exactly `H(j+1) ≤ N + j`.

The exact push/pop depth recurrence is still available from
`SelectorStackDepthStepSemanticsU`; the growth-only bound below is now
unconditional, using the concrete list-length theorem
`M_U_stack_growth_le_one`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open MachineInstance

/-- One universal-machine step changes a stack length by at most one downward:
`coordDelta ≥ −1` (push is the only growth move, `delta = −1`). -/
theorem coordDelta_ge_neg_one (c : UConf) (i : Fin d_U) :
    (-1 : ℤ) ≤ stackMachineEncodingU.coordDelta c i := by
  unfold StackMachineEncoding.coordDelta
  cases hci : stackMachineEncodingU.coordStackIndex i with
  | none => norm_num
  | some s =>
    simp only
    unfold StackMachineEncoding.stackDelta
    cases stackMachineEncodingU.moveType c s <;> norm_num [StackMove.delta]

/-- One concrete universal-machine step grows the selected stack depth by at most one. -/
theorem selectorStackDepthU_succ_le_add_one (w : ℕ) (s : Fin 4) (j : ℕ) :
    selectorStackDepthU w s (j + 1) ≤ selectorStackDepthU w s j + 1 := by
  unfold selectorStackDepthU selectorStackCoordU
  rw [MachineInstance.depthU_stack, MachineInstance.depthU_stack]
  rw [selectorCfgU_succ w j]
  exact M_U_stack_growth_le_one (selectorCfgU w j) s

/-- **The stack depth grows by at most one per cycle: `H(j) ≤ H(0) + j`.** -/
theorem selectorStackDepthU_le_initial_add_unconditional (w : ℕ) (s : Fin 4) :
    ∀ j, selectorStackDepthU w s j ≤ selectorStackDepthU w s 0 + (j : ℤ) := by
  intro j
  induction j with
  | zero => simp
  | succ k ih =>
    have hstep := selectorStackDepthU_succ_le_add_one w s k
    push_cast at ih ⊢
    omega

/-- Compatibility wrapper for callers that still carry the exact depth-step
semantics hypothesis.  The growth-only conclusion no longer needs it. -/
theorem selectorStackDepthU_le_initial_add_of_semantics
    (_hsem : SelectorStackDepthStepSemanticsU) (w : ℕ) (s : Fin 4) :
    ∀ j, selectorStackDepthU w s j ≤ selectorStackDepthU w s 0 + (j : ℤ) :=
  selectorStackDepthU_le_initial_add_unconditional w s

/-- The input-length warm-up target `N = H(0) + 1`, giving the `uniform_reserve_forall_w_of_warmup`
form `H(j+1) ≤ N + j`. -/
def selectorInputHeightU (w : ℕ) (s : Fin 4) : ℤ :=
  selectorStackDepthU w s 0 + 1

/-- **The preloaded-height bound in the exact `hHpre` shape: `H(j+1) ≤ N + j`** with
`N = selectorInputHeightU`. -/
theorem selectorStackDepthU_succ_le_inputHeight_add_unconditional
    (w : ℕ) (s : Fin 4) :
    ∀ j, (selectorStackDepthU w s (j + 1) : ℝ)
      ≤ (selectorInputHeightU w s : ℝ) + (j : ℝ) := by
  intro j
  have h := selectorStackDepthU_le_initial_add_unconditional w s (j + 1)
  calc
    (selectorStackDepthU w s (j + 1) : ℝ)
        ≤ ((selectorStackDepthU w s 0 + ((j + 1 : ℕ) : ℤ) : ℤ) : ℝ) := by
          exact_mod_cast h
    _ = (selectorInputHeightU w s : ℝ) + (j : ℝ) := by
          simp [selectorInputHeightU]
          ring

/-- Compatibility wrapper for callers that still carry the exact depth-step
semantics hypothesis. -/
theorem selectorStackDepthU_succ_le_inputHeight_add
    (_hsem : SelectorStackDepthStepSemanticsU) (w : ℕ) (s : Fin 4) :
    ∀ j, (selectorStackDepthU w s (j + 1) : ℝ)
      ≤ (selectorInputHeightU w s : ℝ) + (j : ℝ) :=
  selectorStackDepthU_succ_le_inputHeight_add_unconditional w s

#print axioms coordDelta_ge_neg_one
#print axioms selectorStackDepthU_succ_le_add_one
#print axioms selectorStackDepthU_le_initial_add_unconditional
#print axioms selectorStackDepthU_le_initial_add_of_semantics
#print axioms selectorInputHeightU
#print axioms selectorStackDepthU_succ_le_inputHeight_add_unconditional
#print axioms selectorStackDepthU_succ_le_inputHeight_add

end Ripple.BoundedUniversality.BGP
