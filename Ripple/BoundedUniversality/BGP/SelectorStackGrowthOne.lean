import Ripple.BoundedUniversality.BGP.MachineInstance

/-!
Ripple.BoundedUniversality.BGP.SelectorStackGrowthOne
---------------------------------

Per-coordinate stack-length growth for the concrete finite-support universal
machine instance.  One `M_U.step` may execute a bounded TM2 statement body and
may touch several stacks, but each of the four stack coordinates grows by at
most one symbol in that one step.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open MachineInstance
open UniversalMachine
open Turing.PartrecToTM2

theorem step_none_stack_growth_le_one
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU (finStepBranch (c := c_f) none (v, S)) s).length : ℤ)
      ≤ ((indexedStackU ((none, v, S) : UConf) s).length : ℤ) + 1 := by
  rcases S with ⟨M, R, A, D⟩
  fin_cases s <;>
    simp [finStepBranch, indexedStackU, stackKindOfIndexU,
      mainStackU, revStackU, auxStackU, dataStackU]

set_option maxHeartbeats 1600000 in
-- Large finite case split over four stacks and conditional TM2 clauses.
set_option maxRecDepth 2048 in
theorem step_move_stack_growth_le_one
    (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU
        (finStepBranch (c := c_f) (some ⟨Λ'.move p k₁ k₂ q, hmem⟩) (v, S)) s).length : ℤ)
      ≤ ((indexedStackU ((some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, S) : UConf) s).length : ℤ) + 1 := by
  rcases S with ⟨M, R, A, D⟩
  cases M <;> cases R <;> cases A <;> cases D <;>
  fin_cases s <;> cases k₁ <;> cases k₂ <;>
    simp [finStepBranch, indexedStackU, stackKindOfIndexU,
      mainStackU, revStackU, auxStackU, dataStackU,
      stackPop, stackPush, stackSet, stackGet] <;>
    repeat split_ifs <;>
    simp_all
  all_goals omega

set_option maxHeartbeats 4000000 in
-- Large finite case split over four stacks and conditional TM2 clauses.
theorem step_clear_stack_growth_le_one
    (p : Γ' → Bool) (k : K') (q : Λ')
    (hmem : Λ'.clear p k q ∈ supportSet c_f)
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU
        (finStepBranch (c := c_f) (some ⟨Λ'.clear p k q, hmem⟩) (v, S)) s).length : ℤ)
      ≤ ((indexedStackU ((some ⟨Λ'.clear p k q, hmem⟩, v, S) : UConf) s).length : ℤ) + 1 := by
  rcases S with ⟨M, R, A, D⟩
  cases M <;> cases R <;> cases A <;> cases D <;>
  fin_cases s <;> cases k <;>
    simp [finStepBranch, indexedStackU, stackKindOfIndexU,
      mainStackU, revStackU, auxStackU, dataStackU,
      stackPop, stackSet, stackGet] <;>
    repeat split_ifs <;>
    simp_all
  all_goals omega

theorem step_copy_stack_growth_le_one
    (q : Λ') (hmem : Λ'.copy q ∈ supportSet c_f)
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU
        (finStepBranch (c := c_f) (some ⟨Λ'.copy q, hmem⟩) (v, S)) s).length : ℤ)
      ≤ ((indexedStackU ((some ⟨Λ'.copy q, hmem⟩, v, S) : UConf) s).length : ℤ) + 1 := by
  rcases S with ⟨M, R, A, D⟩
  cases M <;> cases R <;> cases A <;> cases D <;>
  fin_cases s <;>
    simp [finStepBranch, indexedStackU, stackKindOfIndexU,
      mainStackU, revStackU, auxStackU, dataStackU,
      stackPop, stackPush, stackSet, stackGet] <;>
    omega

set_option maxHeartbeats 4000000 in
-- Large finite case split over four stacks and conditional TM2 clauses.
theorem step_push_stack_growth_le_one
    (k : K') (f : Option Γ' → Option Γ') (q : Λ')
    (hmem : Λ'.push k f q ∈ supportSet c_f)
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU
        (finStepBranch (c := c_f) (some ⟨Λ'.push k f q, hmem⟩) (v, S)) s).length : ℤ)
      ≤ ((indexedStackU ((some ⟨Λ'.push k f q, hmem⟩, v, S) : UConf) s).length : ℤ) + 1 := by
  rcases S with ⟨M, R, A, D⟩
  cases M <;> cases R <;> cases A <;> cases D <;>
  fin_cases s <;> cases k <;>
    simp [finStepBranch, indexedStackU, stackKindOfIndexU,
      mainStackU, revStackU, auxStackU, dataStackU,
      stackPush, stackSet, stackGet] <;>
    repeat split_ifs <;>
    simp_all

theorem step_read_stack_growth_le_one
    (q : Option Γ' → Λ') (hmem : Λ'.read q ∈ supportSet c_f)
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU
        (finStepBranch (c := c_f) (some ⟨Λ'.read q, hmem⟩) (v, S)) s).length : ℤ)
      ≤ ((indexedStackU ((some ⟨Λ'.read q, hmem⟩, v, S) : UConf) s).length : ℤ) + 1 := by
  rcases S with ⟨M, R, A, D⟩
  fin_cases s <;>
    simp [finStepBranch, indexedStackU, stackKindOfIndexU,
      mainStackU, revStackU, auxStackU, dataStackU]

theorem step_succ_stack_growth_le_one
    (q : Λ') (hmem : Λ'.succ q ∈ supportSet c_f)
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU
        (finStepBranch (c := c_f) (some ⟨Λ'.succ q, hmem⟩) (v, S)) s).length : ℤ)
      ≤ ((indexedStackU ((some ⟨Λ'.succ q, hmem⟩, v, S) : UConf) s).length : ℤ) + 1 := by
  rcases S with ⟨M, R, A, D⟩
  cases M <;> cases R <;> cases A <;> cases D <;>
  fin_cases s <;>
    simp [finStepBranch, indexedStackU, stackKindOfIndexU,
      mainStackU, revStackU, auxStackU, dataStackU,
      stackPop, stackPush, stackSet, stackGet, unrev] <;>
    repeat split_ifs <;>
    simp_all
  all_goals omega

theorem step_pred_stack_growth_le_one
    (q₁ q₂ : Λ') (hmem : Λ'.pred q₁ q₂ ∈ supportSet c_f)
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU
        (finStepBranch (c := c_f) (some ⟨Λ'.pred q₁ q₂, hmem⟩) (v, S)) s).length : ℤ)
      ≤ ((indexedStackU ((some ⟨Λ'.pred q₁ q₂, hmem⟩, v, S) : UConf) s).length : ℤ) + 1 := by
  rcases S with ⟨M, R, A, D⟩
  cases M <;> cases R <;> cases A <;> cases D <;>
  fin_cases s <;>
    simp [finStepBranch, indexedStackU, stackKindOfIndexU,
      mainStackU, revStackU, auxStackU, dataStackU,
      stackPop, stackPush, stackSet, stackGet, unrev, natEnd] <;>
    repeat split_ifs <;>
    simp_all
  all_goals omega

theorem step_ret_stack_growth_le_one
    (k : Cont') (hmem : Λ'.ret k ∈ supportSet c_f)
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU
        (finStepBranch (c := c_f) (some ⟨Λ'.ret k, hmem⟩) (v, S)) s).length : ℤ)
      ≤ ((indexedStackU ((some ⟨Λ'.ret k, hmem⟩, v, S) : UConf) s).length : ℤ) + 1 := by
  rcases S with ⟨M, R, A, D⟩
  cases k with
  | cons₁ fs k =>
      cases M <;> cases R <;> cases A <;> cases D <;>
      fin_cases s <;>
      simp [finStepBranch, indexedStackU, stackKindOfIndexU,
        mainStackU, revStackU, auxStackU, dataStackU]
  | cons₂ k =>
      cases M <;> cases R <;> cases A <;> cases D <;>
      fin_cases s <;>
      simp [finStepBranch, indexedStackU, stackKindOfIndexU,
        mainStackU, revStackU, auxStackU, dataStackU]
  | comp f k =>
      cases M <;> cases R <;> cases A <;> cases D <;>
      fin_cases s <;>
      simp [finStepBranch, indexedStackU, stackKindOfIndexU,
        mainStackU, revStackU, auxStackU, dataStackU]
  | fix f k =>
      cases M <;> cases R <;> cases A <;> cases D <;>
      fin_cases s <;>
      simp [finStepBranch, indexedStackU, stackKindOfIndexU,
        mainStackU, revStackU, auxStackU, dataStackU,
        stackPop, stackSet, stackGet, natEnd] <;>
      repeat split_ifs <;>
      simp_all
      all_goals omega
  | halt =>
      cases M <;> cases R <;> cases A <;> cases D <;>
      fin_cases s <;>
      simp [finStepBranch, indexedStackU, stackKindOfIndexU,
        mainStackU, revStackU, auxStackU, dataStackU]

theorem finStepBranch_stack_growth_le_one
    (ol : Option (SuppLabel c_f)) (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU (finStepBranch (c := c_f) ol (v, S)) s).length : ℤ)
      ≤ ((indexedStackU ((ol, v, S) : UConf) s).length : ℤ) + 1 := by
  cases ol with
  | none =>
      exact step_none_stack_growth_le_one v S s
  | some l =>
      rcases l with ⟨lv, hmem⟩
      cases lv with
      | move p k₁ k₂ q => exact step_move_stack_growth_le_one p k₁ k₂ q hmem v S s
      | clear p k q => exact step_clear_stack_growth_le_one p k q hmem v S s
      | copy q => exact step_copy_stack_growth_le_one q hmem v S s
      | push k f q => exact step_push_stack_growth_le_one k f q hmem v S s
      | read q => exact step_read_stack_growth_le_one q hmem v S s
      | succ q => exact step_succ_stack_growth_le_one q hmem v S s
      | pred q₁ q₂ => exact step_pred_stack_growth_le_one q₁ q₂ hmem v S s
      | ret k => exact step_ret_stack_growth_le_one k hmem v S s

/-- Every `M_U.step` grows each of the 4 stacks by at most one symbol. -/
theorem M_U_stack_growth_le_one (c : UConf) (s : Fin 4) :
    ((indexedStackU (M_U.step c) s).length : ℤ)
      ≤ ((indexedStackU c s).length : ℤ) + 1 := by
  change ((indexedStackU (finStep c) s).length : ℤ)
      ≤ ((indexedStackU c s).length : ℤ) + 1
  rw [← finStepBranch_eq_finStep c]
  exact finStepBranch_stack_growth_le_one c.1 c.2.1 c.2.2 s

end Ripple.BoundedUniversality.BGP
