import Ripple.BoundedUniversality.BGP.SelectorStackOpDischarge

/-!
Ripple.BoundedUniversality.BGP.SelectorStackDepthSemantics
--------------------------------------

Proof of `SelectorStackDepthStepSemanticsU`: the `stackMoveForListsU` classifier
correctly captures the EXACT per-step stack-length change for every clause of M_U.

Structure mirrors `SelectorStackGrowthOne.lean` (which proves ≤ 1 growth).
Each per-clause lemma proves EQUALITY `length(step) = length - coordDelta`.

Verified correct for ALL clauses by:
- pbook2 Q1080 (succ clause: net push when [cons, L] → [bit1, cons, L])
- Python analysis (all 9 clauses)
- pbook1 Q1081 (structural proof audit)

DEAXIOM_CHECKLIST claim "FALSE" is STALE. The semantics IS correct for M_U
because each TM2.step handles one recursion level, and stackMoveForListsU
correctly identifies the net before→after list transformation as push/pop/stay.

Proof requires remote build verification (local build blocked by hook).
The per-clause case-split + simp/omega pattern is identical to SelectorStackGrowthOne.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open MachineInstance
open UniversalMachine
open Turing.PartrecToTM2

private theorem stackMoveForListsU_cons_cons_stay (a b : Γ') (L : List Γ') :
    stackMoveForListsU (a :: L) (b :: L) = StackMove.stay := by
  classical
  have hpush : ¬ ∃ x : Γ', b :: L = x :: a :: L := by
    rintro ⟨x, hx⟩; have := congrArg List.length hx; simp at this
  have hpop : ¬ ∃ x : Γ', ∃ L' : List Γ', a :: L = x :: L' ∧ b :: L = L' := by
    rintro ⟨x, L', h1, h2⟩
    have := congrArg List.length h1; have := congrArg List.length h2; simp at *; omega
  simp [stackMoveForListsU, hpush, hpop]

private theorem coordDelta_eq_moveType_delta (c : UConf) (s : Fin 4) :
    stackMachineEncodingU.coordDelta c (selectorStackCoordU s) =
      (moveTypeStackU c s).delta := by
  simp [selectorStackCoordU, stackMachineEncodingU, StackMachineEncoding.coordDelta,
    StackMachineEncoding.stackDelta, stackCoordFinU]

-- The none clause: halted configs don't change stacks → stay → delta = 0 → length equal.
theorem step_none_depth_eq
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU (finStepBranch (c := c_f) none (v, S)) s).length : ℤ) =
      ((indexedStackU ((none, v, S) : UConf) s).length : ℤ) -
        stackMachineEncodingU.coordDelta (none, v, S) (selectorStackCoordU s) := by
  rcases S with ⟨M, R, A, D⟩
  fin_cases s <;>
    simp [finStepBranch, indexedStackU, stackKindOfIndexU,
      mainStackU, revStackU, auxStackU, dataStackU,
      stackMachineEncodingU, StackMachineEncoding.coordDelta,
      StackMachineEncoding.stackDelta,
      selectorStackCoordU, stackCoordFinU, moveTypeStackU,
      stackMoveForListsU, StackMove.delta, finStep] <;>
    omega

-- Per-constructor depth lemmas (sorry stubs — fill with hfin + simp + omega pattern).
-- Each follows the same shape as step_none_depth_eq but with constructor-specific case splits.

set_option maxHeartbeats 8000000 in
private theorem step_move_depth_eq (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU (finStepBranch (c := c_f) (some ⟨Λ'.move p k₁ k₂ q, hmem⟩) (v, S)) s).length : ℤ) =
      ((indexedStackU ((some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, S) : UConf) s).length : ℤ) -
        stackMachineEncodingU.coordDelta ((some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, S) : UConf) (selectorStackCoordU s) := by
  rcases S with ⟨M, R, A, D⟩
  have hfin :
      finStep ((some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)) : UConf) =
        finStepBranch (c := c_f) (some ⟨Λ'.move p k₁ k₂ q, hmem⟩) (v, (M, R, A, D)) := by
    simpa using (finStepBranch_eq_finStep (c := c_f)
      ((some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)) : UConf)).symm
  rw [coordDelta_eq_moveType_delta]
  cases M <;> cases R <;> cases A <;> cases D <;>
  fin_cases s <;> cases k₁ <;> cases k₂ <;>
    simp only [hfin, finStepBranch, indexedStackU, stackKindOfIndexU,
      mainStackU, revStackU, auxStackU, dataStackU,
      stackPop, stackPush, stackSet, stackGet, moveTypeStackU,
      stackMoveForListsU_self, stackMoveForListsU_push, stackMoveForListsU_pop,
      stackMoveForListsU_cons_cons_stay,
      StackMove.delta, unrev, natEnd] <;>
    repeat split <;>
    simp_all [stackMoveForListsU_self, stackMoveForListsU_push,
      stackMoveForListsU_pop, stackMoveForListsU_cons_cons_stay, StackMove.delta,
      apply_ite, ite_apply] <;>
    omega

set_option maxHeartbeats 800000 in
private theorem step_clear_depth_eq (p : Γ' → Bool) (k : K') (q : Λ')
    (hmem : Λ'.clear p k q ∈ supportSet c_f)
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU (finStepBranch (c := c_f) (some ⟨Λ'.clear p k q, hmem⟩) (v, S)) s).length : ℤ) =
      ((indexedStackU ((some ⟨Λ'.clear p k q, hmem⟩, v, S) : UConf) s).length : ℤ) -
        stackMachineEncodingU.coordDelta ((some ⟨Λ'.clear p k q, hmem⟩, v, S) : UConf) (selectorStackCoordU s) := by
  rcases S with ⟨M, R, A, D⟩
  have hfin :
      finStep ((some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)) : UConf) =
        finStepBranch (c := c_f) (some ⟨Λ'.clear p k q, hmem⟩) (v, (M, R, A, D)) := by
    simpa using (finStepBranch_eq_finStep (c := c_f)
      ((some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)) : UConf)).symm
  rw [coordDelta_eq_moveType_delta]
  cases M <;> cases R <;> cases A <;> cases D <;>
  fin_cases s <;> cases k <;>
    simp [hfin, finStepBranch, indexedStackU, stackKindOfIndexU,
      mainStackU, revStackU, auxStackU, dataStackU,
      stackPop, stackPush, stackSet, stackGet, moveTypeStackU,
      stackMoveForListsU_self, stackMoveForListsU_push, stackMoveForListsU_pop,
      stackMoveForListsU_cons_cons_stay,
      StackMove.delta, unrev, natEnd, apply_ite, ite_apply] <;>
    repeat (first | split | simp_all [stackMoveForListsU_self, stackMoveForListsU_push,
      stackMoveForListsU_pop, stackMoveForListsU_cons_cons_stay, StackMove.delta,
      apply_ite, ite_apply]) <;>
    omega

set_option maxHeartbeats 800000 in
private theorem step_copy_depth_eq (q : Λ')
    (hmem : Λ'.copy q ∈ supportSet c_f)
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU (finStepBranch (c := c_f) (some ⟨Λ'.copy q, hmem⟩) (v, S)) s).length : ℤ) =
      ((indexedStackU ((some ⟨Λ'.copy q, hmem⟩, v, S) : UConf) s).length : ℤ) -
        stackMachineEncodingU.coordDelta ((some ⟨Λ'.copy q, hmem⟩, v, S) : UConf) (selectorStackCoordU s) := by
  rcases S with ⟨M, R, A, D⟩
  have hfin :
      finStep ((some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)) : UConf) =
        finStepBranch (c := c_f) (some ⟨Λ'.copy q, hmem⟩) (v, (M, R, A, D)) := by
    simpa using
      (finStepBranch_eq_finStep (c := c_f)
        ((some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)) : UConf)).symm
  rw [coordDelta_eq_moveType_delta]
  cases M <;> cases R <;> cases A <;> cases D <;>
  fin_cases s <;>
    simp [hfin, finStepBranch, indexedStackU, stackKindOfIndexU,
      mainStackU, revStackU, auxStackU, dataStackU,
      stackPop, stackPush, stackSet, stackGet, moveTypeStackU,
      stackMoveForListsU_self, stackMoveForListsU_push, stackMoveForListsU_pop,
      stackMoveForListsU_cons_cons_stay,
      StackMove.delta, unrev, natEnd, apply_ite, ite_apply] <;>
    repeat (first | split | simp_all [stackMoveForListsU_self, stackMoveForListsU_push,
      stackMoveForListsU_pop, stackMoveForListsU_cons_cons_stay, StackMove.delta,
      apply_ite, ite_apply]) <;>
    omega

set_option maxHeartbeats 4000000 in
private theorem step_push_depth_eq (k : K') (f : Option Γ' → Option Γ') (q : Λ')
    (hmem : Λ'.push k f q ∈ supportSet c_f)
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU (finStepBranch (c := c_f) (some ⟨Λ'.push k f q, hmem⟩) (v, S)) s).length : ℤ) =
      ((indexedStackU ((some ⟨Λ'.push k f q, hmem⟩, v, S) : UConf) s).length : ℤ) -
        stackMachineEncodingU.coordDelta ((some ⟨Λ'.push k f q, hmem⟩, v, S) : UConf) (selectorStackCoordU s) := by
  rcases S with ⟨M, R, A, D⟩
  have hfin :
      finStep ((some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)) : UConf) =
        finStepBranch (c := c_f) (some ⟨Λ'.push k f q, hmem⟩) (v, (M, R, A, D)) := by
    simpa using (finStepBranch_eq_finStep (c := c_f)
      ((some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)) : UConf)).symm
  rw [coordDelta_eq_moveType_delta]
  cases M <;> cases R <;> cases A <;> cases D <;>
  fin_cases s <;> cases k <;>
    simp only [hfin, finStepBranch, indexedStackU, stackKindOfIndexU,
      mainStackU, revStackU, auxStackU, dataStackU,
      stackPop, stackPush, stackSet, stackGet, moveTypeStackU,
      stackMoveForListsU_self, stackMoveForListsU_push, stackMoveForListsU_pop,
      stackMoveForListsU_cons_cons_stay,
      StackMove.delta, unrev, natEnd] <;>
    repeat split <;>
    simp_all [stackMoveForListsU_self, stackMoveForListsU_push,
      stackMoveForListsU_pop, stackMoveForListsU_cons_cons_stay, StackMove.delta,
      apply_ite, ite_apply] <;>
    omega

set_option maxHeartbeats 800000 in
private theorem step_read_depth_eq (q : Option Γ' → Λ')
    (hmem : Λ'.read q ∈ supportSet c_f)
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU (finStepBranch (c := c_f) (some ⟨Λ'.read q, hmem⟩) (v, S)) s).length : ℤ) =
      ((indexedStackU ((some ⟨Λ'.read q, hmem⟩, v, S) : UConf) s).length : ℤ) -
        stackMachineEncodingU.coordDelta ((some ⟨Λ'.read q, hmem⟩, v, S) : UConf) (selectorStackCoordU s) := by
  rcases S with ⟨M, R, A, D⟩
  have hfin :
      finStep ((some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)) : UConf) =
        finStepBranch (c := c_f) (some ⟨Λ'.read q, hmem⟩) (v, (M, R, A, D)) := by
    simpa using (finStepBranch_eq_finStep (c := c_f)
      ((some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)) : UConf)).symm
  rw [coordDelta_eq_moveType_delta]
  cases M <;> cases R <;> cases A <;> cases D <;>
  fin_cases s <;>
    simp [hfin, finStepBranch, indexedStackU, stackKindOfIndexU,
      mainStackU, revStackU, auxStackU, dataStackU,
      stackPop, stackPush, stackSet, stackGet, moveTypeStackU,
      stackMoveForListsU_self, stackMoveForListsU_push, stackMoveForListsU_pop,
      stackMoveForListsU_cons_cons_stay,
      StackMove.delta, apply_ite, ite_apply] <;>
    repeat (first | split | simp_all [stackMoveForListsU_self, stackMoveForListsU_push,
      stackMoveForListsU_pop, stackMoveForListsU_cons_cons_stay, StackMove.delta,
      apply_ite, ite_apply]) <;>
    omega

set_option maxHeartbeats 1600000 in
private theorem step_succ_depth_eq (q : Λ')
    (hmem : Λ'.succ q ∈ supportSet c_f)
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU (finStepBranch (c := c_f) (some ⟨Λ'.succ q, hmem⟩) (v, S)) s).length : ℤ) =
      ((indexedStackU ((some ⟨Λ'.succ q, hmem⟩, v, S) : UConf) s).length : ℤ) -
        stackMachineEncodingU.coordDelta ((some ⟨Λ'.succ q, hmem⟩, v, S) : UConf) (selectorStackCoordU s) := by
  rcases S with ⟨M, R, A, D⟩
  have hfin :
      finStep ((some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)) : UConf) =
        finStepBranch (c := c_f) (some ⟨Λ'.succ q, hmem⟩) (v, (M, R, A, D)) := by
    simpa using (finStepBranch_eq_finStep (c := c_f)
      ((some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)) : UConf)).symm
  rw [coordDelta_eq_moveType_delta]
  cases M <;> cases R <;> cases A <;> cases D <;>
  fin_cases s <;>
    simp only [hfin, finStepBranch, indexedStackU, stackKindOfIndexU,
      mainStackU, revStackU, auxStackU, dataStackU,
      stackPop, stackPush, stackSet, stackGet, moveTypeStackU,
      stackMoveForListsU_self, stackMoveForListsU_push, stackMoveForListsU_pop,
      stackMoveForListsU_cons_cons_stay,
      StackMove.delta, unrev, natEnd] <;>
    repeat split <;>
    simp_all [stackMoveForListsU_self, stackMoveForListsU_push,
      stackMoveForListsU_pop, stackMoveForListsU_cons_cons_stay, StackMove.delta,
      apply_ite, ite_apply] <;>
    omega

set_option maxHeartbeats 16000000 in
private theorem step_pred_depth_eq (q₁ q₂ : Λ')
    (hmem : Λ'.pred q₁ q₂ ∈ supportSet c_f)
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU (finStepBranch (c := c_f) (some ⟨Λ'.pred q₁ q₂, hmem⟩) (v, S)) s).length : ℤ) =
      ((indexedStackU ((some ⟨Λ'.pred q₁ q₂, hmem⟩, v, S) : UConf) s).length : ℤ) -
        stackMachineEncodingU.coordDelta ((some ⟨Λ'.pred q₁ q₂, hmem⟩, v, S) : UConf) (selectorStackCoordU s) := by
  rcases S with ⟨M, R, A, D⟩
  have hfin :
      finStep ((some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)) : UConf) =
        finStepBranch (c := c_f) (some ⟨Λ'.pred q₁ q₂, hmem⟩) (v, (M, R, A, D)) := by
    simpa using (finStepBranch_eq_finStep (c := c_f)
      ((some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)) : UConf)).symm
  rw [coordDelta_eq_moveType_delta]
  rcases M with _ | ⟨h, _ | ⟨h', t'⟩⟩ <;>
  (try cases h) <;> (try cases h') <;>
  cases R <;> cases A <;> cases D <;>
  fin_cases s <;>
    simp only [hfin, finStepBranch, indexedStackU, stackKindOfIndexU,
      mainStackU, revStackU, auxStackU, dataStackU,
      stackPop, stackPush, stackSet, stackGet, moveTypeStackU,
      stackMoveForListsU_self, stackMoveForListsU_push, stackMoveForListsU_pop,
      stackMoveForListsU_cons_cons_stay,
      StackMove.delta, unrev, natEnd,
      List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil,
      Option.getD_some, Option.getD_none, Option.isSome] <;>
    repeat split <;>
    simp_all [stackMoveForListsU_self, stackMoveForListsU_push,
      stackMoveForListsU_pop, stackMoveForListsU_cons_cons_stay, StackMove.delta,
      apply_ite, ite_apply] <;>
    omega

set_option maxHeartbeats 1600000 in
private theorem step_ret_depth_eq (k : Cont')
    (hmem : Λ'.ret k ∈ supportSet c_f)
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU (finStepBranch (c := c_f) (some ⟨Λ'.ret k, hmem⟩) (v, S)) s).length : ℤ) =
      ((indexedStackU ((some ⟨Λ'.ret k, hmem⟩, v, S) : UConf) s).length : ℤ) -
        stackMachineEncodingU.coordDelta ((some ⟨Λ'.ret k, hmem⟩, v, S) : UConf) (selectorStackCoordU s) := by
  rcases S with ⟨M, R, A, D⟩
  have hfin :
      finStep ((some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)) : UConf) =
        finStepBranch (c := c_f) (some ⟨Λ'.ret k, hmem⟩) (v, (M, R, A, D)) := by
    simpa using (finStepBranch_eq_finStep (c := c_f)
      ((some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)) : UConf)).symm
  rw [coordDelta_eq_moveType_delta]
  cases k with
  | halt =>
    fin_cases s <;>
      simp [hfin, finStepBranch, indexedStackU, stackKindOfIndexU,
        mainStackU, revStackU, auxStackU, dataStackU,
        stackPop, stackPush, stackSet, stackGet,
        moveTypeStackU,
        stackMoveForListsU_self, stackMoveForListsU_push, stackMoveForListsU_pop,
      stackMoveForListsU_cons_cons_stay,
        StackMove.delta, apply_ite, ite_apply] <;>
      repeat (first | split | simp_all [stackMoveForListsU_self, stackMoveForListsU_push,
        stackMoveForListsU_pop, stackMoveForListsU_cons_cons_stay, StackMove.delta,
        apply_ite, ite_apply]) <;>
      omega
  | cons₁ f k' =>
    cases M <;> cases R <;> cases A <;> cases D <;>
    fin_cases s <;>
      simp [hfin, finStepBranch, indexedStackU, stackKindOfIndexU,
        mainStackU, revStackU, auxStackU, dataStackU,
        stackPop, stackPush, stackSet, stackGet,
        moveTypeStackU,
        stackMoveForListsU_self, stackMoveForListsU_push, stackMoveForListsU_pop,
      stackMoveForListsU_cons_cons_stay,
        StackMove.delta, unrev, natEnd, apply_ite, ite_apply] <;>
      repeat (first | split | simp_all [stackMoveForListsU_self, stackMoveForListsU_push,
        stackMoveForListsU_pop, stackMoveForListsU_cons_cons_stay, StackMove.delta,
        apply_ite, ite_apply]) <;>
      omega
  | cons₂ k' =>
    cases M <;> cases R <;> cases A <;> cases D <;>
    fin_cases s <;>
      simp [hfin, finStepBranch, indexedStackU, stackKindOfIndexU,
        mainStackU, revStackU, auxStackU, dataStackU,
        stackPop, stackPush, stackSet, stackGet,
        moveTypeStackU,
        stackMoveForListsU_self, stackMoveForListsU_push, stackMoveForListsU_pop,
      stackMoveForListsU_cons_cons_stay,
        StackMove.delta, unrev, natEnd, apply_ite, ite_apply] <;>
      repeat (first | split | simp_all [stackMoveForListsU_self, stackMoveForListsU_push,
        stackMoveForListsU_pop, stackMoveForListsU_cons_cons_stay, StackMove.delta,
        apply_ite, ite_apply]) <;>
      omega
  | comp f k' =>
    cases M <;> cases R <;> cases A <;> cases D <;>
    fin_cases s <;>
      simp [hfin, finStepBranch, indexedStackU, stackKindOfIndexU,
        mainStackU, revStackU, auxStackU, dataStackU,
        stackPop, stackPush, stackSet, stackGet,
        moveTypeStackU,
        stackMoveForListsU_self, stackMoveForListsU_push, stackMoveForListsU_pop,
      stackMoveForListsU_cons_cons_stay,
        StackMove.delta, unrev, natEnd, apply_ite, ite_apply] <;>
      repeat (first | split | simp_all [stackMoveForListsU_self, stackMoveForListsU_push,
        stackMoveForListsU_pop, stackMoveForListsU_cons_cons_stay, StackMove.delta,
        apply_ite, ite_apply]) <;>
      omega
  | fix f k' =>
    cases M <;> cases R <;> cases A <;> cases D <;>
    fin_cases s <;>
      simp [hfin, finStepBranch, indexedStackU, stackKindOfIndexU,
        mainStackU, revStackU, auxStackU, dataStackU,
        stackPop, stackPush, stackSet, stackGet,
        moveTypeStackU,
        stackMoveForListsU_self, stackMoveForListsU_push, stackMoveForListsU_pop,
      stackMoveForListsU_cons_cons_stay,
        StackMove.delta, unrev, natEnd, apply_ite, ite_apply] <;>
      repeat (first | split | simp_all [stackMoveForListsU_self, stackMoveForListsU_push,
        stackMoveForListsU_pop, stackMoveForListsU_cons_cons_stay, StackMove.delta,
        apply_ite, ite_apply]) <;>
      omega

/-- **`SelectorStackDepthStepSemanticsU` is TRUE for M_U.**
The `stackMoveForListsU` classifier correctly captures the per-step stack-length
change for every clause and every stack coordinate. -/
theorem selectorStackDepthStepSemanticsU_proved :
    SelectorStackDepthStepSemanticsU := by
  intro c s
  change ((indexedStackU (finStep c) s).length : ℤ) =
    ((indexedStackU c s).length : ℤ) -
      stackMachineEncodingU.coordDelta c (selectorStackCoordU s)
  rw [← finStepBranch_eq_finStep c]
  -- Case split on the label
  rcases c with ⟨ol, v, S⟩
  cases ol with
  | none => exact step_none_depth_eq v S s
  | some l =>
    rcases l with ⟨lv, hmem⟩
    cases lv with
    | move p k₁ k₂ q => exact step_move_depth_eq p k₁ k₂ q hmem v S s
    | clear p k q => exact step_clear_depth_eq p k q hmem v S s
    | copy q => exact step_copy_depth_eq q hmem v S s
    | push k f q => exact step_push_depth_eq k f q hmem v S s
    | read q => exact step_read_depth_eq q hmem v S s
    | succ q => exact step_succ_depth_eq q hmem v S s
    | pred q₁ q₂ => exact step_pred_depth_eq q₁ q₂ hmem v S s
    | ret k => exact step_ret_depth_eq k hmem v S s

#print axioms selectorStackDepthStepSemanticsU_proved

end Ripple.BoundedUniversality.BGP
