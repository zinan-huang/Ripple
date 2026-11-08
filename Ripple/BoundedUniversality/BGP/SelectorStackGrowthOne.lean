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

/-! ## One step changes each stack by at most one push, one pop, or a same-length rewrite

`StackStepRel L L'` says that `L'` arises from `L` by pushing one symbol, popping one
symbol, or keeping the length.  Every clause of `finStepBranch` relates each stack in this way
(`stackStepRel_finStepBranch`), proved from the generic `stackPop_get` / `stackPush_get`
equations instead of a case split over the shapes of all four stacks. -/

/-- One-step shape relation between a stack before (`L`) and after (`L'`) a step. -/
def StackStepRel (L L' : List Γ') : Prop :=
  (∃ a, L' = a :: L) ∨ (∃ a, L = a :: L') ∨ L'.length = L.length

theorem StackStepRel.refl (L : List Γ') : StackStepRel L L :=
  Or.inr (Or.inr rfl)

theorem StackStepRel.cons (a : Γ') (L : List Γ') : StackStepRel L (a :: L) :=
  Or.inl ⟨a, rfl⟩

theorem StackStepRel.tail (L : List Γ') : StackStepRel L L.tail := by
  cases L with
  | nil => exact StackStepRel.refl _
  | cons a t => exact Or.inr (Or.inl ⟨a, rfl⟩)

theorem StackStepRel.cons_tail (b : Γ') (L : List Γ') : StackStepRel L (b :: L.tail) := by
  cases L with
  | nil => exact StackStepRel.cons b []
  | cons a t => exact Or.inr (Or.inr (by simp))

theorem StackStepRel.cons_cons_tail (b c : Γ') {L : List Γ'} (h : L.head? = some c) :
    StackStepRel L (b :: c :: L.tail) := by
  cases L with
  | nil => simp at h
  | cons a t =>
      simp only [List.head?_cons, Option.some.injEq] at h
      subst h
      exact StackStepRel.cons b _

theorem StackStepRel.length_le {L L' : List Γ'} (h : StackStepRel L L') :
    (L'.length : ℤ) ≤ L.length + 1 := by
  rcases h with ⟨a, rfl⟩ | ⟨a, rfl⟩ | h
  · simp only [List.length_cons]; push_cast; omega
  · simp only [List.length_cons]; push_cast; omega
  · rw [h]; omega

/-- Under `StackStepRel`, the length change is the push/pop exponent of
`stackMoveForListsU`. -/
theorem StackStepRel.length_eq_sub_delta {L L' : List Γ'} (h : StackStepRel L L') :
    (L'.length : ℤ) = L.length - (stackMoveForListsU L L').delta := by
  rcases h with ⟨a, rfl⟩ | ⟨a, rfl⟩ | h
  · rw [stackMoveForListsU_push]
    simp [StackMove.delta]
  · rw [stackMoveForListsU_pop]
    simp [StackMove.delta]
  · classical
    have hpush : ¬ ∃ a : Γ', L' = a :: L := by
      rintro ⟨a, rfl⟩
      simp at h
    have hpop : ¬ ∃ a : Γ', L = a :: L' := by
      rintro ⟨a, rfl⟩
      simp at h
    have hpop' : ¬ ∃ a : Γ', ∃ M : List Γ', L = a :: M ∧ L' = M := by
      rintro ⟨a, M, rfl, rfl⟩
      exact hpop ⟨a, rfl⟩
    simp [stackMoveForListsU, hpush, hpop, hpop', StackMove.delta, h]

/-- A stack of a configuration, read through the contract index. -/
theorem indexedStackU_eq_stackGet (c : UConf) (s : Fin 4) :
    indexedStackU c s = stackGet c.2.2 (stackKindOfIndexU s) := by
  rcases c with ⟨q, v, M, R, A, D⟩
  fin_cases s <;> rfl

/-- Every clause of the finite-support step relates each stack by `StackStepRel`. -/
theorem stackStepRel_finStepBranch
    (ol : Option (SuppLabel c_f)) (v : Option Γ') (S : StackTuple) (j : K') :
    StackStepRel (stackGet S j) (stackGet (finStepBranch (c := c_f) ol (v, S)).2.2 j) := by
  rcases ol with _ | ⟨l, hmem⟩
  · exact StackStepRel.refl _
  cases l with
  | succ q =>
      simp only [finStepBranch]
      split_ifs with h1 h2
      all_goals (try simp only [stackPush_get, stackPop_get, stackPop_head] at *)
      all_goals (try split_ifs)
      all_goals (try subst_vars)
      all_goals first
        | exact StackStepRel.refl _
        | exact StackStepRel.tail _
        | exact StackStepRel.cons _ _
        | exact StackStepRel.cons_tail _ _
        | exact StackStepRel.cons_cons_tail _ _ h2
        | contradiction
  | _ =>
      all_goals (try cases ‹Cont'›)
      all_goals simp only [finStepBranch]
      all_goals (try split_ifs)
      all_goals (try simp only [stackPush_get, stackPop_get])
      all_goals (try split_ifs)
      all_goals (try subst_vars)
      all_goals first
        | exact StackStepRel.refl _
        | exact StackStepRel.tail _
        | exact StackStepRel.cons _ _
        | exact StackStepRel.cons_tail _ _
        | contradiction

/-- `StackStepRel` for the contract-indexed stacks of one `finStepBranch` step. -/
theorem stackStepRel_indexed_finStepBranch
    (ol : Option (SuppLabel c_f)) (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    StackStepRel (indexedStackU ((ol, v, S) : UConf) s)
      (indexedStackU (finStepBranch (c := c_f) ol (v, S)) s) := by
  rw [indexedStackU_eq_stackGet, indexedStackU_eq_stackGet]
  exact stackStepRel_finStepBranch ol v S _

theorem step_none_stack_growth_le_one
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU (finStepBranch (c := c_f) none (v, S)) s).length : ℤ)
      ≤ ((indexedStackU ((none, v, S) : UConf) s).length : ℤ) + 1 := by
  exact (stackStepRel_indexed_finStepBranch _ v S s).length_le

theorem step_move_stack_growth_le_one
    (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU
        (finStepBranch (c := c_f) (some ⟨Λ'.move p k₁ k₂ q, hmem⟩) (v, S)) s).length : ℤ)
      ≤ ((indexedStackU ((some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, S) : UConf) s).length : ℤ) + 1 := by
  exact (stackStepRel_indexed_finStepBranch _ v S s).length_le

theorem step_clear_stack_growth_le_one
    (p : Γ' → Bool) (k : K') (q : Λ')
    (hmem : Λ'.clear p k q ∈ supportSet c_f)
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU
        (finStepBranch (c := c_f) (some ⟨Λ'.clear p k q, hmem⟩) (v, S)) s).length : ℤ)
      ≤ ((indexedStackU ((some ⟨Λ'.clear p k q, hmem⟩, v, S) : UConf) s).length : ℤ) + 1 := by
  exact (stackStepRel_indexed_finStepBranch _ v S s).length_le

theorem step_copy_stack_growth_le_one
    (q : Λ') (hmem : Λ'.copy q ∈ supportSet c_f)
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU
        (finStepBranch (c := c_f) (some ⟨Λ'.copy q, hmem⟩) (v, S)) s).length : ℤ)
      ≤ ((indexedStackU ((some ⟨Λ'.copy q, hmem⟩, v, S) : UConf) s).length : ℤ) + 1 := by
  exact (stackStepRel_indexed_finStepBranch _ v S s).length_le

theorem step_push_stack_growth_le_one
    (k : K') (f : Option Γ' → Option Γ') (q : Λ')
    (hmem : Λ'.push k f q ∈ supportSet c_f)
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU
        (finStepBranch (c := c_f) (some ⟨Λ'.push k f q, hmem⟩) (v, S)) s).length : ℤ)
      ≤ ((indexedStackU ((some ⟨Λ'.push k f q, hmem⟩, v, S) : UConf) s).length : ℤ) + 1 := by
  exact (stackStepRel_indexed_finStepBranch _ v S s).length_le

theorem step_read_stack_growth_le_one
    (q : Option Γ' → Λ') (hmem : Λ'.read q ∈ supportSet c_f)
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU
        (finStepBranch (c := c_f) (some ⟨Λ'.read q, hmem⟩) (v, S)) s).length : ℤ)
      ≤ ((indexedStackU ((some ⟨Λ'.read q, hmem⟩, v, S) : UConf) s).length : ℤ) + 1 := by
  exact (stackStepRel_indexed_finStepBranch _ v S s).length_le

theorem step_succ_stack_growth_le_one
    (q : Λ') (hmem : Λ'.succ q ∈ supportSet c_f)
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU
        (finStepBranch (c := c_f) (some ⟨Λ'.succ q, hmem⟩) (v, S)) s).length : ℤ)
      ≤ ((indexedStackU ((some ⟨Λ'.succ q, hmem⟩, v, S) : UConf) s).length : ℤ) + 1 := by
  exact (stackStepRel_indexed_finStepBranch _ v S s).length_le

theorem step_pred_stack_growth_le_one
    (q₁ q₂ : Λ') (hmem : Λ'.pred q₁ q₂ ∈ supportSet c_f)
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU
        (finStepBranch (c := c_f) (some ⟨Λ'.pred q₁ q₂, hmem⟩) (v, S)) s).length : ℤ)
      ≤ ((indexedStackU ((some ⟨Λ'.pred q₁ q₂, hmem⟩, v, S) : UConf) s).length : ℤ) + 1 := by
  exact (stackStepRel_indexed_finStepBranch _ v S s).length_le

theorem step_ret_stack_growth_le_one
    (k : Cont') (hmem : Λ'.ret k ∈ supportSet c_f)
    (v : Option Γ') (S : StackTuple) (s : Fin 4) :
    ((indexedStackU
        (finStepBranch (c := c_f) (some ⟨Λ'.ret k, hmem⟩) (v, S)) s).length : ℤ)
      ≤ ((indexedStackU ((some ⟨Λ'.ret k, hmem⟩, v, S) : UConf) s).length : ℤ) + 1 := by
  exact (stackStepRel_indexed_finStepBranch _ v S s).length_le

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
