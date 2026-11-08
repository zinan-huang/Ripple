namespace Ripple.sCRNUniversality

structure DetSystem where
  Cfg : Type u
  step? : Cfg -> Option Cfg

namespace DetSystem

def halts (A : DetSystem) (c : A.Cfg) : Prop :=
  A.step? c = none

def iter {Sigma : Type u} (step? : Sigma -> Option Sigma) : Nat -> Sigma -> Option Sigma
  | 0, c => some c
  | n + 1, c =>
      match step? c with
      | none => none
      | some c' => iter step? n c'

def steps? (A : DetSystem) (n : Nat) (c : A.Cfg) : Option A.Cfg :=
  iter A.step? n c

@[simp]
theorem steps_zero (A : DetSystem) (c : A.Cfg) :
    A.steps? 0 c = some c := rfl

theorem steps?_append (A : DetSystem) {n m : Nat} {x y z : A.Cfg}
    (h₁ : A.steps? n x = some y)
    (h₂ : A.steps? m y = some z) :
    A.steps? (n + m) x = some z := by
  revert x
  induction n with
  | zero =>
      intro x h₁
      simp [steps?] at h₁
      cases h₁
      simpa [steps?] using h₂
  | succ n ih =>
      intro x h₁
      cases hstep : A.step? x with
      | none =>
          simp [steps?, iter, hstep] at h₁
      | some x₁ =>
          have htail : A.steps? n x₁ = some y := by
            simpa [steps?, iter, hstep] using h₁
          simpa [steps?, iter, hstep, Nat.succ_add] using ih htail

theorem steps?_one_of_step? (A : DetSystem) {x y : A.Cfg}
    (h : A.step? x = some y) :
    A.steps? 1 x = some y := by
  simp [steps?, iter, h]

end DetSystem

end Ripple.sCRNUniversality
