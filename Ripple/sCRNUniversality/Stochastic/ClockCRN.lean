/-
  Clock module CRN from SCWB 2008 (Fig 3.1B, Appendix A.1).

  A random walk on states {C_0, ..., C_{l-1}} catalysed by A (forward)
  and A* (backward):
    Forward:  C_i + A  → C_{i+1} + A    (i = 0 .. l-2)
    Backward: C_{i+1} + A* → C_i + A*   (i = 0 .. l-2)

  "Tick" = C_0 present, which triggers state-transition initiation.
  The ratio #A / #A* controls clock speed.

  Properties proved:
  • All reactions are unit-rate.
  • Catalysts A and A* are preserved by every reaction.
  • Total C-molecule count is preserved by every reaction.
-/
import Ripple.sCRNUniversality.Core.Run
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace Ripple.sCRNUniversality.Stochastic.ClockCRN

/-- Species of the clock module: l clock states plus two catalysts. -/
inductive Sp (l : Nat) where
  | C : Fin l → Sp l
  | A : Sp l
  | Astar : Sp l
  deriving DecidableEq, Repr

/-- Clock reaction index: forward i or backward i, for i : Fin (l - 1). -/
inductive Ix (l : Nat) where
  | fwd : Fin (l - 1) → Ix l
  | bwd : Fin (l - 1) → Ix l
  deriving DecidableEq, Repr

section FintypeInstances

private def Sp.equiv (l : Nat) : Sum (Fin l) Bool ≃ Sp l where
  toFun
    | Sum.inl i => Sp.C i
    | Sum.inr false => Sp.A
    | Sum.inr true => Sp.Astar
  invFun
    | Sp.C i => Sum.inl i
    | Sp.A => Sum.inr false
    | Sp.Astar => Sum.inr true
  left_inv x := by cases x with | inl i => rfl | inr b => cases b <;> rfl
  right_inv x := by cases x with | C i => rfl | A => rfl | Astar => rfl

instance : Fintype (Sp l) :=
  Fintype.ofEquiv _ (Sp.equiv l)

private def Ix.equiv (l : Nat) : Sum (Fin (l - 1)) (Fin (l - 1)) ≃ Ix l where
  toFun
    | Sum.inl i => Ix.fwd i
    | Sum.inr i => Ix.bwd i
  invFun
    | Ix.fwd i => Sum.inl i
    | Ix.bwd i => Sum.inr i
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

instance : Fintype (Ix l) :=
  Fintype.ofEquiv _ (Ix.equiv l)

end FintypeInstances

variable {l : Nat}

/-- Lift Fin index i (in Fin (l-1)) to Fin l. -/
private def liftFin (i : Fin (l - 1)) : Fin l :=
  ⟨i.val, by omega⟩

/-- Successor of Fin index i (in Fin (l-1)) as Fin l. -/
private def succFin (i : Fin (l - 1)) : Fin l :=
  ⟨i.val + 1, by omega⟩

private theorem liftFin_ne_succFin (i : Fin (l - 1)) : liftFin i ≠ succFin i := by
  intro h
  have := congr_arg Fin.val h
  simp [liftFin, succFin] at this

private theorem succFin_ne_liftFin (i : Fin (l - 1)) : succFin i ≠ liftFin i :=
  (liftFin_ne_succFin i).symm

/-- Forward reaction i: C_i + A → C_{i+1} + A. -/
def rxnFwd (i : Fin (l - 1)) : Reaction (Sp l) :=
  { l := fun | .C j => if j = liftFin i then 1 else 0
              | .A => 1 | .Astar => 0,
    r := fun | .C j => if j = succFin i then 1 else 0
              | .A => 1 | .Astar => 0,
    k := 1 }

/-- Backward reaction i: C_{i+1} + A* → C_i + A*. -/
def rxnBwd (i : Fin (l - 1)) : Reaction (Sp l) :=
  { l := fun | .C j => if j = succFin i then 1 else 0
              | .A => 0 | .Astar => 1,
    r := fun | .C j => if j = liftFin i then 1 else 0
              | .A => 0 | .Astar => 1,
    k := 1 }

/-- The clock CRN with 2(l-1) reactions. -/
def net : Network (Sp l) where
  I := Ix l
  fintypeI := inferInstance
  rxn | .fwd i => rxnFwd i | .bwd i => rxnBwd i

/-! ### Unit rate -/

theorem allUnitRate : (net (l := l)).allUnitRate := by
  intro i; cases i with
  | fwd _ => exact rfl
  | bwd _ => exact rfl

/-! ### Catalyst preservation -/

/-- Catalyst A is preserved by every reaction. -/
theorem catalyst_A_preserved {i : (net (l := l)).I} {z z' : State (Sp l)}
    (hStep : net.StepAt i z z') : z' .A = z .A := by
  have hfire := hStep.eq_fire
  cases i with
  | fwd j =>
    have := hStep.enabled (.A)
    simp only [net, rxnFwd] at this
    rw [hfire]; simp only [Reaction.fire, net, rxnFwd]; omega
  | bwd j =>
    rw [hfire]; simp only [Reaction.fire, net, rxnBwd]; omega

/-- Catalyst A* is preserved by every reaction. -/
theorem catalyst_Astar_preserved {i : (net (l := l)).I} {z z' : State (Sp l)}
    (hStep : net.StepAt i z z') : z' .Astar = z .Astar := by
  have hfire := hStep.eq_fire
  cases i with
  | fwd j =>
    rw [hfire]; simp only [Reaction.fire, net, rxnFwd]; omega
  | bwd j =>
    have := hStep.enabled (.Astar)
    simp only [net, rxnBwd] at this
    rw [hfire]; simp only [Reaction.fire, net, rxnBwd]; omega

/-! ### Total C-molecule count preservation -/

/-- The total count of all C-species in a state. -/
def totalC (z : State (Sp l)) : Nat :=
  ∑ j : Fin l, z (.C j)

/-- Helper: for swap-pair sums. If f' agrees with f except at two points a, b
    where f'(a) = f(a) - 1 and f'(b) = f(b) + 1, and 1 ≤ f(a),
    then the sums are equal. -/
private theorem sum_swap_pair {n : Nat} {f f' : Fin n → Nat}
    {a b : Fin n} (hab : a ≠ b)
    (ha : f' a = f a - 1) (hb : f' b = f b + 1)
    (hother : ∀ j, j ≠ a → j ≠ b → f' j = f j)
    (hge : 1 ≤ f a) :
    ∑ j : Fin n, f' j = ∑ j : Fin n, f j := by
  have hmem_a : a ∈ Finset.univ := Finset.mem_univ a
  have hmem_b : b ∈ (Finset.univ.erase a) :=
    Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩
  calc ∑ j : Fin n, f' j
      = f' a + ∑ j ∈ Finset.univ.erase a, f' j :=
        (Finset.add_sum_erase _ _ hmem_a).symm
    _ = f' a + (f' b + ∑ j ∈ (Finset.univ.erase a).erase b, f' j) := by
        congr 1; exact (Finset.add_sum_erase _ _ hmem_b).symm
    _ = (f a - 1) + ((f b + 1) + ∑ j ∈ (Finset.univ.erase a).erase b, f j) := by
        rw [ha, hb]
        congr 1; congr 1
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Finset.mem_erase] at hj
        exact hother j hj.2.1 hj.1
    _ = f a + (f b + ∑ j ∈ (Finset.univ.erase a).erase b, f j) := by omega
    _ = f a + ∑ j ∈ Finset.univ.erase a, f j := by
        congr 1; exact Finset.add_sum_erase _ _ hmem_b
    _ = ∑ j : Fin n, f j :=
        Finset.add_sum_erase _ _ hmem_a

/-- Forward reaction preserves totalC. -/
private theorem fwd_totalC (i : Fin (l - 1)) {z z' : State (Sp l)}
    (hStep : net.StepAt (.fwd i) z z') :
    totalC z' = totalC z := by
  have hfire := hStep.eq_fire
  have hle : 1 ≤ z (.C (liftFin i)) := by
    have := hStep.enabled (.C (liftFin i))
    simp [net, rxnFwd] at this; exact this
  unfold totalC
  rw [hfire]
  show ∑ j, (rxnFwd i).fire z (.C j) = _
  apply sum_swap_pair (liftFin_ne_succFin i)
  · simp [Reaction.fire, rxnFwd, liftFin_ne_succFin]
  · simp [Reaction.fire, rxnFwd, succFin_ne_liftFin]
  · intro j hj1 hj2
    simp [Reaction.fire, rxnFwd, hj1, hj2]
  · exact hle

/-- Backward reaction preserves totalC. -/
private theorem bwd_totalC (i : Fin (l - 1)) {z z' : State (Sp l)}
    (hStep : net.StepAt (.bwd i) z z') :
    totalC z' = totalC z := by
  have hfire := hStep.eq_fire
  have hle : 1 ≤ z (.C (succFin i)) := by
    have := hStep.enabled (.C (succFin i))
    simp [net, rxnBwd] at this; exact this
  unfold totalC
  rw [hfire]
  show ∑ j, (rxnBwd i).fire z (.C j) = _
  apply sum_swap_pair (succFin_ne_liftFin i)
  · simp [Reaction.fire, rxnBwd, succFin_ne_liftFin]
  · simp [Reaction.fire, rxnBwd, liftFin_ne_succFin]
  · intro j hj1 hj2
    simp [Reaction.fire, rxnBwd, hj1, hj2]
  · exact hle

/-- The total C-molecule count is a step invariant of the clock network. -/
theorem totalC_stepInvariant :
    (net (l := l)).StepInvariant (fun z => totalC z = n) := by
  intro i z z' hStep hP
  cases i with
  | fwd j => rw [fwd_totalC j hStep, hP]
  | bwd j => rw [bwd_totalC j hStep, hP]

/-- The total C-molecule count is preserved along any execution. -/
theorem totalC_exec_preserved {z z' : State (Sp l)} {is : List (net (l := l)).I}
    (hExec : net.Exec z z' is) :
    totalC z' = totalC z :=
  Network.StepInvariant.exec (totalC_stepInvariant (n := totalC z)) hExec rfl

/-- The total C-molecule count is preserved along any reachable sequence. -/
theorem totalC_reaches_preserved {z z' : State (Sp l)}
    (hReach : net.Reaches z z') :
    totalC z' = totalC z :=
  Network.StepInvariant.reaches (totalC_stepInvariant (n := totalC z)) hReach rfl

end Ripple.sCRNUniversality.Stochastic.ClockCRN
