import Ripple.sCRNUniversality.Core.Finite
import Ripple.sCRNUniversality.Core.Run

open scoped BigOperators

namespace Ripple.sCRNUniversality

namespace State

def lin {S : Type u} [Fintype S] (w : S -> Int) (z : State S) : Int :=
  Finset.univ.sum (fun s => w s * (z s : Int))

end State

namespace Complex

def lin {S : Type u} [Fintype S] (w : S -> Int) (c : Complex S) : Int :=
  Finset.univ.sum (fun s => w s * (c s : Int))

end Complex

namespace Reaction

variable {S : Type u} [Fintype S]

def Balances (rho : Reaction S) (w : S -> Int) : Prop :=
  Complex.lin w rho.l = Complex.lin w rho.r

def PreservesLin (rho : Reaction S) (w : S -> Int) : Prop :=
  forall {z z' : State S}, rho.FiresTo z z' -> State.lin w z' = State.lin w z

theorem FiresTo.lin_eq_of_weight_zero_on_touches
    {rho : Reaction S} {w : S -> Int} {z z' : State S}
    (hFire : rho.FiresTo z z')
    (hw : forall s, rho.Touches s -> w s = 0) :
    State.lin w z' = State.lin w z := by
  unfold State.lin
  refine Finset.sum_congr rfl ?_
  intro s _hs
  by_cases ht : rho.Touches s
  · simp [hw s ht]
  · have hcoord : z' s = z s := hFire.eq_on_not_touches ht
    simp [hcoord]

theorem PreservesLin.of_weight_zero_on_touches
    {rho : Reaction S} {w : S -> Int}
    (hw : forall s, rho.Touches s -> w s = 0) :
    rho.PreservesLin w := by
  intro _z _z' hFire
  exact hFire.lin_eq_of_weight_zero_on_touches hw

end Reaction

namespace Network

variable {S : Type u} [Fintype S]

def Balances (N : Network S) (w : S -> Int) : Prop :=
  forall i : N.I, (N.rxn i).Balances w

def PreservesLin (N : Network S) (w : S -> Int) : Prop :=
  forall i : N.I, (N.rxn i).PreservesLin w

def WeightZeroOnTouches (N : Network S) (w : S -> Int) : Prop :=
  forall i : N.I, forall s : S, (N.rxn i).Touches s -> w s = 0

namespace StepAt

theorem lin_eq_of_preservesLin
    {N : Network S} {w : S -> Int}
    (hN : N.PreservesLin w)
    {i : N.I} {z z' : State S}
    (hStep : N.StepAt i z z') :
    State.lin w z' = State.lin w z :=
  hN i hStep

end StepAt

namespace Exec

theorem lin_eq_of_preservesLin
    {N : Network S} {w : S -> Int}
    (hN : N.PreservesLin w)
    {z z' : State S} {is : List N.I}
    (hExec : N.Exec z z' is) :
    State.lin w z' = State.lin w z := by
  induction hExec with
  | nil _ =>
      rfl
  | cons hStep _tail ih =>
      exact ih.trans (StepAt.lin_eq_of_preservesLin hN hStep)

end Exec

namespace Reaches

theorem lin_eq_of_preservesLin
    {N : Network S} {w : S -> Int}
    (hN : N.PreservesLin w)
    {z z' : State S}
    (hReach : N.Reaches z z') :
    State.lin w z' = State.lin w z := by
  rcases hReach with ⟨is, hExec⟩
  exact Exec.lin_eq_of_preservesLin hN hExec

end Reaches

theorem preservesLin_of_weightZeroOnTouches
    {N : Network S} {w : S -> Int}
    (h : N.WeightZeroOnTouches w) :
    N.PreservesLin w := by
  intro i
  exact Reaction.PreservesLin.of_weight_zero_on_touches (rho := N.rxn i) (h i)

theorem parallel_preservesLin_iff
    (N M : Network S) (w : S -> Int) :
    (N.parallel M).PreservesLin w <->
      N.PreservesLin w /\ M.PreservesLin w := by
  constructor
  · intro h
    constructor
    · intro i
      exact h (Sum.inl i)
    · intro i
      exact h (Sum.inr i)
  · rintro ⟨hN, hM⟩ i
    cases i with
    | inl i =>
        exact hN i
    | inr i =>
        exact hM i

theorem parallel_balances_iff
    (N M : Network S) (w : S -> Int) :
    (N.parallel M).Balances w <->
      N.Balances w /\ M.Balances w := by
  constructor
  · intro h
    constructor
    · intro i
      exact h (Sum.inl i)
    · intro i
      exact h (Sum.inr i)
  · rintro ⟨hN, hM⟩ i
    cases i with
    | inl i =>
        exact hN i
    | inr i =>
        exact hM i

end Network

end Ripple.sCRNUniversality
