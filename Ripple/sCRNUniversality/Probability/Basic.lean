import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic

namespace Ripple.sCRNUniversality

namespace Probability

abbrev Event (Omega : Type u) := Set Omega

def ErrorEvent {Omega : Type u} (success : Omega -> Prop) : Event Omega :=
  {omega | Not (success omega)}

def finUnion {Omega : Type u} {I : Type v}
    (s : Finset I) (E : I -> Event Omega) : Event Omega :=
  {omega | exists i, i ∈ s /\ omega ∈ E i}

def countUnion {Omega : Type u}
    (E : Nat -> Event Omega) : Event Omega :=
  {omega | exists n, omega ∈ E n}

structure ProbSpec (Omega : Type u) where
  Pr : Event Omega -> ENNReal

structure ProbAxioms.{u, v} {Omega : Type u} (P : ProbSpec Omega) : Prop where
  monotone :
    forall {E F : Event Omega}, E ⊆ F -> P.Pr E <= P.Pr F
  union_le_add :
    forall (E F : Event Omega), P.Pr (E ∪ F) <= P.Pr E + P.Pr F
  finUnion_le_sum :
    forall {I : Type v} (s : Finset I) (E : I -> Event Omega),
      P.Pr (finUnion s E) <= s.sum (fun i => P.Pr (E i))
  countUnion_le_of_prefixBounds :
    forall (E : Nat -> Event Omega) (err : Nat -> ENNReal) (epsilon : ENNReal),
      (forall n, P.Pr (E n) <= err n) ->
      (forall N, (Finset.range N).sum err <= epsilon) ->
      P.Pr (countUnion E) <= epsilon

end Probability

end Ripple.sCRNUniversality
