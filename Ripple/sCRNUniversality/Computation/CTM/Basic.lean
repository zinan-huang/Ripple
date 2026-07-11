import Mathlib.Data.Vector.Basic
import Mathlib.Tactic
import Ripple.sCRNUniversality.Computation.DetSystem

namespace Ripple.sCRNUniversality

namespace CTM

structure Machine (Q : Type u) (Gamma : Type v) where
  start : Q
  delta : Q -> Gamma -> Option (Gamma × Q)

structure Cfg (Q : Type u) (Gamma : Type v) (s : Nat) where
  state : Q
  tape : List.Vector Gamma (s + 1)

namespace Machine

def rotateWrite {Gamma : Type v} {s : Nat}
    (t : List.Vector Gamma (s + 1)) (a : Gamma) : List.Vector Gamma (s + 1) :=
  ⟨t.toList.tail ++ [a], by
    have hlen : t.toList.length = s + 1 := t.2
    rw [List.length_append, List.length_tail, List.length_singleton, hlen]
    omega⟩

def step? {Q : Type u} {Gamma : Type v} {s : Nat} (M : Machine Q Gamma) :
    Cfg Q Gamma s -> Option (Cfg Q Gamma s)
  | c =>
      match M.delta c.state c.tape.head with
      | none => none
      | some (a, q') =>
          some { state := q', tape := rotateWrite c.tape a }

def detSystem {Q : Type u} {Gamma : Type v} {s : Nat}
    (M : Machine Q Gamma) : DetSystem where
  Cfg := Cfg Q Gamma s
  step? := M.step?

end Machine

abbrev Binary (Q : Type u) := Machine Q Bool

end CTM

end Ripple.sCRNUniversality
