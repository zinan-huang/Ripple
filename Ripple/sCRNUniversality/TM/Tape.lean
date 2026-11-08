namespace Ripple.sCRNUniversality

namespace TM

inductive Move where
  | L
  | R
deriving DecidableEq, Repr

structure Tape (Gamma : Type u) where
  left : List Gamma
  head : Gamma
  right : List Gamma
deriving Repr

namespace Tape

variable {Gamma : Type u}

def read (t : Tape Gamma) : Gamma :=
  t.head

def write (a : Gamma) (t : Tape Gamma) : Tape Gamma :=
  { t with head := a }

def move (blank : Gamma) : Move -> Tape Gamma -> Tape Gamma
  | Move.L, t =>
      match t.left with
      | [] => { left := [], head := blank, right := t.head :: t.right }
      | a :: rest => { left := rest, head := a, right := t.head :: t.right }
  | Move.R, t =>
      match t.right with
      | [] => { left := t.head :: t.left, head := blank, right := [] }
      | a :: rest => { left := t.head :: t.left, head := a, right := rest }

end Tape

end TM

end Ripple.sCRNUniversality
