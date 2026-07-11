import Ripple.sCRNUniversality.Computation.DetSystem
import Ripple.sCRNUniversality.Computation.TM.Tape

namespace Ripple.sCRNUniversality

namespace TM

structure Machine (Q : Type u) (Gamma : Type v) where
  start : Q
  blank : Gamma
  delta : Q -> Gamma -> Option (Gamma × Move × Q)

structure Cfg (Q : Type u) (Gamma : Type v) where
  state : Q
  tape : Tape Gamma
deriving Repr

namespace Machine

def step? {Q : Type u} {Gamma : Type v} (M : Machine Q Gamma) :
    Cfg Q Gamma -> Option (Cfg Q Gamma)
  | c =>
      match M.delta c.state c.tape.read with
      | none => none
      | some (a, d, q') =>
          let tape' := (c.tape.write a).move M.blank d
          some { state := q', tape := tape' }

def detSystem {Q : Type u} {Gamma : Type v} (M : Machine Q Gamma) : DetSystem where
  Cfg := Cfg Q Gamma
  step? := M.step?

def NoWriteBlank {Q : Type u} {Gamma : Type v} (M : Machine Q Gamma) : Prop :=
  forall q a a' d q', M.delta q a = some (a', d, q') -> a' ≠ M.blank

end Machine

end TM

end Ripple.sCRNUniversality
