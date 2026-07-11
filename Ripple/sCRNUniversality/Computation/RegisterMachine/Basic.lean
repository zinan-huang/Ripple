import Ripple.sCRNUniversality.Computation.DetSystem

namespace Ripple.sCRNUniversality

namespace RegisterMachine

inductive Instr (Reg Label : Type u) where
  | inc : Reg -> Label -> Instr Reg Label
  | decJz : Reg -> Label -> Label -> Instr Reg Label
  | halt : Instr Reg Label

structure RM (Reg Label : Type u) where
  start : Label
  code : Label -> Instr Reg Label

structure Cfg (Reg Label : Type u) where
  pc : Label
  reg : Reg -> Nat

namespace Cfg

def updateReg {Reg Label : Type u} [DecidableEq Reg]
    (c : Cfg Reg Label) (r : Reg) (value : Nat) : Cfg Reg Label :=
  { c with reg := fun r' => if r' = r then value else c.reg r' }

end Cfg

namespace RM

variable {Reg Label : Type u} [DecidableEq Reg]

def step? (M : RM Reg Label) (c : Cfg Reg Label) : Option (Cfg Reg Label) :=
  match M.code c.pc with
  | Instr.inc r next =>
      some { pc := next, reg := fun r' => if r' = r then c.reg r' + 1 else c.reg r' }
  | Instr.decJz r nonzero zero =>
      if c.reg r = 0 then
        some { c with pc := zero }
      else
        some { pc := nonzero, reg := fun r' => if r' = r then c.reg r - 1 else c.reg r' }
  | Instr.halt => none

def detSystem (M : RM Reg Label) : DetSystem where
  Cfg := Cfg Reg Label
  step? := M.step?

end RM

end RegisterMachine

end Ripple.sCRNUniversality
