/-
  Register-machine network of Soloveichik, Cook, Winfree and Bruck (2008), §3:
  one-instruction facts.

  `rmNetwork prog` has, for each instruction, the reactions of the paper's
  register-machine construction without the clock module (the paper's "first
  attempt", Fig. 3.1A): one species `catalyst` plays both the dummy catalyst C
  of increments and, in place of the clock output C₁, the catalyst of the zero
  branch.  Reactions: `rxnInc` for an
  increment, and `rxnDec1` (decrement a nonzero register) and `rxnDec2` (the
  jump taken when the register is read as zero) for a decrement.  This file
  proves:

  * `rmNetwork_reaches_successor`: the intended successor of one instruction
    is reachable;
  * `rm_error_source_characterization`: when the register is nonzero both
    decrement reactions are enabled, so the wrong jump `rxnDec2` can fire
    (the error source that the paper's clock module suppresses);
  * `rm_correct_when_zero`: when the register is zero only `rxnDec2` is
    enabled.

  The paper's Theorem 3.1 (for every RM, error probability at most δ over t
  steps, with the accuracy species A of the clock module and expected time
  O(v t^2 / (k δ))) is not formalized: `rmNetwork` has no clock module, no
  accuracy species and no probability.  See `OPEN_PROBLEMS.md` §6.2.
-/
import Ripple.sCRNUniversality.RegisterMachine.RMSimulation

namespace Ripple.sCRNUniversality.RegisterMachine

universe u v

variable {Q : Type u} [Fintype Q] [DecidableEq Q]
         {R : Type v} [Fintype R] [DecidableEq R]

-- Unit rate and bimolecularity are structural properties of the reactions
-- (rxnInc, rxnDec1, rxnDec2 all have k=1 and inputArity ≤ 2)

theorem rxnInc_unitRate (instr : IncInstruction Q R) :
    (rxnInc instr).unitRate := rfl

theorem rxnDec1_unitRate (instr : DecInstruction Q R) :
    (rxnDec1 instr).unitRate := rfl

theorem rxnDec2_unitRate (instr : DecInstruction Q R) :
    (rxnDec2 instr).unitRate := rfl

theorem rmNetwork_reaches_successor
    (prog : RMProgram Q R)
    (idx : Fin prog.length)
    (regs : R → Nat) :
    match prog.get idx with
    | .inc instr =>
        instr.source ≠ instr.target →
        (rmNetwork prog).Reaches
          (encodeRM instr.source regs)
          (encodeRM instr.target
            (Function.update regs instr.register (regs instr.register + 1)))
    | .dec instr =>
        (0 < regs instr.register →
          instr.source ≠ instr.target_nonzero →
          (rmNetwork prog).Reaches
            (encodeRM instr.source regs)
            (encodeRM instr.target_nonzero
              (Function.update regs instr.register (regs instr.register - 1)))) ∧
        (regs instr.register = 0 →
          instr.source ≠ instr.target_zero →
          (rmNetwork prog).Reaches
            (encodeRM instr.source regs)
            (encodeRM instr.target_zero regs)) := by
  cases h : prog.get idx with
  | inc instr =>
    intro hne
    exact rmNetwork_inc_simulation prog idx instr h regs hne
  | dec instr =>
    exact ⟨fun hr hne => rmNetwork_dec_nonzero_simulation prog idx instr h regs hr hne,
           fun hr hne => rmNetwork_dec_zero_simulation prog idx instr h regs hr hne⟩

theorem rm_error_source_characterization
    (instr : DecInstruction Q R) (regs : R → Nat)
    (hr : 0 < regs instr.register) :
    (rxnDec1 instr).enabled (encodeRM instr.source regs) ∧
    (rxnDec2 instr).enabled (encodeRM instr.source regs) :=
  both_enabled_when_register_nonzero instr regs hr

theorem rm_correct_when_zero
    (instr : DecInstruction Q R) (regs : R → Nat)
    (hr : regs instr.register = 0) :
    (rxnDec2 instr).enabled (encodeRM instr.source regs) ∧
    ¬(rxnDec1 instr).enabled (encodeRM instr.source regs) :=
  only_dec2_when_zero instr regs hr

end Ripple.sCRNUniversality.RegisterMachine
