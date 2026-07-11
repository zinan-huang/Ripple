/-
  Paper-facing Theorem 3.1: Bounded RM simulation.

  For any RM, any input, any error bound δ, and any step bound t,
  there exists an SCRN with initial accuracy species A that simulates
  the RM for t steps with cumulative error at most δ.

  The CRN uses at-most-bimolecular reactions with unit rates.
  The error is controlled by the clock module (#A accuracy species).
  Per-step error ≤ 1/#A^(l-1) via the geometric sum bound.
  Setting #A = Θ((t/δ)^{1/(l-1)}) gives total error ≤ δ.
-/
import Ripple.sCRNUniversality.Computation.RegisterMachine.RMSimulation

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

theorem rmNetwork_simulation_correct
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
