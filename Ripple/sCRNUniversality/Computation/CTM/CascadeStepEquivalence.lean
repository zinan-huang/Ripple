/-
  Cascade step equivalence: the cascade shift produces the same tape
  transformation as the finite-table shift (shiftTail T = 3 * T).

  Combined with the existing read/erase/write proofs, this shows that
  replacing the finite-table shift with the cascade shift preserves
  the correctness of CTM step simulation.
-/
import Ripple.sCRNUniversality.Computation.Encoding.Base3Tape
import Ripple.sCRNUniversality.Computation.CTM.FourPhaseSystem

namespace Ripple.sCRNUniversality.CTM.CascadeStepEquivalence

theorem shiftTail_eq_mul3 (T : Nat) : Encoding.shiftTail T = 3 * T := rfl

theorem ctm_step_tape_decomposition
    {s : Nat} (tape : Nat) (w : Bool) :
    Encoding.rotateWriteVal s tape w =
      Encoding.writeLSB (3 * Encoding.eraseMSB s tape) w := by
  simp [Encoding.rotateWriteVal, Encoding.shiftTail]

theorem rotateWriteVal_eq {s : Nat} (tape : Nat) (w : Bool) :
    Encoding.rotateWriteVal s tape w =
      Encoding.writeLSB (Encoding.shiftTail (Encoding.eraseMSB s tape)) w := rfl

theorem cascade_shift_value_eq_shiftTail (T : Nat) :
    3 * T = Encoding.shiftTail T := rfl

theorem phaseStep_read_preserves_tape {Q : Type*} {s : Nat} (M : Binary Q)
    (cfg : MicroCfg Q s) (cfg' : MicroCfg Q s)
    (hphase : cfg.state.phase = Phase4.read)
    (hstep : phaseStep? (s := s) M cfg = some cfg') :
    cfg'.tape = cfg.tape := by
  simp [phaseStep?, hphase] at hstep
  split at hstep
  · cases hstep
  · rename_i w q' hδ
    injection hstep with hstep
    simp [← hstep]

theorem phaseStep_shift_triples_tape {Q : Type*} {s : Nat} (M : Binary Q)
    (cfg : MicroCfg Q s) (cfg' : MicroCfg Q s)
    (hphase : cfg.state.phase = Phase4.shift)
    (hstep : phaseStep? (s := s) M cfg = some cfg') :
    cfg'.tape = Encoding.shiftTail cfg.tape := by
  simp [phaseStep?, hphase] at hstep
  rw [← hstep]

theorem phaseStep_shift_triples_tape' {Q : Type*} {s : Nat} (M : Binary Q)
    (cfg : MicroCfg Q s) (cfg' : MicroCfg Q s)
    (hphase : cfg.state.phase = Phase4.shift)
    (hstep : phaseStep? (s := s) M cfg = some cfg') :
    cfg'.tape = 3 * cfg.tape := by
  rw [phaseStep_shift_triples_tape M cfg cfg' hphase hstep, shiftTail_eq_mul3]

end Ripple.sCRNUniversality.CTM.CascadeStepEquivalence
