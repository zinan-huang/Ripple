/-
  Tape arithmetic of one CTM phase step: `shiftTail T = 3 * T`, the write after
  erase-and-shift as `writeLSB (3 * eraseMSB s tape) w`, and the read phase leaving
  the tape unchanged.

  These are unfoldings of the definitions in `Encoding.Base3Tape`. The cascade
  shift network itself is `CTM.CascadeShift.cascade_effect`; no theorem here
  connects it to `phaseStep?` or to the CTM step simulation.
-/
import Ripple.sCRNUniversality.Encoding.Base3Tape
import Ripple.sCRNUniversality.CTM.FourPhaseSystem

namespace Ripple.sCRNUniversality.CTM.PhaseStepTape

theorem shiftTail_eq_three_mul (T : Nat) : Encoding.shiftTail T = 3 * T := rfl

theorem rotateWriteVal_eq_writeLSB_three_mul_eraseMSB
    {s : Nat} (tape : Nat) (w : Bool) :
    Encoding.rotateWriteVal s tape w =
      Encoding.writeLSB (3 * Encoding.eraseMSB s tape) w := by
  simp [Encoding.rotateWriteVal, Encoding.shiftTail]

theorem rotateWriteVal_eq {s : Nat} (tape : Nat) (w : Bool) :
    Encoding.rotateWriteVal s tape w =
      Encoding.writeLSB (Encoding.shiftTail (Encoding.eraseMSB s tape)) w := rfl

theorem three_mul_eq_shiftTail (T : Nat) :
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

theorem phaseStep_shift_tape_eq_three_mul {Q : Type*} {s : Nat} (M : Binary Q)
    (cfg : MicroCfg Q s) (cfg' : MicroCfg Q s)
    (hphase : cfg.state.phase = Phase4.shift)
    (hstep : phaseStep? (s := s) M cfg = some cfg') :
    cfg'.tape = 3 * cfg.tape := by
  rw [phaseStep_shift_triples_tape M cfg cfg' hphase hstep, shiftTail_eq_three_mul]

end Ripple.sCRNUniversality.CTM.PhaseStepTape
