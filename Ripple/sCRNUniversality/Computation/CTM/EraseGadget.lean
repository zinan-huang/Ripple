import Ripple.sCRNUniversality.Computation.CTM.GadgetArithmetic
import Ripple.sCRNUniversality.Core.OneReaction

namespace Ripple.sCRNUniversality

namespace CTM

namespace EraseGadget

universe u

variable {Q : Type u} [DecidableEq Q]

def eraseMass (s : Nat) (r : Bool) : Nat :=
  Encoding.bitDigit r * 3 ^ s

def sourceState (q : Q) (r w : Bool) (qNext : Q) : MicroState Q :=
  MicroState.afterRead (MicroState.readPhase q) r w qNext

def targetState (q : Q) (r w : Bool) (qNext : Q) : MicroState Q :=
  MicroState.afterErase (sourceState q r w qNext)

def sourceCfg {s : Nat} (q : Q) (r w : Bool) (qNext : Q)
    (tape : Nat) : MicroCfg Q s :=
  { state := sourceState q r w qNext, tape := tape }

def targetCfg {s : Nat} (q : Q) (r w : Bool) (qNext : Q)
    (tape : Nat) : MicroCfg Q s :=
  { state := targetState q r w qNext,
    tape := Encoding.eraseMSBWith s r tape }

def input {s : Nat} (q : Q) (r w : Bool) (qNext : Q) :
    Complex (FourPhaseSpecies Q) :=
  State.add
    (State.single (FourPhaseSpecies.ctrlOf (sourceState q r w qNext)) 1)
    (State.single FourPhaseSpecies.tape (eraseMass s r))

def output {s : Nat} (q : Q) (r w : Bool) (qNext : Q) :
    Complex (FourPhaseSpecies Q) :=
  State.add
    (State.single (FourPhaseSpecies.ctrlOf (targetState q r w qNext)) 1)
    (State.single FourPhaseSpecies.tapeBar (eraseMass s r))

def reaction {s : Nat} (q : Q) (r w : Bool) (qNext : Q) :
    Reaction (FourPhaseSpecies Q) where
  l := input (s := s) q r w qNext
  r := output (s := s) q r w qNext
  k := 1

@[simp]
theorem reaction_inputArity [Fintype Q] {s : Nat}
    (q : Q) (r w : Bool) (qNext : Q) :
    (reaction (s := s) q r w qNext).inputArity =
      1 + eraseMass s r := by
  simp [Reaction.inputArity, reaction, input]

@[simp]
theorem reaction_outputArity [Fintype Q] {s : Nat}
    (q : Q) (r w : Bool) (qNext : Q) :
    (reaction (s := s) q r w qNext).outputArity =
      1 + eraseMass s r := by
  simp [Reaction.outputArity, reaction, output]

def network {s : Nat} (q : Q) (r w : Bool) (qNext : Q) :
    Network (FourPhaseSpecies Q) :=
  Network.oneRxnNetwork (reaction (s := s) q r w qNext)

theorem reaction_enabled_of_mass_le {s : Nat}
    (q : Q) (r w : Bool) (qNext : Q) (tape : Nat)
    (hMass : eraseMass s r <= tape) :
    (reaction (s := s) q r w qNext).enabled
      (FourPhaseEncoding.enc (sourceCfg (s := s) q r w qNext tape)) := by
  intro species
  cases species with
  | ctrl q0 phase0 read0 write0 state0 =>
      simp [sourceCfg, sourceState, reaction, input, eraseMass,
        FourPhaseEncoding.enc, FourPhaseEncoding.control,
        FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar, State.add,
        FourPhaseSpecies.ctrlOf, MicroState.readPhase, MicroState.afterRead]
  | tape =>
      simpa [sourceCfg, reaction, input, eraseMass,
        FourPhaseEncoding.enc, FourPhaseEncoding.control,
        FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar, State.add,
        FourPhaseSpecies.ctrlOf, sourceState, MicroState.readPhase,
        MicroState.afterRead] using hMass
  | tapeBar =>
      simp [sourceCfg, sourceState, reaction, input, eraseMass,
        FourPhaseEncoding.enc, FourPhaseEncoding.control,
        FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar, State.add,
        FourPhaseSpecies.ctrlOf, MicroState.readPhase, MicroState.afterRead]

theorem reaction_enabled {s : Nat}
    (q : Q) (r w : Bool) (qNext : Q) (tape : Nat)
    (hTape : Encoding.IsBase3BoolTape (s + 1) tape)
    (hread : r = Encoding.readMSB? s tape) :
    (reaction (s := s) q r w qNext).enabled
      (FourPhaseEncoding.enc (sourceCfg (s := s) q r w qNext tape)) := by
  exact reaction_enabled_of_mass_le (s := s) q r w qNext tape
    (by
      simpa [eraseMass] using
        Encoding.bitDigit_mul_pow_le_of_IsBase3BoolTape_read hTape hread)

theorem reaction_firesTo {s : Nat}
    (q : Q) (r w : Bool) (qNext : Q) (tape : Nat)
    (hTape : Encoding.IsBase3BoolTape (s + 1) tape)
    (hread : r = Encoding.readMSB? s tape) :
    (reaction (s := s) q r w qNext).FiresTo
      (FourPhaseEncoding.enc (sourceCfg (s := s) q r w qNext tape))
      (FourPhaseEncoding.enc (targetCfg (s := s) q r w qNext tape)) := by
  have hMass : eraseMass s r <= tape := by
    simpa [eraseMass] using
      Encoding.bitDigit_mul_pow_le_of_IsBase3BoolTape_read hTape hread
  have hBar :
      FourPhaseEncoding.maxTape s - Encoding.eraseMSBWith s r tape =
        FourPhaseEncoding.maxTape s - tape + eraseMass s r := by
    simpa [eraseMass] using
      FourPhaseEncoding.maxTape_sub_eraseMSBWith_eq_add hTape hread
  refine ⟨reaction_enabled (s := s) q r w qNext tape hTape hread, ?_⟩
  funext species
  cases species with
  | ctrl q0 phase0 read0 write0 state0 =>
      simp [sourceCfg, targetCfg, sourceState, targetState,
        Reaction.fire, reaction, input, output, eraseMass,
        FourPhaseEncoding.enc, FourPhaseEncoding.control,
        FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar, State.add,
        FourPhaseSpecies.ctrlOf, MicroState.readPhase, MicroState.afterRead,
        MicroState.afterErase]
  | tape =>
      simp [sourceCfg, targetCfg, sourceState, targetState,
        Reaction.fire, reaction, input, output, eraseMass,
        Encoding.eraseMSBWith, FourPhaseEncoding.enc,
        FourPhaseEncoding.control, FourPhaseEncoding.tape,
        FourPhaseEncoding.tapeBar, State.add, FourPhaseSpecies.ctrlOf,
        MicroState.readPhase, MicroState.afterRead, MicroState.afterErase]
  | tapeBar =>
      simpa [sourceCfg, targetCfg, sourceState, targetState,
        Reaction.fire, reaction, input, output, eraseMass,
        FourPhaseEncoding.enc, FourPhaseEncoding.control,
        FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar, State.add,
        FourPhaseSpecies.ctrlOf, MicroState.readPhase, MicroState.afterRead,
        MicroState.afterErase] using hBar

theorem exec {s : Nat}
    (q : Q) (r w : Bool) (qNext : Q) (tape : Nat)
    (hTape : Encoding.IsBase3BoolTape (s + 1) tape)
    (hread : r = Encoding.readMSB? s tape) :
    (network (s := s) q r w qNext).Exec
      (FourPhaseEncoding.enc (sourceCfg (s := s) q r w qNext tape))
      (FourPhaseEncoding.enc (targetCfg (s := s) q r w qNext tape))
      [Network.OneRxnIdx.step] :=
  Network.oneRxn_exec
    (reaction_firesTo (s := s) q r w qNext tape hTape hread)

end EraseGadget

end CTM

end Ripple.sCRNUniversality
