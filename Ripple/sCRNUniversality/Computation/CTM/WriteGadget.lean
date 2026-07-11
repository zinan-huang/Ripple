import Ripple.sCRNUniversality.Computation.CTM.GadgetArithmetic
import Ripple.sCRNUniversality.Core.OneReaction

namespace Ripple.sCRNUniversality

namespace CTM

namespace WriteGadget

universe u

variable {Q : Type u} [DecidableEq Q]

def writeMass (w : Bool) : Nat :=
  Encoding.bitDigit w

def sourceState (q : Q) (r w : Bool) (qNext : Q) : MicroState Q :=
  MicroState.afterShift
    (MicroState.afterErase
      (MicroState.afterRead (MicroState.readPhase q) r w qNext))

def targetState (_q : Q) (_r _w : Bool) (qNext : Q) : MicroState Q :=
  MicroState.afterWrite qNext

def sourceCfg {s : Nat} (q : Q) (r w : Bool) (qNext : Q)
    (tape : Nat) : MicroCfg Q s :=
  { state := sourceState q r w qNext, tape := tape }

def targetCfg {s : Nat} (q : Q) (r w : Bool) (qNext : Q)
    (tape : Nat) : MicroCfg Q s :=
  { state := targetState q r w qNext,
    tape := Encoding.writeLSB tape w }

def input (q : Q) (r w : Bool) (qNext : Q) :
    Complex (FourPhaseSpecies Q) :=
  State.add
    (State.single (FourPhaseSpecies.ctrlOf (sourceState q r w qNext)) 1)
    (State.single FourPhaseSpecies.tapeBar (writeMass w))

def output (q : Q) (r w : Bool) (qNext : Q) :
    Complex (FourPhaseSpecies Q) :=
  State.add
    (State.single (FourPhaseSpecies.ctrlOf (targetState q r w qNext)) 1)
    (State.single FourPhaseSpecies.tape (writeMass w))

def reaction (q : Q) (r w : Bool) (qNext : Q) :
    Reaction (FourPhaseSpecies Q) where
  l := input q r w qNext
  r := output q r w qNext
  k := 1

@[simp]
theorem reaction_inputArity [Fintype Q]
    (q : Q) (r w : Bool) (qNext : Q) :
    (reaction q r w qNext).inputArity = 1 + writeMass w := by
  simp [Reaction.inputArity, reaction, input]

@[simp]
theorem reaction_outputArity [Fintype Q]
    (q : Q) (r w : Bool) (qNext : Q) :
    (reaction q r w qNext).outputArity = 1 + writeMass w := by
  simp [Reaction.outputArity, reaction, output]

def network (q : Q) (r w : Bool) (qNext : Q) :
    Network (FourPhaseSpecies Q) :=
  Network.oneRxnNetwork (reaction q r w qNext)

theorem reaction_enabled_of_mass_le {s : Nat}
    (q : Q) (r w : Bool) (qNext : Q) (tape : Nat)
    (hMass : writeMass w <= FourPhaseEncoding.maxTape s - tape) :
    (reaction q r w qNext).enabled
      (FourPhaseEncoding.enc (sourceCfg (s := s) q r w qNext tape)) := by
  intro species
  cases species with
  | ctrl q0 phase0 read0 write0 state0 =>
      simp [sourceCfg, sourceState, reaction, input, writeMass,
        FourPhaseEncoding.enc, FourPhaseEncoding.control,
        FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar, State.add,
        FourPhaseSpecies.ctrlOf, MicroState.readPhase, MicroState.afterRead,
        MicroState.afterErase, MicroState.afterShift]
  | tape =>
      simp [sourceCfg, sourceState, reaction, input, writeMass,
        FourPhaseEncoding.enc, FourPhaseEncoding.control,
        FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar, State.add,
        FourPhaseSpecies.ctrlOf, MicroState.readPhase, MicroState.afterRead,
        MicroState.afterErase, MicroState.afterShift]
  | tapeBar =>
      simpa [sourceCfg, sourceState, reaction, input, writeMass,
        FourPhaseEncoding.enc, FourPhaseEncoding.control,
        FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar, State.add,
        FourPhaseSpecies.ctrlOf, MicroState.readPhase, MicroState.afterRead,
        MicroState.afterErase, MicroState.afterShift] using hMass

theorem reaction_enabled {s : Nat}
    (q : Q) (r w : Bool) (qNext : Q) (tape : Nat)
    (hTape : Encoding.IsShiftedBase3BoolTape s tape) :
    (reaction q r w qNext).enabled
      (FourPhaseEncoding.enc (sourceCfg (s := s) q r w qNext tape)) := by
  exact reaction_enabled_of_mass_le (s := s) q r w qNext tape
    (by
      simpa [writeMass] using
        FourPhaseEncoding.bitDigit_le_tapeBar_of_shifted hTape w)

theorem reaction_firesTo {s : Nat}
    (q : Q) (r w : Bool) (qNext : Q) (tape : Nat)
    (hTape : Encoding.IsShiftedBase3BoolTape s tape) :
    (reaction q r w qNext).FiresTo
      (FourPhaseEncoding.enc (sourceCfg (s := s) q r w qNext tape))
      (FourPhaseEncoding.enc (targetCfg (s := s) q r w qNext tape)) := by
  have hBar :
      FourPhaseEncoding.maxTape s - Encoding.writeLSB tape w =
        FourPhaseEncoding.maxTape s - tape - writeMass w := by
    simpa [writeMass] using
      FourPhaseEncoding.maxTape_sub_writeLSB_eq_sub_of_shifted hTape w
  refine ⟨reaction_enabled (s := s) q r w qNext tape hTape, ?_⟩
  funext species
  cases species with
  | ctrl q0 phase0 read0 write0 state0 =>
      simp [sourceCfg, targetCfg, sourceState, targetState,
        Reaction.fire, reaction, input, output, writeMass,
        FourPhaseEncoding.enc, FourPhaseEncoding.control,
        FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar, State.add,
        FourPhaseSpecies.ctrlOf, MicroState.readPhase, MicroState.afterRead,
        MicroState.afterErase, MicroState.afterShift, MicroState.afterWrite]
  | tape =>
      simp [sourceCfg, targetCfg, sourceState, targetState,
        Reaction.fire, reaction, input, output, writeMass,
        Encoding.writeLSB, FourPhaseEncoding.enc,
        FourPhaseEncoding.control, FourPhaseEncoding.tape,
        FourPhaseEncoding.tapeBar, State.add, FourPhaseSpecies.ctrlOf,
        MicroState.readPhase, MicroState.afterRead, MicroState.afterErase,
        MicroState.afterShift, MicroState.afterWrite]
  | tapeBar =>
      simpa [sourceCfg, targetCfg, sourceState, targetState,
        Reaction.fire, reaction, input, output, writeMass,
        FourPhaseEncoding.enc, FourPhaseEncoding.control,
        FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar, State.add,
        FourPhaseSpecies.ctrlOf, MicroState.readPhase, MicroState.afterRead,
        MicroState.afterErase, MicroState.afterShift, MicroState.afterWrite]
        using hBar

theorem exec {s : Nat}
    (q : Q) (r w : Bool) (qNext : Q) (tape : Nat)
    (hTape : Encoding.IsShiftedBase3BoolTape s tape) :
    (network q r w qNext).Exec
      (FourPhaseEncoding.enc (sourceCfg (s := s) q r w qNext tape))
      (FourPhaseEncoding.enc (targetCfg (s := s) q r w qNext tape))
      [Network.OneRxnIdx.step] :=
  Network.oneRxn_exec
    (reaction_firesTo (s := s) q r w qNext tape hTape)

end WriteGadget

end CTM

end Ripple.sCRNUniversality
