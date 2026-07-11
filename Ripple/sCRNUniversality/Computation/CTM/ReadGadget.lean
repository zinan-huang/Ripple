import Ripple.sCRNUniversality.Computation.CTM.FourPhaseGadgetInterface
import Ripple.sCRNUniversality.Core.OneReaction

namespace Ripple.sCRNUniversality

namespace CTM

namespace ReadGadget

universe u

variable {Q : Type u} [DecidableEq Q]

def sourceCfg {s : Nat} (q : Q) (tape : Nat) : MicroCfg Q s :=
  { state := MicroState.readPhase q, tape := tape }

def targetCfg {s : Nat} (q : Q) (r w : Bool) (qNext : Q)
    (tape : Nat) : MicroCfg Q s :=
  { state := MicroState.afterRead (MicroState.readPhase q) r w qNext,
    tape := tape }

def input {s : Nat} (q : Q) (r : Bool) :
    Complex (FourPhaseSpecies Q) :=
  State.add
    (State.single (FourPhaseSpecies.ctrlOf (MicroState.readPhase q)) 1)
    (State.single (FourPhaseEncoding.readProbe r)
      (FourPhaseEncoding.readProbeNeed s r))

def output {s : Nat} (q : Q) (r w : Bool) (q' : Q) :
    Complex (FourPhaseSpecies Q) :=
  State.add
    (State.single
      (FourPhaseSpecies.ctrlOf
        (MicroState.afterRead (MicroState.readPhase q) r w q')) 1)
    (State.single (FourPhaseEncoding.readProbe r)
      (FourPhaseEncoding.readProbeNeed s r))

def reaction {s : Nat} (q : Q) (r w : Bool) (q' : Q) :
    Reaction (FourPhaseSpecies Q) where
  l := input (s := s) q r
  r := output (s := s) q r w q'
  k := 1

@[simp]
theorem reaction_inputArity [Fintype Q] {s : Nat}
    (q : Q) (r w : Bool) (q' : Q) :
    (reaction (s := s) q r w q').inputArity =
      1 + FourPhaseEncoding.readProbeNeed s r := by
  simp [Reaction.inputArity, reaction, input]

@[simp]
theorem reaction_outputArity [Fintype Q] {s : Nat}
    (q : Q) (r w : Bool) (q' : Q) :
    (reaction (s := s) q r w q').outputArity =
      1 + FourPhaseEncoding.readProbeNeed s r := by
  simp [Reaction.outputArity, reaction, output]

def network {s : Nat} (q : Q) (r w : Bool) (q' : Q) :
    Network (FourPhaseSpecies Q) :=
  Network.oneRxnNetwork (reaction (s := s) q r w q')

theorem reaction_enabled {s : Nat}
    (q : Q) (r w : Bool) (qNext : Q) (tape : Nat)
    (hread : r = Encoding.readMSB? s tape) :
    (reaction (s := s) q r w qNext).enabled
      (FourPhaseEncoding.enc (sourceCfg (s := s) q tape)) := by
  let c : MicroCfg Q s := sourceCfg (s := s) q tape
  have hNeed :
      FourPhaseEncoding.readProbeNeed s r <=
        FourPhaseEncoding.enc c (FourPhaseEncoding.readProbe r) :=
    FourPhaseEncoding.readProbeNeed_le_enc_readProbe_of_readMSB c r hread
  intro species
  cases species with
  | ctrl q0 phase0 read0 write0 state0 =>
      cases r <;>
        simp [sourceCfg, reaction, input, FourPhaseEncoding.readProbe,
          FourPhaseEncoding.readProbeNeed, FourPhaseEncoding.enc,
          FourPhaseEncoding.control, FourPhaseEncoding.tape,
          FourPhaseEncoding.tapeBar, State.add, FourPhaseSpecies.ctrlOf,
          MicroState.readPhase]
  | tape =>
      cases r
      · simp [reaction, input, FourPhaseEncoding.readProbe,
          FourPhaseEncoding.readProbeNeed, State.add]
      · simpa [c, reaction, input, FourPhaseEncoding.readProbe,
          FourPhaseEncoding.readProbeNeed, State.add] using hNeed
  | tapeBar =>
      cases r
      · simpa [c, reaction, input, FourPhaseEncoding.readProbe,
          FourPhaseEncoding.readProbeNeed, State.add] using hNeed
      · simp [reaction, input, FourPhaseEncoding.readProbe,
          FourPhaseEncoding.readProbeNeed, State.add]

theorem reaction_firesTo {s : Nat}
    (q : Q) (r w : Bool) (qNext : Q) (tape : Nat)
    (hread : r = Encoding.readMSB? s tape) :
    (reaction (s := s) q r w qNext).FiresTo
      (FourPhaseEncoding.enc (sourceCfg (s := s) q tape))
      (FourPhaseEncoding.enc (targetCfg (s := s) q r w qNext tape)) := by
  let c : MicroCfg Q s := sourceCfg (s := s) q tape
  have hNeed :
      FourPhaseEncoding.readProbeNeed s r <=
        FourPhaseEncoding.enc c (FourPhaseEncoding.readProbe r) :=
    FourPhaseEncoding.readProbeNeed_le_enc_readProbe_of_readMSB c r hread
  refine ⟨reaction_enabled (s := s) q r w qNext tape hread, ?_⟩
  funext species
  cases species with
  | ctrl q0 phase0 read0 write0 state0 =>
      cases r <;>
        simp [targetCfg, sourceCfg, Reaction.fire, reaction, input, output,
          FourPhaseEncoding.readProbe, FourPhaseEncoding.readProbeNeed,
          FourPhaseEncoding.enc, FourPhaseEncoding.control,
          FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar, State.add,
          FourPhaseSpecies.ctrlOf, MicroState.readPhase, MicroState.afterRead]
  | tape =>
      cases r
      · simp [sourceCfg, targetCfg, Reaction.fire, reaction, input, output,
          FourPhaseEncoding.enc, FourPhaseEncoding.control,
          FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar,
          FourPhaseEncoding.readProbe, FourPhaseEncoding.readProbeNeed, State.add,
          FourPhaseSpecies.ctrlOf, MicroState.readPhase, MicroState.afterRead]
      · have hTape : 2 * 3 ^ s <= tape := by
          simpa [c, sourceCfg, FourPhaseEncoding.readProbe,
            FourPhaseEncoding.readProbeNeed, FourPhaseEncoding.enc,
            FourPhaseEncoding.control, FourPhaseEncoding.tape,
            FourPhaseEncoding.tapeBar, State.add, FourPhaseSpecies.ctrlOf,
            MicroState.readPhase] using hNeed
        simp [sourceCfg, targetCfg, Reaction.fire, reaction, input, output,
          FourPhaseEncoding.enc, FourPhaseEncoding.control,
          FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar,
          FourPhaseEncoding.readProbe, FourPhaseEncoding.readProbeNeed, State.add,
          FourPhaseSpecies.ctrlOf, MicroState.readPhase, MicroState.afterRead,
          Nat.sub_add_cancel hTape]
  | tapeBar =>
      cases r
      · have hBar : 3 ^ s <= FourPhaseEncoding.maxTape s - tape := by
          simpa [c, sourceCfg, FourPhaseEncoding.readProbe,
            FourPhaseEncoding.readProbeNeed, FourPhaseEncoding.enc,
            FourPhaseEncoding.control, FourPhaseEncoding.tape,
            FourPhaseEncoding.tapeBar, State.add, FourPhaseSpecies.ctrlOf,
            MicroState.readPhase] using hNeed
        simp [sourceCfg, targetCfg, Reaction.fire, reaction, input, output,
          FourPhaseEncoding.enc, FourPhaseEncoding.control,
          FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar,
          FourPhaseEncoding.readProbe, FourPhaseEncoding.readProbeNeed, State.add,
          FourPhaseSpecies.ctrlOf, MicroState.readPhase, MicroState.afterRead,
          Nat.sub_add_cancel hBar]
      · simp [sourceCfg, targetCfg, Reaction.fire, reaction, input, output,
          FourPhaseEncoding.enc, FourPhaseEncoding.control,
          FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar,
          FourPhaseEncoding.readProbe, FourPhaseEncoding.readProbeNeed, State.add,
          FourPhaseSpecies.ctrlOf, MicroState.readPhase, MicroState.afterRead]

theorem exec {s : Nat}
    (q : Q) (r w : Bool) (qNext : Q) (tape : Nat)
    (hread : r = Encoding.readMSB? s tape) :
    (network (s := s) q r w qNext).Exec
      (FourPhaseEncoding.enc (sourceCfg (s := s) q tape))
      (FourPhaseEncoding.enc (targetCfg (s := s) q r w qNext tape))
      [Network.OneRxnIdx.step] :=
  Network.oneRxn_exec (reaction_firesTo (s := s) q r w qNext tape hread)

end ReadGadget

end CTM

end Ripple.sCRNUniversality
