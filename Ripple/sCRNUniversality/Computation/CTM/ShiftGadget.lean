import Ripple.sCRNUniversality.Computation.CTM.GadgetArithmetic

namespace Ripple.sCRNUniversality

namespace CTM

namespace ShiftGadget

universe u

variable {Q : Type u} [DecidableEq Q]

structure Idx (Q : Type u) (s : Nat) where
  q : Q
  r : Bool
  w : Bool
  qNext : Q
  tail : Fin (3 ^ s)
deriving DecidableEq, Repr, Fintype

namespace Idx

def tailVal {Q : Type u} {s : Nat} (i : Idx Q s) : Nat :=
  i.tail.val

theorem tail_lt {Q : Type u} {s : Nat} (i : Idx Q s) :
    i.tailVal < 3 ^ s :=
  i.tail.isLt

end Idx

def shiftMass (tail : Nat) : Nat :=
  2 * tail

def sourceState (q : Q) (r w : Bool) (qNext : Q) : MicroState Q :=
  MicroState.afterErase
    (MicroState.afterRead (MicroState.readPhase q) r w qNext)

def targetState (q : Q) (r w : Bool) (qNext : Q) : MicroState Q :=
  MicroState.afterShift (sourceState q r w qNext)

def sourceCfg {s : Nat} (q : Q) (r w : Bool) (qNext : Q)
    (tape : Nat) : MicroCfg Q s :=
  { state := sourceState q r w qNext, tape := tape }

def targetCfg {s : Nat} (q : Q) (r w : Bool) (qNext : Q)
    (tape : Nat) : MicroCfg Q s :=
  { state := targetState q r w qNext,
    tape := Encoding.shiftTail tape }

def input {s : Nat} (i : Idx Q s) :
    Complex (FourPhaseSpecies Q) :=
  State.add
    (State.add
      (State.single
        (FourPhaseSpecies.ctrlOf
          (sourceState i.q i.r i.w i.qNext)) 1)
      (State.single FourPhaseSpecies.tape i.tailVal))
    (State.single FourPhaseSpecies.tapeBar (shiftMass i.tailVal))

def output {s : Nat} (i : Idx Q s) :
    Complex (FourPhaseSpecies Q) :=
  State.add
    (State.single
      (FourPhaseSpecies.ctrlOf
        (targetState i.q i.r i.w i.qNext)) 1)
    (State.single FourPhaseSpecies.tape (Encoding.shiftTail i.tailVal))

def reaction {s : Nat} (i : Idx Q s) :
    Reaction (FourPhaseSpecies Q) where
  l := input i
  r := output i
  k := 1

@[simp]
theorem reaction_inputArity [Fintype Q] {s : Nat} (i : Idx Q s) :
    (reaction i).inputArity = 1 + i.tailVal + shiftMass i.tailVal := by
  simp [Reaction.inputArity, reaction, input]

@[simp]
theorem reaction_outputArity [Fintype Q] {s : Nat} (i : Idx Q s) :
    (reaction i).outputArity = 1 + Encoding.shiftTail i.tailVal := by
  simp [Reaction.outputArity, reaction, output]

def network (Q : Type u) [Fintype Q] [DecidableEq Q] (s : Nat) :
    Network (FourPhaseSpecies Q) where
  I := Idx Q s
  fintypeI := inferInstance
  rxn := reaction

theorem network_allUnitRate (Q : Type u) [Fintype Q] [DecidableEq Q]
    (s : Nat) :
    (network Q s).allUnitRate := by
  intro i
  rfl

theorem network_hasPositiveRates (Q : Type u) [Fintype Q] [DecidableEq Q]
    (s : Nat) :
    (network Q s).hasPositiveRates :=
  Network.hasPositiveRates_of_allUnitRate
    (network_allUnitRate Q s)

theorem network_equalRates (Q : Type u) [Fintype Q] [DecidableEq Q]
    (s : Nat) :
    (network Q s).equalRates :=
  Network.equalRates_of_allUnitRate
    (network_allUnitRate Q s)

def idxOfTape (q : Q) (r w : Bool) (qNext : Q)
    {s tape : Nat} (hTape : tape < 3 ^ s) : Idx Q s :=
  { q := q, r := r, w := w, qNext := qNext,
    tail := ⟨tape, hTape⟩ }

def zeroIdx {s : Nat} (q : Q) (r w : Bool) (qNext : Q) : Idx Q s :=
  { q := q, r := r, w := w, qNext := qNext,
    tail := ⟨0, Nat.pow_pos (by norm_num)⟩ }

omit [DecidableEq Q] in
@[simp]
theorem zeroIdx_tailVal {s : Nat}
    (q : Q) (r w : Bool) (qNext : Q) :
    (zeroIdx (Q := Q) (s := s) q r w qNext).tailVal = 0 := by
  rfl

theorem reaction_enabled {s : Nat} (i : Idx Q s) :
    (reaction i).enabled
      (FourPhaseEncoding.enc
        (sourceCfg (s := s) i.q i.r i.w i.qNext i.tailVal)) := by
  have hShiftMass :
      shiftMass i.tailVal <= FourPhaseEncoding.maxTape s - i.tailVal := by
    simpa [shiftMass] using
      FourPhaseEncoding.two_mul_le_tapeBar_of_lt_pow i.tail_lt
  intro species
  cases species with
  | ctrl q0 phase0 read0 write0 state0 =>
      simp [sourceCfg, sourceState, reaction, input, shiftMass,
        FourPhaseEncoding.enc, FourPhaseEncoding.control,
        FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar, State.add,
        FourPhaseSpecies.ctrlOf, MicroState.readPhase, MicroState.afterRead,
        MicroState.afterErase]
  | tape =>
      simp [sourceCfg, sourceState, reaction, input, shiftMass,
        FourPhaseEncoding.enc, FourPhaseEncoding.control,
        FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar, State.add,
        FourPhaseSpecies.ctrlOf, MicroState.readPhase, MicroState.afterRead,
        MicroState.afterErase]
  | tapeBar =>
      simpa [sourceCfg, sourceState, reaction, input, shiftMass,
        FourPhaseEncoding.enc, FourPhaseEncoding.control,
        FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar, State.add,
        FourPhaseSpecies.ctrlOf, MicroState.readPhase, MicroState.afterRead,
        MicroState.afterErase] using hShiftMass

theorem reaction_firesTo {s : Nat} (i : Idx Q s) :
    (reaction i).FiresTo
      (FourPhaseEncoding.enc
        (sourceCfg (s := s) i.q i.r i.w i.qNext i.tailVal))
      (FourPhaseEncoding.enc
        (targetCfg (s := s) i.q i.r i.w i.qNext i.tailVal)) := by
  have hBar :
      FourPhaseEncoding.maxTape s - Encoding.shiftTail i.tailVal =
        FourPhaseEncoding.maxTape s - i.tailVal - shiftMass i.tailVal := by
    simpa [shiftMass] using
      FourPhaseEncoding.maxTape_sub_shiftTail_eq_sub i.tail_lt
  refine ⟨reaction_enabled i, ?_⟩
  funext species
  cases species with
  | ctrl q0 phase0 read0 write0 state0 =>
      simp [sourceCfg, targetCfg, sourceState, targetState,
        Reaction.fire, reaction, input, output, shiftMass,
        FourPhaseEncoding.enc, FourPhaseEncoding.control,
        FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar, State.add,
        FourPhaseSpecies.ctrlOf, MicroState.readPhase, MicroState.afterRead,
        MicroState.afterErase, MicroState.afterShift]
  | tape =>
      simp [sourceCfg, targetCfg, sourceState, targetState,
        Reaction.fire, reaction, input, output, shiftMass,
        Encoding.shiftTail, FourPhaseEncoding.enc,
        FourPhaseEncoding.control, FourPhaseEncoding.tape,
        FourPhaseEncoding.tapeBar, State.add, FourPhaseSpecies.ctrlOf,
        MicroState.readPhase, MicroState.afterRead, MicroState.afterErase,
        MicroState.afterShift]
  | tapeBar =>
      simpa [sourceCfg, targetCfg, sourceState, targetState,
        Reaction.fire, reaction, input, output, shiftMass,
        FourPhaseEncoding.enc, FourPhaseEncoding.control,
        FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar, State.add,
        FourPhaseSpecies.ctrlOf, MicroState.readPhase, MicroState.afterRead,
        MicroState.afterErase, MicroState.afterShift]
        using hBar

theorem exec_idx {s : Nat} [Fintype Q] (i : Idx Q s) :
    (network Q s).Exec
      (FourPhaseEncoding.enc
        (sourceCfg (s := s) i.q i.r i.w i.qNext i.tailVal))
      (FourPhaseEncoding.enc
        (targetCfg (s := s) i.q i.r i.w i.qNext i.tailVal))
      [i] := by
  exact ExecOf.cons
    (by simpa [network, Network.StepAt] using reaction_firesTo i)
    (ExecOf.nil _)

theorem zero_tail_reaction_enabled_at_source
    {s : Nat} (q : Q) (r w : Bool) (qNext : Q) (tape : Nat) :
    (reaction (zeroIdx (Q := Q) (s := s) q r w qNext)).enabled
      (FourPhaseEncoding.enc
        (sourceCfg (s := s) q r w qNext tape)) := by
  intro species
  cases species with
  | ctrl q0 phase0 read0 write0 state0 =>
      simp [zeroIdx, sourceCfg, sourceState, reaction, input, shiftMass,
        Idx.tailVal,
        FourPhaseEncoding.enc, FourPhaseEncoding.control,
        FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar, State.add,
        FourPhaseSpecies.ctrlOf, MicroState.readPhase, MicroState.afterRead,
        MicroState.afterErase]
  | tape =>
      simp [zeroIdx, sourceCfg, sourceState, reaction, input, shiftMass,
        Idx.tailVal,
        FourPhaseEncoding.enc, FourPhaseEncoding.control,
        FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar, State.add,
        FourPhaseSpecies.ctrlOf, MicroState.readPhase, MicroState.afterRead,
        MicroState.afterErase]
  | tapeBar =>
      simp [zeroIdx, sourceCfg, sourceState, reaction, input, shiftMass,
        Idx.tailVal,
        FourPhaseEncoding.enc, FourPhaseEncoding.control,
        FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar, State.add,
        FourPhaseSpecies.ctrlOf, MicroState.readPhase, MicroState.afterRead,
        MicroState.afterErase]

theorem zero_tail_reaction_fire_tape_at_source
    {s : Nat} (q : Q) (r w : Bool) (qNext : Q) (tape : Nat) :
    (reaction (zeroIdx (Q := Q) (s := s) q r w qNext)).fire
      (FourPhaseEncoding.enc
        (sourceCfg (s := s) q r w qNext tape))
      FourPhaseSpecies.tape = tape := by
  simp [zeroIdx, sourceCfg, sourceState, reaction, input, output, shiftMass,
    Idx.tailVal, Encoding.shiftTail, Reaction.fire, FourPhaseEncoding.enc,
    FourPhaseEncoding.control, FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar,
    State.add,
    FourPhaseSpecies.ctrlOf, MicroState.readPhase, MicroState.afterRead,
    MicroState.afterErase]

theorem zero_tail_reaction_not_firesTo_target_of_pos_tape
    {s : Nat} (q : Q) (r w : Bool) (qNext : Q) {tape : Nat}
    (hpos : 0 < tape) :
    ¬ (reaction (zeroIdx (Q := Q) (s := s) q r w qNext)).FiresTo
      (FourPhaseEncoding.enc
        (sourceCfg (s := s) q r w qNext tape))
      (FourPhaseEncoding.enc
        (targetCfg (s := s) q r w qNext tape)) := by
  intro hFire
  have hcoord :=
    congrArg (fun z => z FourPhaseSpecies.tape) hFire.eq_fire
  have htarget :
      FourPhaseEncoding.enc
        (targetCfg (s := s) q r w qNext tape)
        FourPhaseSpecies.tape = Encoding.shiftTail tape := by
    simp [targetCfg]
  have hfire :
      (reaction (zeroIdx (Q := Q) (s := s) q r w qNext)).fire
        (FourPhaseEncoding.enc
          (sourceCfg (s := s) q r w qNext tape))
        FourPhaseSpecies.tape = tape :=
    zero_tail_reaction_fire_tape_at_source
      (Q := Q) (s := s) q r w qNext tape
  have hShift : Encoding.shiftTail tape = tape := by
    exact htarget.symm.trans (hcoord.trans hfire)
  unfold Encoding.shiftTail at hShift
  omega

theorem zero_tail_spurious_enabled_not_intended
    {s : Nat} (q : Q) (r w : Bool) (qNext : Q) {tape : Nat}
    (hpos : 0 < tape) :
    (reaction (zeroIdx (Q := Q) (s := s) q r w qNext)).enabled
      (FourPhaseEncoding.enc
        (sourceCfg (s := s) q r w qNext tape)) /\
    Not
      ((reaction (zeroIdx (Q := Q) (s := s) q r w qNext)).FiresTo
        (FourPhaseEncoding.enc
          (sourceCfg (s := s) q r w qNext tape))
        (FourPhaseEncoding.enc
          (targetCfg (s := s) q r w qNext tape))) := by
  exact ⟨zero_tail_reaction_enabled_at_source
      (Q := Q) (s := s) q r w qNext tape,
    zero_tail_reaction_not_firesTo_target_of_pos_tape
      (Q := Q) (s := s) q r w qNext hpos⟩

theorem exec {s : Nat} [Fintype Q]
    (q : Q) (r w : Bool) (qNext : Q) (tape : Nat)
    (hTape : tape < 3 ^ s) :
    (network Q s).Exec
      (FourPhaseEncoding.enc (sourceCfg (s := s) q r w qNext tape))
      (FourPhaseEncoding.enc (targetCfg (s := s) q r w qNext tape))
      [idxOfTape q r w qNext hTape] := by
  simpa [idxOfTape, Idx.tailVal] using
    exec_idx (Q := Q) (s := s) (idxOfTape q r w qNext hTape)

end ShiftGadget

end CTM

end Ripple.sCRNUniversality
