import Ripple.sCRNUniversality.Computation.CTM.FourPhaseMacroModule
import Ripple.sCRNUniversality.Computation.CTM.FourPhaseEncodingSafety

namespace Ripple.sCRNUniversality

namespace CTM

universe u

namespace ReadGadget

variable {Q : Type u} [DecidableEq Q]

theorem reaction_guardedBy {s : Nat}
    (q : Q) (r w : Bool) (qNext : Q) :
    (reaction (s := s) q r w qNext).GuardedBy
      (FourPhaseSpecies.ctrlOf (MicroState.readPhase q)) := by
  simp [Reaction.GuardedBy, Reaction.Requires, reaction, input, State.add,
    State.single, FourPhaseSpecies.ctrlOf, MicroState.readPhase]

end ReadGadget

namespace EraseGadget

variable {Q : Type u} [DecidableEq Q]

theorem reaction_guardedBy {s : Nat}
    (q : Q) (r w : Bool) (qNext : Q) :
    (reaction (s := s) q r w qNext).GuardedBy
      (FourPhaseSpecies.ctrlOf (sourceState q r w qNext)) := by
  simp [Reaction.GuardedBy, Reaction.Requires, reaction, input, State.add,
    State.single, FourPhaseSpecies.ctrlOf, sourceState,
    MicroState.readPhase, MicroState.afterRead]

end EraseGadget

namespace ShiftGadget

variable {Q : Type u} [DecidableEq Q]

theorem reaction_guardedBy {s : Nat} (i : Idx Q s) :
    (reaction i).GuardedBy
      (FourPhaseSpecies.ctrlOf (sourceState i.q i.r i.w i.qNext)) := by
  simp [Reaction.GuardedBy, Reaction.Requires, reaction, input, State.add,
    State.single, FourPhaseSpecies.ctrlOf, sourceState,
    MicroState.readPhase, MicroState.afterRead, MicroState.afterErase]

end ShiftGadget

namespace WriteGadget

variable {Q : Type u} [DecidableEq Q]

theorem reaction_guardedBy
    (q : Q) (r w : Bool) (qNext : Q) :
    (reaction q r w qNext).GuardedBy
      (FourPhaseSpecies.ctrlOf (sourceState q r w qNext)) := by
  simp [Reaction.GuardedBy, Reaction.Requires, reaction, input, State.add,
    State.single, FourPhaseSpecies.ctrlOf, sourceState,
    MicroState.readPhase, MicroState.afterRead, MicroState.afterErase,
    MicroState.afterShift]

end WriteGadget

namespace ReadNetwork

theorem network_guardedByFamily {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) :
    (network (s := s) M).GuardedByFamily
      (fun i =>
        FourPhaseSpecies.ctrlOf (MicroState.readPhase (ReadIdx.q i))) := by
  intro i
  simpa [network] using
    ReadGadget.reaction_guardedBy (s := s)
      (ReadIdx.q i) (ReadIdx.r i) (ReadIdx.w i) (ReadIdx.qNext i)

end ReadNetwork

namespace EraseNetwork

theorem network_guardedByFamily {Q : Type u} [Fintype Q] [DecidableEq Q]
    (s : Nat) :
    (network Q s).GuardedByFamily
      (fun i =>
        FourPhaseSpecies.ctrlOf
          (EraseGadget.sourceState i.q i.r i.w i.qNext)) := by
  intro i
  simpa [network] using
    EraseGadget.reaction_guardedBy (s := s) i.q i.r i.w i.qNext

end EraseNetwork

namespace ShiftGadget

theorem network_guardedByFamily (Q : Type u) [Fintype Q] [DecidableEq Q]
    (s : Nat) :
    (network Q s).GuardedByFamily
      (fun i =>
        FourPhaseSpecies.ctrlOf (sourceState i.q i.r i.w i.qNext)) := by
  intro i
  simpa [network] using reaction_guardedBy (Q := Q) (s := s) i

end ShiftGadget

namespace WriteNetwork

theorem network_guardedByFamily (Q : Type u) [Fintype Q] [DecidableEq Q] :
    (network Q).GuardedByFamily
      (fun i =>
        FourPhaseSpecies.ctrlOf
          (WriteGadget.sourceState i.q i.r i.w i.qNext)) := by
  intro i
  simpa [network] using
    WriteGadget.reaction_guardedBy i.q i.r i.w i.qNext

end WriteNetwork

namespace FourPhaseMacroSafety

theorem readNetwork_terminal_of_ne_phase
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) (c : MicroCfg Q s)
    (hphase : Phase4.read ≠ c.state.phase) :
    (ReadNetwork.network (s := s) M).Terminal
      (FourPhaseEncoding.enc c) := by
  apply Network.terminal_of_guardedByFamily_zero
  · exact ReadNetwork.network_guardedByFamily (s := s) M
  · intro i
    exact FourPhaseEncoding.enc_ctrlOf_eq_zero_of_ne_phase
      c (MicroState.readPhase (ReadNetwork.ReadIdx.q i))
      (by simpa [MicroState.readPhase] using hphase)

theorem eraseNetwork_terminal_of_ne_phase
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (c : MicroCfg Q s)
    (hphase : Phase4.erase ≠ c.state.phase) :
    (EraseNetwork.network Q s).Terminal
      (FourPhaseEncoding.enc c) := by
  apply Network.terminal_of_guardedByFamily_zero
  · exact EraseNetwork.network_guardedByFamily (Q := Q) s
  · intro i
    exact FourPhaseEncoding.enc_ctrlOf_eq_zero_of_ne_phase
      c (EraseGadget.sourceState i.q i.r i.w i.qNext)
      (by simpa [EraseGadget.sourceState, MicroState.readPhase,
        MicroState.afterRead] using hphase)

theorem shiftNetwork_terminal_of_ne_phase
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (c : MicroCfg Q s)
    (hphase : Phase4.shift ≠ c.state.phase) :
    (ShiftGadget.network Q s).Terminal
      (FourPhaseEncoding.enc c) := by
  apply Network.terminal_of_guardedByFamily_zero
  · exact ShiftGadget.network_guardedByFamily Q s
  · intro i
    exact FourPhaseEncoding.enc_ctrlOf_eq_zero_of_ne_phase
      c (ShiftGadget.sourceState i.q i.r i.w i.qNext)
      (by simpa [ShiftGadget.sourceState, MicroState.readPhase,
        MicroState.afterRead, MicroState.afterErase] using hphase)

theorem writeNetwork_terminal_of_ne_phase
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (c : MicroCfg Q s)
    (hphase : Phase4.write ≠ c.state.phase) :
    (WriteNetwork.network Q).Terminal
      (FourPhaseEncoding.enc c) := by
  apply Network.terminal_of_guardedByFamily_zero
  · exact WriteNetwork.network_guardedByFamily Q
  · intro i
    exact FourPhaseEncoding.enc_ctrlOf_eq_zero_of_ne_phase
      c (WriteGadget.sourceState i.q i.r i.w i.qNext)
      (by simpa [WriteGadget.sourceState, MicroState.readPhase,
        MicroState.afterRead, MicroState.afterErase, MicroState.afterShift]
        using hphase)

theorem macro_no_read_stepAt_of_ne_phase
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) (c : MicroCfg Q s)
    (hphase : Phase4.read ≠ c.state.phase)
    {i : (ReadNetwork.network (s := s) M).I}
    {z' : State (FourPhaseSpecies Q)} :
    Not
      ((FourPhaseMacroModule.network (s := s) M).StepAt
        (Sum.inl (Sum.inl i))
        (FourPhaseEncoding.enc c) z') := by
  intro hStep
  have hRead :
      (ReadNetwork.network (s := s) M).StepAt i
        (FourPhaseEncoding.enc c) z' := by
    simpa [FourPhaseMacroModule.network] using hStep
  exact (readNetwork_terminal_of_ne_phase (s := s) M c hphase) i hRead.enabled

theorem macro_no_erase_stepAt_of_ne_phase
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) (c : MicroCfg Q s)
    (hphase : Phase4.erase ≠ c.state.phase)
    {i : (EraseNetwork.network Q s).I}
    {z' : State (FourPhaseSpecies Q)} :
    Not
      ((FourPhaseMacroModule.network (s := s) M).StepAt
        (Sum.inl (Sum.inr i))
        (FourPhaseEncoding.enc c) z') := by
  intro hStep
  have hErase :
      (EraseNetwork.network Q s).StepAt i
        (FourPhaseEncoding.enc c) z' := by
    simpa [FourPhaseMacroModule.network] using hStep
  exact (eraseNetwork_terminal_of_ne_phase (s := s) c hphase) i hErase.enabled

theorem macro_no_shift_stepAt_of_ne_phase
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) (c : MicroCfg Q s)
    (hphase : Phase4.shift ≠ c.state.phase)
    {i : (ShiftGadget.network Q s).I}
    {z' : State (FourPhaseSpecies Q)} :
    Not
      ((FourPhaseMacroModule.network (s := s) M).StepAt
        (Sum.inr (Sum.inl i))
        (FourPhaseEncoding.enc c) z') := by
  intro hStep
  have hShift :
      (ShiftGadget.network Q s).StepAt i
        (FourPhaseEncoding.enc c) z' := by
    simpa [FourPhaseMacroModule.network] using hStep
  exact (shiftNetwork_terminal_of_ne_phase (s := s) c hphase) i hShift.enabled

theorem macro_no_write_stepAt_of_ne_phase
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) (c : MicroCfg Q s)
    (hphase : Phase4.write ≠ c.state.phase)
    {i : (WriteNetwork.network Q).I}
    {z' : State (FourPhaseSpecies Q)} :
    Not
      ((FourPhaseMacroModule.network (s := s) M).StepAt
        (Sum.inr (Sum.inr i))
        (FourPhaseEncoding.enc c) z') := by
  intro hStep
  have hWrite :
      (WriteNetwork.network Q).StepAt i
        (FourPhaseEncoding.enc c) z' := by
    simpa [FourPhaseMacroModule.network] using hStep
  exact (writeNetwork_terminal_of_ne_phase (s := s) c hphase) i hWrite.enabled

theorem enabledAt_isReadIndex_of_phase_read
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) {c : MicroCfg Q s}
    {i : (FourPhaseMacroModule.network (s := s) M).I}
    (hphase : c.state.phase = Phase4.read)
    (hEnabled :
      (FourPhaseMacroModule.network (s := s) M).EnabledAt
        (FourPhaseEncoding.enc c) i) :
    FourPhaseMacroModule.IsReadIndex (s := s) M i := by
  rcases i with (iRead | iErase) | (iShift | iWrite)
  · exact ⟨iRead, rfl⟩
  · rcases
      (Network.exists_stepAt_iff_enabledAt
        (N := FourPhaseMacroModule.network (s := s) M)
        (i := Sum.inl (Sum.inr iErase))
        (z := FourPhaseEncoding.enc c)).mpr hEnabled with
      ⟨z', hStep⟩
    exfalso
    exact
      (macro_no_erase_stepAt_of_ne_phase
        (s := s) M c
        (by simp [hphase])
        (i := iErase) (z' := z')) hStep
  · rcases
      (Network.exists_stepAt_iff_enabledAt
        (N := FourPhaseMacroModule.network (s := s) M)
        (i := Sum.inr (Sum.inl iShift))
        (z := FourPhaseEncoding.enc c)).mpr hEnabled with
      ⟨z', hStep⟩
    exfalso
    exact
      (macro_no_shift_stepAt_of_ne_phase
        (s := s) M c
        (by simp [hphase])
        (i := iShift) (z' := z')) hStep
  · rcases
      (Network.exists_stepAt_iff_enabledAt
        (N := FourPhaseMacroModule.network (s := s) M)
        (i := Sum.inr (Sum.inr iWrite))
        (z := FourPhaseEncoding.enc c)).mpr hEnabled with
      ⟨z', hStep⟩
    exfalso
    exact
      (macro_no_write_stepAt_of_ne_phase
        (s := s) M c
        (by simp [hphase])
        (i := iWrite) (z' := z')) hStep

theorem enabledAt_isEraseIndex_of_phase_erase
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) {c : MicroCfg Q s}
    {i : (FourPhaseMacroModule.network (s := s) M).I}
    (hphase : c.state.phase = Phase4.erase)
    (hEnabled :
      (FourPhaseMacroModule.network (s := s) M).EnabledAt
        (FourPhaseEncoding.enc c) i) :
    FourPhaseMacroModule.IsEraseIndex (s := s) M i := by
  rcases i with (iRead | iErase) | (iShift | iWrite)
  · rcases
      (Network.exists_stepAt_iff_enabledAt
        (N := FourPhaseMacroModule.network (s := s) M)
        (i := Sum.inl (Sum.inl iRead))
        (z := FourPhaseEncoding.enc c)).mpr hEnabled with
      ⟨z', hStep⟩
    exfalso
    exact
      (macro_no_read_stepAt_of_ne_phase
        (s := s) M c
        (by simp [hphase])
        (i := iRead) (z' := z')) hStep
  · exact ⟨iErase, rfl⟩
  · rcases
      (Network.exists_stepAt_iff_enabledAt
        (N := FourPhaseMacroModule.network (s := s) M)
        (i := Sum.inr (Sum.inl iShift))
        (z := FourPhaseEncoding.enc c)).mpr hEnabled with
      ⟨z', hStep⟩
    exfalso
    exact
      (macro_no_shift_stepAt_of_ne_phase
        (s := s) M c
        (by simp [hphase])
        (i := iShift) (z' := z')) hStep
  · rcases
      (Network.exists_stepAt_iff_enabledAt
        (N := FourPhaseMacroModule.network (s := s) M)
        (i := Sum.inr (Sum.inr iWrite))
        (z := FourPhaseEncoding.enc c)).mpr hEnabled with
      ⟨z', hStep⟩
    exfalso
    exact
      (macro_no_write_stepAt_of_ne_phase
        (s := s) M c
        (by simp [hphase])
        (i := iWrite) (z' := z')) hStep

theorem enabledAt_isShiftIndex_of_phase_shift
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) {c : MicroCfg Q s}
    {i : (FourPhaseMacroModule.network (s := s) M).I}
    (hphase : c.state.phase = Phase4.shift)
    (hEnabled :
      (FourPhaseMacroModule.network (s := s) M).EnabledAt
        (FourPhaseEncoding.enc c) i) :
    FourPhaseMacroModule.IsShiftIndex (s := s) M i := by
  rcases i with (iRead | iErase) | (iShift | iWrite)
  · rcases
      (Network.exists_stepAt_iff_enabledAt
        (N := FourPhaseMacroModule.network (s := s) M)
        (i := Sum.inl (Sum.inl iRead))
        (z := FourPhaseEncoding.enc c)).mpr hEnabled with
      ⟨z', hStep⟩
    exfalso
    exact
      (macro_no_read_stepAt_of_ne_phase
        (s := s) M c
        (by simp [hphase])
        (i := iRead) (z' := z')) hStep
  · rcases
      (Network.exists_stepAt_iff_enabledAt
        (N := FourPhaseMacroModule.network (s := s) M)
        (i := Sum.inl (Sum.inr iErase))
        (z := FourPhaseEncoding.enc c)).mpr hEnabled with
      ⟨z', hStep⟩
    exfalso
    exact
      (macro_no_erase_stepAt_of_ne_phase
        (s := s) M c
        (by simp [hphase])
        (i := iErase) (z' := z')) hStep
  · exact ⟨iShift, rfl⟩
  · rcases
      (Network.exists_stepAt_iff_enabledAt
        (N := FourPhaseMacroModule.network (s := s) M)
        (i := Sum.inr (Sum.inr iWrite))
        (z := FourPhaseEncoding.enc c)).mpr hEnabled with
      ⟨z', hStep⟩
    exfalso
    exact
      (macro_no_write_stepAt_of_ne_phase
        (s := s) M c
        (by simp [hphase])
        (i := iWrite) (z' := z')) hStep

theorem enabledAt_isWriteIndex_of_phase_write
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) {c : MicroCfg Q s}
    {i : (FourPhaseMacroModule.network (s := s) M).I}
    (hphase : c.state.phase = Phase4.write)
    (hEnabled :
      (FourPhaseMacroModule.network (s := s) M).EnabledAt
        (FourPhaseEncoding.enc c) i) :
    FourPhaseMacroModule.IsWriteIndex (s := s) M i := by
  rcases i with (iRead | iErase) | (iShift | iWrite)
  · rcases
      (Network.exists_stepAt_iff_enabledAt
        (N := FourPhaseMacroModule.network (s := s) M)
        (i := Sum.inl (Sum.inl iRead))
        (z := FourPhaseEncoding.enc c)).mpr hEnabled with
      ⟨z', hStep⟩
    exfalso
    exact
      (macro_no_read_stepAt_of_ne_phase
        (s := s) M c
        (by simp [hphase])
        (i := iRead) (z' := z')) hStep
  · rcases
      (Network.exists_stepAt_iff_enabledAt
        (N := FourPhaseMacroModule.network (s := s) M)
        (i := Sum.inl (Sum.inr iErase))
        (z := FourPhaseEncoding.enc c)).mpr hEnabled with
      ⟨z', hStep⟩
    exfalso
    exact
      (macro_no_erase_stepAt_of_ne_phase
        (s := s) M c
        (by simp [hphase])
        (i := iErase) (z' := z')) hStep
  · rcases
      (Network.exists_stepAt_iff_enabledAt
        (N := FourPhaseMacroModule.network (s := s) M)
        (i := Sum.inr (Sum.inl iShift))
        (z := FourPhaseEncoding.enc c)).mpr hEnabled with
      ⟨z', hStep⟩
    exfalso
    exact
      (macro_no_shift_stepAt_of_ne_phase
        (s := s) M c
        (by simp [hphase])
        (i := iShift) (z' := z')) hStep
  · exact ⟨iWrite, rfl⟩

def badUnlessReadIndex
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) :
    (FourPhaseMacroModule.network (s := s) M).BadIndexSet :=
  fun i => Not (FourPhaseMacroModule.IsReadIndex (s := s) M i)

def badUnlessEraseIndex
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) :
    (FourPhaseMacroModule.network (s := s) M).BadIndexSet :=
  fun i => Not (FourPhaseMacroModule.IsEraseIndex (s := s) M i)

def badUnlessShiftIndex
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) :
    (FourPhaseMacroModule.network (s := s) M).BadIndexSet :=
  fun i => Not (FourPhaseMacroModule.IsShiftIndex (s := s) M i)

def badUnlessWriteIndex
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) :
    (FourPhaseMacroModule.network (s := s) M).BadIndexSet :=
  fun i => Not (FourPhaseMacroModule.IsWriteIndex (s := s) M i)

def offPhaseBadIndexSet
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) (c : MicroCfg Q s) :
    (FourPhaseMacroModule.network (s := s) M).BadIndexSet :=
  match c.state.phase with
  | Phase4.read => badUnlessReadIndex (s := s) M
  | Phase4.erase => badUnlessEraseIndex (s := s) M
  | Phase4.shift => badUnlessShiftIndex (s := s) M
  | Phase4.write => badUnlessWriteIndex (s := s) M

theorem not_badUnlessReadIndex_of_enabledAt_phase_read
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) {c : MicroCfg Q s}
    {i : (FourPhaseMacroModule.network (s := s) M).I}
    (hphase : c.state.phase = Phase4.read)
    (hEnabled :
      (FourPhaseMacroModule.network (s := s) M).EnabledAt
        (FourPhaseEncoding.enc c) i) :
    Not (badUnlessReadIndex (s := s) M i) := by
  intro hbad
  exact hbad
    (enabledAt_isReadIndex_of_phase_read
      (s := s) M hphase hEnabled)

theorem not_badUnlessEraseIndex_of_enabledAt_phase_erase
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) {c : MicroCfg Q s}
    {i : (FourPhaseMacroModule.network (s := s) M).I}
    (hphase : c.state.phase = Phase4.erase)
    (hEnabled :
      (FourPhaseMacroModule.network (s := s) M).EnabledAt
        (FourPhaseEncoding.enc c) i) :
    Not (badUnlessEraseIndex (s := s) M i) := by
  intro hbad
  exact hbad
    (enabledAt_isEraseIndex_of_phase_erase
      (s := s) M hphase hEnabled)

theorem not_badUnlessShiftIndex_of_enabledAt_phase_shift
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) {c : MicroCfg Q s}
    {i : (FourPhaseMacroModule.network (s := s) M).I}
    (hphase : c.state.phase = Phase4.shift)
    (hEnabled :
      (FourPhaseMacroModule.network (s := s) M).EnabledAt
        (FourPhaseEncoding.enc c) i) :
    Not (badUnlessShiftIndex (s := s) M i) := by
  intro hbad
  exact hbad
    (enabledAt_isShiftIndex_of_phase_shift
      (s := s) M hphase hEnabled)

theorem not_badUnlessWriteIndex_of_enabledAt_phase_write
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) {c : MicroCfg Q s}
    {i : (FourPhaseMacroModule.network (s := s) M).I}
    (hphase : c.state.phase = Phase4.write)
    (hEnabled :
      (FourPhaseMacroModule.network (s := s) M).EnabledAt
        (FourPhaseEncoding.enc c) i) :
    Not (badUnlessWriteIndex (s := s) M i) := by
  intro hbad
  exact hbad
    (enabledAt_isWriteIndex_of_phase_write
      (s := s) M hphase hEnabled)

theorem not_offPhaseBadIndexSet_of_enabledAt_encoded
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) {c : MicroCfg Q s}
    {i : (FourPhaseMacroModule.network (s := s) M).I}
    (hEnabled :
      (FourPhaseMacroModule.network (s := s) M).EnabledAt
        (FourPhaseEncoding.enc c) i) :
    Not (offPhaseBadIndexSet (s := s) M c i) := by
  cases hphase : c.state.phase
  · simpa [offPhaseBadIndexSet, hphase] using
      not_badUnlessReadIndex_of_enabledAt_phase_read
        (s := s) M hphase hEnabled
  · simpa [offPhaseBadIndexSet, hphase] using
      not_badUnlessEraseIndex_of_enabledAt_phase_erase
        (s := s) M hphase hEnabled
  · simpa [offPhaseBadIndexSet, hphase] using
      not_badUnlessShiftIndex_of_enabledAt_phase_shift
        (s := s) M hphase hEnabled
  · simpa [offPhaseBadIndexSet, hphase] using
      not_badUnlessWriteIndex_of_enabledAt_phase_write
        (s := s) M hphase hEnabled

theorem not_badFiresAt_badUnlessReadIndex_of_state_phase_read
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {path : (FourPhaseMacroModule.network (s := s) M).Path}
    {c : MicroCfg Q s} {t : Nat}
    (hstate : path.state t = FourPhaseEncoding.enc c)
    (hphase : c.state.phase = Phase4.read) :
    Not (path.BadFiresAt (badUnlessReadIndex (s := s) M) t) := by
  rintro ⟨i, hfired, hbad⟩
  have hEnabled :
      (FourPhaseMacroModule.network (s := s) M).EnabledAt
        (FourPhaseEncoding.enc c) i := by
    have hStep := Network.Path.stepAt_of_fired (path := path) hfired
    simpa [hstate] using hStep.enabled
  exact
    (not_badUnlessReadIndex_of_enabledAt_phase_read
      (s := s) M hphase hEnabled) hbad

theorem not_badFiresAt_badUnlessEraseIndex_of_state_phase_erase
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {path : (FourPhaseMacroModule.network (s := s) M).Path}
    {c : MicroCfg Q s} {t : Nat}
    (hstate : path.state t = FourPhaseEncoding.enc c)
    (hphase : c.state.phase = Phase4.erase) :
    Not (path.BadFiresAt (badUnlessEraseIndex (s := s) M) t) := by
  rintro ⟨i, hfired, hbad⟩
  have hEnabled :
      (FourPhaseMacroModule.network (s := s) M).EnabledAt
        (FourPhaseEncoding.enc c) i := by
    have hStep := Network.Path.stepAt_of_fired (path := path) hfired
    simpa [hstate] using hStep.enabled
  exact
    (not_badUnlessEraseIndex_of_enabledAt_phase_erase
      (s := s) M hphase hEnabled) hbad

theorem not_badFiresAt_badUnlessShiftIndex_of_state_phase_shift
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {path : (FourPhaseMacroModule.network (s := s) M).Path}
    {c : MicroCfg Q s} {t : Nat}
    (hstate : path.state t = FourPhaseEncoding.enc c)
    (hphase : c.state.phase = Phase4.shift) :
    Not (path.BadFiresAt (badUnlessShiftIndex (s := s) M) t) := by
  rintro ⟨i, hfired, hbad⟩
  have hEnabled :
      (FourPhaseMacroModule.network (s := s) M).EnabledAt
        (FourPhaseEncoding.enc c) i := by
    have hStep := Network.Path.stepAt_of_fired (path := path) hfired
    simpa [hstate] using hStep.enabled
  exact
    (not_badUnlessShiftIndex_of_enabledAt_phase_shift
      (s := s) M hphase hEnabled) hbad

theorem not_badFiresAt_badUnlessWriteIndex_of_state_phase_write
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {path : (FourPhaseMacroModule.network (s := s) M).Path}
    {c : MicroCfg Q s} {t : Nat}
    (hstate : path.state t = FourPhaseEncoding.enc c)
    (hphase : c.state.phase = Phase4.write) :
    Not (path.BadFiresAt (badUnlessWriteIndex (s := s) M) t) := by
  rintro ⟨i, hfired, hbad⟩
  have hEnabled :
      (FourPhaseMacroModule.network (s := s) M).EnabledAt
        (FourPhaseEncoding.enc c) i := by
    have hStep := Network.Path.stepAt_of_fired (path := path) hfired
    simpa [hstate] using hStep.enabled
  exact
    (not_badUnlessWriteIndex_of_enabledAt_phase_write
      (s := s) M hphase hEnabled) hbad

theorem fired_index_matches_phase_of_encoded_state
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {path : (FourPhaseMacroModule.network (s := s) M).Path}
    {c : MicroCfg Q s} {t : Nat}
    {i : (FourPhaseMacroModule.network (s := s) M).I}
    (hstate : path.state t = FourPhaseEncoding.enc c)
    (hfired : path.fired t = some i) :
    match c.state.phase with
    | Phase4.read => FourPhaseMacroModule.IsReadIndex (s := s) M i
    | Phase4.erase => FourPhaseMacroModule.IsEraseIndex (s := s) M i
    | Phase4.shift => FourPhaseMacroModule.IsShiftIndex (s := s) M i
    | Phase4.write => FourPhaseMacroModule.IsWriteIndex (s := s) M i := by
  have hEnabled :
      (FourPhaseMacroModule.network (s := s) M).EnabledAt
        (FourPhaseEncoding.enc c) i := by
    have hStep := Network.Path.stepAt_of_fired (path := path) hfired
    simpa [hstate] using hStep.enabled
  cases hphase : c.state.phase
  · exact enabledAt_isReadIndex_of_phase_read (s := s) M hphase hEnabled
  · exact enabledAt_isEraseIndex_of_phase_erase (s := s) M hphase hEnabled
  · exact enabledAt_isShiftIndex_of_phase_shift (s := s) M hphase hEnabled
  · exact enabledAt_isWriteIndex_of_phase_write (s := s) M hphase hEnabled

theorem not_offPhaseBadIndexSet_of_encoded_state_fired
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {path : (FourPhaseMacroModule.network (s := s) M).Path}
    {c : MicroCfg Q s} {t : Nat}
    {i : (FourPhaseMacroModule.network (s := s) M).I}
    (hstate : path.state t = FourPhaseEncoding.enc c)
    (hfired : path.fired t = some i) :
    Not (offPhaseBadIndexSet (s := s) M c i) := by
  have hEnabled :
      (FourPhaseMacroModule.network (s := s) M).EnabledAt
        (FourPhaseEncoding.enc c) i := by
    simpa [hstate] using
      (Network.Path.enabledAt_of_fired (path := path) hfired)
  exact not_offPhaseBadIndexSet_of_enabledAt_encoded
    (s := s) M hEnabled

theorem not_badFiresAt_offPhaseBadIndexSet_of_encoded_state
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {path : (FourPhaseMacroModule.network (s := s) M).Path}
    {c : MicroCfg Q s} {t : Nat}
    (hstate : path.state t = FourPhaseEncoding.enc c) :
    Not (path.BadFiresAt (offPhaseBadIndexSet (s := s) M c) t) := by
  cases hphase : c.state.phase
  · simpa [offPhaseBadIndexSet, hphase] using
      not_badFiresAt_badUnlessReadIndex_of_state_phase_read
        (s := s) M hstate hphase
  · simpa [offPhaseBadIndexSet, hphase] using
      not_badFiresAt_badUnlessEraseIndex_of_state_phase_erase
        (s := s) M hstate hphase
  · simpa [offPhaseBadIndexSet, hphase] using
      not_badFiresAt_badUnlessShiftIndex_of_state_phase_shift
        (s := s) M hstate hphase
  · simpa [offPhaseBadIndexSet, hphase] using
      not_badFiresAt_badUnlessWriteIndex_of_state_phase_write
        (s := s) M hstate hphase

theorem noBadFiresBefore_offPhaseBadIndexSet_singleton_of_encoded_state
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {path : (FourPhaseMacroModule.network (s := s) M).Path}
    {c : MicroCfg Q s} {t : Nat}
    (hstate : path.state t = FourPhaseEncoding.enc c) :
    path.NoBadFiresBefore
      (offPhaseBadIndexSet (s := s) M c) t (t + 1) :=
  (Network.Path.noBadFiresBefore_singleton_iff
    (path := path)
    (Bad := offPhaseBadIndexSet (s := s) M c)
    (t := t)).mpr
    (not_badFiresAt_offPhaseBadIndexSet_of_encoded_state
      (s := s) M hstate)

theorem not_badFiresAt_offPhaseBadIndexSet_of_encoded_state_same_phase
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {path : (FourPhaseMacroModule.network (s := s) M).Path}
    {c0 c : MicroCfg Q s} {t : Nat}
    (hstate : path.state t = FourPhaseEncoding.enc c)
    (hphase : c.state.phase = c0.state.phase) :
    Not (path.BadFiresAt (offPhaseBadIndexSet (s := s) M c0) t) := by
  cases hphase0 : c0.state.phase
  · have hc : c.state.phase = Phase4.read := by
      exact hphase.trans hphase0
    simpa [offPhaseBadIndexSet, hphase0] using
      not_badFiresAt_badUnlessReadIndex_of_state_phase_read
        (s := s) M hstate hc
  · have hc : c.state.phase = Phase4.erase := by
      exact hphase.trans hphase0
    simpa [offPhaseBadIndexSet, hphase0] using
      not_badFiresAt_badUnlessEraseIndex_of_state_phase_erase
        (s := s) M hstate hc
  · have hc : c.state.phase = Phase4.shift := by
      exact hphase.trans hphase0
    simpa [offPhaseBadIndexSet, hphase0] using
      not_badFiresAt_badUnlessShiftIndex_of_state_phase_shift
        (s := s) M hstate hc
  · have hc : c.state.phase = Phase4.write := by
      exact hphase.trans hphase0
    simpa [offPhaseBadIndexSet, hphase0] using
      not_badFiresAt_badUnlessWriteIndex_of_state_phase_write
        (s := s) M hstate hc

theorem noBadFiresBefore_offPhaseBadIndexSet_singleton_of_encoded_state_same_phase
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {path : (FourPhaseMacroModule.network (s := s) M).Path}
    {c0 c : MicroCfg Q s} {t : Nat}
    (hstate : path.state t = FourPhaseEncoding.enc c)
    (hphase : c.state.phase = c0.state.phase) :
    path.NoBadFiresBefore
      (offPhaseBadIndexSet (s := s) M c0) t (t + 1) :=
  (Network.Path.noBadFiresBefore_singleton_iff
    (path := path)
    (Bad := offPhaseBadIndexSet (s := s) M c0)
    (t := t)).mpr
    (not_badFiresAt_offPhaseBadIndexSet_of_encoded_state_same_phase
      (s := s) M hstate hphase)

theorem noBadFiresBefore_offPhaseBadIndexSet_of_forall_encoded_state_same_phase
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {path : (FourPhaseMacroModule.network (s := s) M).Path}
    {c0 : MicroCfg Q s} {t0 t1 : Nat}
    (hstate :
      forall t,
        t0 <= t -> t < t1 ->
          exists c : MicroCfg Q s,
            path.state t = FourPhaseEncoding.enc c /\
            c.state.phase = c0.state.phase) :
    path.NoBadFiresBefore
      (offPhaseBadIndexSet (s := s) M c0) t0 t1 := by
  apply Network.Path.noBadFiresBefore_of_forall_not_bad
  intro t i ht0 ht1 hfired hBad
  rcases hstate t ht0 ht1 with ⟨c, hc, hphase⟩
  exact
    (not_badFiresAt_offPhaseBadIndexSet_of_encoded_state_same_phase
      (s := s) M hc hphase) ⟨i, hfired, hBad⟩

theorem intendedWinsRaceAt_offPhaseBadIndexSet_of_firesIntendedContiguouslyAt_same_phase
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {path : (FourPhaseMacroModule.network (s := s) M).Path}
    {c0 : MicroCfg Q s} {t : Nat}
    {z0 z1 : State (FourPhaseSpecies Q)}
    (I :
      (FourPhaseMacroModule.network (s := s) M).IntendedSchedule z0 z1)
    (hfire : path.FiresIntendedContiguouslyAt t I)
    (hstate :
      forall u,
        t <= u -> u < t + I.schedule.length ->
          exists c : MicroCfg Q s,
            path.state u = FourPhaseEncoding.enc c /\
            c.state.phase = c0.state.phase) :
    path.IntendedWinsRaceAt
      (offPhaseBadIndexSet (s := s) M c0) t I :=
  ⟨hfire,
    noBadFiresBefore_offPhaseBadIndexSet_of_forall_encoded_state_same_phase
      (s := s) M hstate⟩

theorem intendedWinsRaceAt_offPhaseBadIndexSet_of_bounded_firesIntendedContiguouslyAt_same_phase
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {path : (FourPhaseMacroModule.network (s := s) M).Path}
    {c0 : MicroCfg Q s} {bound t : Nat}
    {z0 z1 : State (FourPhaseSpecies Q)}
    (I :
      (FourPhaseMacroModule.network (s := s) M).BoundedIntendedSchedule
        bound z0 z1)
    (hfire : path.FiresIntendedContiguouslyAt t I.toIntendedSchedule)
    (hstate :
      forall u,
        t <= u -> u < t + bound ->
          exists c : MicroCfg Q s,
            path.state u = FourPhaseEncoding.enc c /\
            c.state.phase = c0.state.phase) :
    path.IntendedWinsRaceAt
      (offPhaseBadIndexSet (s := s) M c0) t I.toIntendedSchedule :=
  Network.Path.intendedWinsRaceAt_of_bounded_noBadFiresBefore I hfire
    (noBadFiresBefore_offPhaseBadIndexSet_of_forall_encoded_state_same_phase
      (s := s) M hstate)

theorem noBadFiresBefore_badUnlessReadIndex_of_forall_state_phase_read
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {path : (FourPhaseMacroModule.network (s := s) M).Path}
    {t0 t1 : Nat}
    (hstate :
      forall t,
        t0 <= t -> t < t1 ->
          exists c : MicroCfg Q s,
            path.state t = FourPhaseEncoding.enc c /\
            c.state.phase = Phase4.read) :
    path.NoBadFiresBefore (badUnlessReadIndex (s := s) M) t0 t1 := by
  apply Network.Path.noBadFiresBefore_of_forall_not_bad
  intro t i ht0 ht1 hfired hBad
  rcases hstate t ht0 ht1 with ⟨c, hc, hphase⟩
  exact
    (not_badFiresAt_badUnlessReadIndex_of_state_phase_read
      (s := s) M hc hphase) ⟨i, hfired, hBad⟩

theorem noBadFiresBefore_badUnlessEraseIndex_of_forall_state_phase_erase
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {path : (FourPhaseMacroModule.network (s := s) M).Path}
    {t0 t1 : Nat}
    (hstate :
      forall t,
        t0 <= t -> t < t1 ->
          exists c : MicroCfg Q s,
            path.state t = FourPhaseEncoding.enc c /\
            c.state.phase = Phase4.erase) :
    path.NoBadFiresBefore (badUnlessEraseIndex (s := s) M) t0 t1 := by
  apply Network.Path.noBadFiresBefore_of_forall_not_bad
  intro t i ht0 ht1 hfired hBad
  rcases hstate t ht0 ht1 with ⟨c, hc, hphase⟩
  exact
    (not_badFiresAt_badUnlessEraseIndex_of_state_phase_erase
      (s := s) M hc hphase) ⟨i, hfired, hBad⟩

theorem noBadFiresBefore_badUnlessShiftIndex_of_forall_state_phase_shift
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {path : (FourPhaseMacroModule.network (s := s) M).Path}
    {t0 t1 : Nat}
    (hstate :
      forall t,
        t0 <= t -> t < t1 ->
          exists c : MicroCfg Q s,
            path.state t = FourPhaseEncoding.enc c /\
            c.state.phase = Phase4.shift) :
    path.NoBadFiresBefore (badUnlessShiftIndex (s := s) M) t0 t1 := by
  apply Network.Path.noBadFiresBefore_of_forall_not_bad
  intro t i ht0 ht1 hfired hBad
  rcases hstate t ht0 ht1 with ⟨c, hc, hphase⟩
  exact
    (not_badFiresAt_badUnlessShiftIndex_of_state_phase_shift
      (s := s) M hc hphase) ⟨i, hfired, hBad⟩

theorem noBadFiresBefore_badUnlessWriteIndex_of_forall_state_phase_write
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {path : (FourPhaseMacroModule.network (s := s) M).Path}
    {t0 t1 : Nat}
    (hstate :
      forall t,
        t0 <= t -> t < t1 ->
          exists c : MicroCfg Q s,
            path.state t = FourPhaseEncoding.enc c /\
            c.state.phase = Phase4.write) :
    path.NoBadFiresBefore (badUnlessWriteIndex (s := s) M) t0 t1 := by
  apply Network.Path.noBadFiresBefore_of_forall_not_bad
  intro t i ht0 ht1 hfired hBad
  rcases hstate t ht0 ht1 with ⟨c, hc, hphase⟩
  exact
    (not_badFiresAt_badUnlessWriteIndex_of_state_phase_write
      (s := s) M hc hphase) ⟨i, hfired, hBad⟩

end FourPhaseMacroSafety

end CTM

end Ripple.sCRNUniversality
