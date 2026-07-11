import Ripple.sCRNUniversality.Computation.CTM.FourPhaseMacroModule
import Ripple.sCRNUniversality.Computation.CTM.FourPhaseFootprint

namespace Ripple.sCRNUniversality

namespace CTM

namespace ReadNetwork

universe u

def localFootprint {Q : Type u} {M : Binary Q} (i : ReadIdx M) :
    FourPhaseSpecies Q -> Prop :=
  FourPhaseSpecies.IsLocalMacroFootprint
    (FourPhaseSpecies.ctrlOf (MicroState.readPhase (ReadIdx.q i)))
    (FourPhaseSpecies.ctrlOf
      (MicroState.afterRead (MicroState.readPhase (ReadIdx.q i))
        (ReadIdx.r i) (ReadIdx.w i) (ReadIdx.qNext i)))

theorem rxn_footprintWithin {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) (i : ReadIdx M) :
    ((network (s := s) M).rxn i).FootprintWithin
      (localFootprint i) := by
  simpa [network, localFootprint] using
    ReadGadget.reaction_footprintWithin (Q := Q) (s := s)
      (ReadIdx.q i) (ReadIdx.r i) (ReadIdx.w i) (ReadIdx.qNext i)

theorem scheduleFootprintWithin_singleton
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) (i : (network (s := s) M).I) :
    (network (s := s) M).ScheduleFootprintWithin [i]
      (localFootprint i) :=
  Network.scheduleFootprintWithin_singleton
    (rxn_footprintWithin (s := s) M i)

theorem stepAt_agreesOutside_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {i : (network (s := s) M).I} {z z' : State (FourPhaseSpecies Q)}
    (hStep : (network (s := s) M).StepAt i z z') :
    State.AgreesOutside (localFootprint i) z z' :=
  Network.StepAt.agreesOutside_of_footprintWithin hStep
    (rxn_footprintWithin (s := s) M i)

theorem scheduleFootprintWithin_of_forall_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {is : List (network (s := s) M).I}
    {P : FourPhaseSpecies Q -> Prop}
    (hSub :
      forall i, i ∈ is -> forall species,
        localFootprint i species -> P species) :
    (network (s := s) M).ScheduleFootprintWithin is P := by
  intro i hi species hTouches
  exact hSub i hi species
    ((rxn_footprintWithin (s := s) M i) species hTouches)

theorem exec_agreesOutside_of_forall_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {is : List (network (s := s) M).I}
    {z z' : State (FourPhaseSpecies Q)}
    {P : FourPhaseSpecies Q -> Prop}
    (hExec : (network (s := s) M).Exec z z' is)
    (hSub :
      forall i, i ∈ is -> forall species,
        localFootprint i species -> P species) :
    State.AgreesOutside P z z' :=
  Network.Exec.agreesOutside_of_scheduleFootprintWithin hExec
    (scheduleFootprintWithin_of_forall_local (s := s) M hSub)

end ReadNetwork

namespace EraseNetwork

universe u

def localFootprint {Q : Type u} (i : Idx Q) :
    FourPhaseSpecies Q -> Prop :=
  FourPhaseSpecies.IsLocalMacroFootprint
    (FourPhaseSpecies.ctrlOf
      (EraseGadget.sourceState i.q i.r i.w i.qNext))
    (FourPhaseSpecies.ctrlOf
      (EraseGadget.targetState i.q i.r i.w i.qNext))

theorem rxn_footprintWithin {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (i : Idx Q) :
    ((network Q s).rxn i).FootprintWithin
      (localFootprint i) := by
  simpa [network, localFootprint] using
    EraseGadget.reaction_footprintWithin (Q := Q) (s := s)
      i.q i.r i.w i.qNext

theorem scheduleFootprintWithin_singleton
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (i : (network Q s).I) :
    (network Q s).ScheduleFootprintWithin [i]
      (localFootprint i) :=
  Network.scheduleFootprintWithin_singleton
    (rxn_footprintWithin (Q := Q) (s := s) i)

theorem stepAt_agreesOutside_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} {i : (network Q s).I}
    {z z' : State (FourPhaseSpecies Q)}
    (hStep : (network Q s).StepAt i z z') :
    State.AgreesOutside (localFootprint i) z z' :=
  Network.StepAt.agreesOutside_of_footprintWithin hStep
    (rxn_footprintWithin (Q := Q) (s := s) i)

theorem scheduleFootprintWithin_of_forall_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} {is : List (network Q s).I}
    {P : FourPhaseSpecies Q -> Prop}
    (hSub :
      forall i, i ∈ is -> forall species,
        localFootprint i species -> P species) :
    (network Q s).ScheduleFootprintWithin is P := by
  intro i hi species hTouches
  exact hSub i hi species
    ((rxn_footprintWithin (Q := Q) (s := s) i) species hTouches)

theorem exec_agreesOutside_of_forall_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} {is : List (network Q s).I}
    {z z' : State (FourPhaseSpecies Q)}
    {P : FourPhaseSpecies Q -> Prop}
    (hExec : (network Q s).Exec z z' is)
    (hSub :
      forall i, i ∈ is -> forall species,
        localFootprint i species -> P species) :
    State.AgreesOutside P z z' :=
  Network.Exec.agreesOutside_of_scheduleFootprintWithin hExec
    (scheduleFootprintWithin_of_forall_local (Q := Q) (s := s) hSub)

end EraseNetwork

namespace ShiftGadget

universe u

def localFootprint {Q : Type u} {s : Nat} (i : Idx Q s) :
    FourPhaseSpecies Q -> Prop :=
  FourPhaseSpecies.IsLocalMacroFootprint
    (FourPhaseSpecies.ctrlOf
      (sourceState i.q i.r i.w i.qNext))
    (FourPhaseSpecies.ctrlOf
      (targetState i.q i.r i.w i.qNext))

theorem network_rxn_footprintWithin
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (i : Idx Q s) :
    ((network Q s).rxn i).FootprintWithin
      (localFootprint i) := by
  simpa [network, localFootprint] using
    ShiftGadget.reaction_footprintWithin (Q := Q) (s := s) i

theorem scheduleFootprintWithin_singleton
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (i : (network Q s).I) :
    (network Q s).ScheduleFootprintWithin [i]
      (localFootprint i) :=
  Network.scheduleFootprintWithin_singleton
    (network_rxn_footprintWithin (Q := Q) (s := s) i)

theorem stepAt_agreesOutside_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} {i : (network Q s).I}
    {z z' : State (FourPhaseSpecies Q)}
    (hStep : (network Q s).StepAt i z z') :
    State.AgreesOutside (localFootprint i) z z' :=
  Network.StepAt.agreesOutside_of_footprintWithin hStep
    (network_rxn_footprintWithin (Q := Q) (s := s) i)

theorem scheduleFootprintWithin_of_forall_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} {is : List (network Q s).I}
    {P : FourPhaseSpecies Q -> Prop}
    (hSub :
      forall i, i ∈ is -> forall species,
        localFootprint i species -> P species) :
    (network Q s).ScheduleFootprintWithin is P := by
  intro i hi species hTouches
  exact hSub i hi species
    ((network_rxn_footprintWithin (Q := Q) (s := s) i) species hTouches)

theorem exec_agreesOutside_of_forall_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} {is : List (network Q s).I}
    {z z' : State (FourPhaseSpecies Q)}
    {P : FourPhaseSpecies Q -> Prop}
    (hExec : (network Q s).Exec z z' is)
    (hSub :
      forall i, i ∈ is -> forall species,
        localFootprint i species -> P species) :
    State.AgreesOutside P z z' :=
  Network.Exec.agreesOutside_of_scheduleFootprintWithin hExec
    (scheduleFootprintWithin_of_forall_local (Q := Q) (s := s) hSub)

end ShiftGadget

namespace WriteNetwork

universe u

def localFootprint {Q : Type u} (i : Idx Q) :
    FourPhaseSpecies Q -> Prop :=
  FourPhaseSpecies.IsLocalMacroFootprint
    (FourPhaseSpecies.ctrlOf
      (WriteGadget.sourceState i.q i.r i.w i.qNext))
    (FourPhaseSpecies.ctrlOf
      (WriteGadget.targetState i.q i.r i.w i.qNext))

theorem rxn_footprintWithin {Q : Type u} [Fintype Q] [DecidableEq Q]
    (i : Idx Q) :
    ((network Q).rxn i).FootprintWithin
      (localFootprint i) := by
  simpa [network, localFootprint] using
    WriteGadget.reaction_footprintWithin (Q := Q)
      i.q i.r i.w i.qNext

theorem scheduleFootprintWithin_singleton
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    (i : (network Q).I) :
    (network Q).ScheduleFootprintWithin [i]
      (localFootprint i) :=
  Network.scheduleFootprintWithin_singleton
    (rxn_footprintWithin (Q := Q) i)

theorem stepAt_agreesOutside_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {i : (network Q).I}
    {z z' : State (FourPhaseSpecies Q)}
    (hStep : (network Q).StepAt i z z') :
    State.AgreesOutside (localFootprint i) z z' :=
  Network.StepAt.agreesOutside_of_footprintWithin hStep
    (rxn_footprintWithin (Q := Q) i)

theorem scheduleFootprintWithin_of_forall_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {is : List (network Q).I}
    {P : FourPhaseSpecies Q -> Prop}
    (hSub :
      forall i, i ∈ is -> forall species,
        localFootprint i species -> P species) :
    (network Q).ScheduleFootprintWithin is P := by
  intro i hi species hTouches
  exact hSub i hi species
    ((rxn_footprintWithin (Q := Q) i) species hTouches)

theorem exec_agreesOutside_of_forall_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {is : List (network Q).I}
    {z z' : State (FourPhaseSpecies Q)}
    {P : FourPhaseSpecies Q -> Prop}
    (hExec : (network Q).Exec z z' is)
    (hSub :
      forall i, i ∈ is -> forall species,
        localFootprint i species -> P species) :
    State.AgreesOutside P z z' :=
  Network.Exec.agreesOutside_of_scheduleFootprintWithin hExec
    (scheduleFootprintWithin_of_forall_local (Q := Q) hSub)

end WriteNetwork

namespace FourPhaseMacroModule

universe u

private theorem List.exists_eq_singleton_of_length_eq_one
    {α : Type u} {xs : List α}
    (h : xs.length = 1) :
    exists x : α, xs = [x] := by
  cases xs with
  | nil =>
      simp at h
  | cons x xs =>
      cases xs with
      | nil =>
          exact ⟨x, rfl⟩
      | cons y ys =>
          simp at h

def localFootprint {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (i : (network (s := s) M).I) :
    FourPhaseSpecies Q -> Prop :=
  match i with
  | Sum.inl (Sum.inl iRead) => ReadNetwork.localFootprint iRead
  | Sum.inl (Sum.inr iErase) => EraseNetwork.localFootprint iErase
  | Sum.inr (Sum.inl iShift) => ShiftGadget.localFootprint iShift
  | Sum.inr (Sum.inr iWrite) => WriteNetwork.localFootprint iWrite

theorem rxn_read_footprintWithin
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (i : (ReadNetwork.network (s := s) M).I) :
    ((network (s := s) M).rxn (Sum.inl (Sum.inl i))).FootprintWithin
      (ReadNetwork.localFootprint i) := by
  simpa [network, phaseParallel4] using
    ReadNetwork.rxn_footprintWithin (Q := Q) (s := s) M i

theorem rxn_erase_footprintWithin
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (i : (EraseNetwork.network Q s).I) :
    ((network (s := s) M).rxn (Sum.inl (Sum.inr i))).FootprintWithin
      (EraseNetwork.localFootprint i) := by
  simpa [network, phaseParallel4] using
    EraseNetwork.rxn_footprintWithin (Q := Q) (s := s) i

theorem rxn_shift_footprintWithin
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (i : (ShiftGadget.network Q s).I) :
    ((network (s := s) M).rxn (Sum.inr (Sum.inl i))).FootprintWithin
      (ShiftGadget.localFootprint i) := by
  simpa [network, phaseParallel4] using
    ShiftGadget.network_rxn_footprintWithin (Q := Q) (s := s) i

theorem rxn_write_footprintWithin
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (i : (WriteNetwork.network Q).I) :
    ((network (s := s) M).rxn (Sum.inr (Sum.inr i))).FootprintWithin
      (WriteNetwork.localFootprint i) := by
  simpa [network, phaseParallel4] using
    WriteNetwork.rxn_footprintWithin (Q := Q) i

theorem scheduleFootprintWithin_read_singleton
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (i : (ReadNetwork.network (s := s) M).I) :
    (network (s := s) M).ScheduleFootprintWithin
      [Sum.inl (Sum.inl i)]
      (ReadNetwork.localFootprint i) :=
  Network.scheduleFootprintWithin_singleton
    (rxn_read_footprintWithin (s := s) M i)

theorem scheduleFootprintWithin_erase_singleton
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (i : (EraseNetwork.network Q s).I) :
    (network (s := s) M).ScheduleFootprintWithin
      [Sum.inl (Sum.inr i)]
      (EraseNetwork.localFootprint i) :=
  Network.scheduleFootprintWithin_singleton
    (rxn_erase_footprintWithin (s := s) M i)

theorem scheduleFootprintWithin_shift_singleton
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (i : (ShiftGadget.network Q s).I) :
    (network (s := s) M).ScheduleFootprintWithin
      [Sum.inr (Sum.inl i)]
      (ShiftGadget.localFootprint i) :=
  Network.scheduleFootprintWithin_singleton
    (rxn_shift_footprintWithin (s := s) M i)

theorem scheduleFootprintWithin_write_singleton
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (i : (WriteNetwork.network Q).I) :
    (network (s := s) M).ScheduleFootprintWithin
      [Sum.inr (Sum.inr i)]
      (WriteNetwork.localFootprint i) :=
  Network.scheduleFootprintWithin_singleton
    (rxn_write_footprintWithin (s := s) M i)

theorem rxn_footprintWithin
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (i : (network (s := s) M).I) :
    ((network (s := s) M).rxn i).FootprintWithin
      (localFootprint M i) := by
  rcases i with (iRead | iErase) | (iShift | iWrite)
  · simpa [localFootprint] using
      rxn_read_footprintWithin (Q := Q) (s := s) M iRead
  · simpa [localFootprint] using
      rxn_erase_footprintWithin (Q := Q) (s := s) M iErase
  · simpa [localFootprint] using
      rxn_shift_footprintWithin (Q := Q) (s := s) M iShift
  · simpa [localFootprint] using
      rxn_write_footprintWithin (Q := Q) (s := s) M iWrite

theorem stepAt_agreesOutside_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {i : (network (s := s) M).I}
    {z z' : State (FourPhaseSpecies Q)}
    (hStep : (network (s := s) M).StepAt i z z') :
    State.AgreesOutside (localFootprint M i) z z' :=
  Network.StepAt.agreesOutside_of_footprintWithin hStep
    (rxn_footprintWithin (s := s) M i)

theorem stepAt_read_agreesOutside_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {i : (ReadNetwork.network (s := s) M).I}
    {z z' : State (FourPhaseSpecies Q)}
    (hStep :
      (network (s := s) M).StepAt (Sum.inl (Sum.inl i)) z z') :
    State.AgreesOutside (ReadNetwork.localFootprint i) z z' :=
  Network.StepAt.agreesOutside_of_footprintWithin hStep
    (rxn_read_footprintWithin (s := s) M i)

theorem stepAt_erase_agreesOutside_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {i : (EraseNetwork.network Q s).I}
    {z z' : State (FourPhaseSpecies Q)}
    (hStep :
      (network (s := s) M).StepAt (Sum.inl (Sum.inr i)) z z') :
    State.AgreesOutside (EraseNetwork.localFootprint i) z z' :=
  Network.StepAt.agreesOutside_of_footprintWithin hStep
    (rxn_erase_footprintWithin (s := s) M i)

theorem stepAt_shift_agreesOutside_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {i : (ShiftGadget.network Q s).I}
    {z z' : State (FourPhaseSpecies Q)}
    (hStep :
      (network (s := s) M).StepAt (Sum.inr (Sum.inl i)) z z') :
    State.AgreesOutside (ShiftGadget.localFootprint i) z z' :=
  Network.StepAt.agreesOutside_of_footprintWithin hStep
    (rxn_shift_footprintWithin (s := s) M i)

theorem stepAt_write_agreesOutside_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {i : (WriteNetwork.network Q).I}
    {z z' : State (FourPhaseSpecies Q)}
    (hStep :
      (network (s := s) M).StepAt (Sum.inr (Sum.inr i)) z z') :
    State.AgreesOutside (WriteNetwork.localFootprint i) z z' :=
  Network.StepAt.agreesOutside_of_footprintWithin hStep
    (rxn_write_footprintWithin (s := s) M i)

theorem execFootprintWithin_of_stepAt
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {i : (network (s := s) M).I}
    {z z' : State (FourPhaseSpecies Q)}
    (hStep : (network (s := s) M).StepAt i z z') :
    (network (s := s) M).ExecFootprintWithin
      (localFootprint M i) z z' :=
  Network.ExecFootprintWithin.of_exec_scheduleFootprintWithin
    (ExecOf.cons hStep (ExecOf.nil z'))
    (Network.scheduleFootprintWithin_singleton
      (rxn_footprintWithin (s := s) M i))

theorem execFootprintWithin_read_of_stepAt
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {i : (ReadNetwork.network (s := s) M).I}
    {z z' : State (FourPhaseSpecies Q)}
    (hStep :
      (network (s := s) M).StepAt (Sum.inl (Sum.inl i)) z z') :
    (network (s := s) M).ExecFootprintWithin
      (ReadNetwork.localFootprint i) z z' := by
  simpa [localFootprint] using
    execFootprintWithin_of_stepAt (s := s) M hStep

theorem execFootprintWithin_erase_of_stepAt
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {i : (EraseNetwork.network Q s).I}
    {z z' : State (FourPhaseSpecies Q)}
    (hStep :
      (network (s := s) M).StepAt (Sum.inl (Sum.inr i)) z z') :
    (network (s := s) M).ExecFootprintWithin
      (EraseNetwork.localFootprint i) z z' := by
  simpa [localFootprint] using
    execFootprintWithin_of_stepAt (s := s) M hStep

theorem execFootprintWithin_shift_of_stepAt
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {i : (ShiftGadget.network Q s).I}
    {z z' : State (FourPhaseSpecies Q)}
    (hStep :
      (network (s := s) M).StepAt (Sum.inr (Sum.inl i)) z z') :
    (network (s := s) M).ExecFootprintWithin
      (ShiftGadget.localFootprint i) z z' := by
  simpa [localFootprint] using
    execFootprintWithin_of_stepAt (s := s) M hStep

theorem execFootprintWithin_write_of_stepAt
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {i : (WriteNetwork.network Q).I}
    {z z' : State (FourPhaseSpecies Q)}
    (hStep :
      (network (s := s) M).StepAt (Sum.inr (Sum.inr i)) z z') :
    (network (s := s) M).ExecFootprintWithin
      (WriteNetwork.localFootprint i) z z' := by
  simpa [localFootprint] using
    execFootprintWithin_of_stepAt (s := s) M hStep

theorem exists_phaseIndex_singleton_exec_of_phaseStep?
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    exists i : (network (s := s) M).I,
      (match c.state.phase with
        | Phase4.read => IsReadIndex (s := s) M i
        | Phase4.erase => IsEraseIndex (s := s) M i
        | Phase4.shift => IsShiftIndex (s := s) M i
        | Phase4.write => IsWriteIndex (s := s) M i) /\
        (network (s := s) M).Exec
          (FourPhaseEncoding.enc c)
          (FourPhaseEncoding.enc c') [i] := by
  cases hphase : c.state.phase with
  | read =>
      rcases ReadNetwork.exec_of_phaseStep?_read
          (s := s) M hc.1 hphase hstep with
        ⟨is, hExec, hLen⟩
      rcases List.exists_eq_singleton_of_length_eq_one hLen with
        ⟨i, his⟩
      subst his
      refine ⟨Sum.inl (Sum.inl i), ?_, ?_⟩
      · exact ⟨i, rfl⟩
      · simpa [network, phaseParallel4] using
          phaseParallel4_exec_read
            (Nerase := EraseNetwork.network Q s)
            (Nshift := ShiftGadget.network Q s)
            (Nwrite := WriteNetwork.network Q)
            hExec
  | erase =>
      rcases EraseNetwork.exec_of_phaseStep?_erase
          (s := s) M hc hphase hstep with
        ⟨is, hExec, hLen⟩
      rcases List.exists_eq_singleton_of_length_eq_one hLen with
        ⟨i, his⟩
      subst his
      refine ⟨Sum.inl (Sum.inr i), ?_, ?_⟩
      · exact ⟨i, rfl⟩
      · simpa [network, phaseParallel4] using
          phaseParallel4_exec_erase
            (Nread := ReadNetwork.network (s := s) M)
            (Nshift := ShiftGadget.network Q s)
            (Nwrite := WriteNetwork.network Q)
            hExec
  | shift =>
      rcases ShiftNetwork.exec_of_phaseStep?_shift
          (s := s) M hc hphase hstep with
        ⟨is, hExec, hLen⟩
      rcases List.exists_eq_singleton_of_length_eq_one hLen with
        ⟨i, his⟩
      subst his
      refine ⟨Sum.inr (Sum.inl i), ?_, ?_⟩
      · exact ⟨i, rfl⟩
      · simpa [network, phaseParallel4] using
          phaseParallel4_exec_shift
            (Nread := ReadNetwork.network (s := s) M)
            (Nerase := EraseNetwork.network Q s)
            (Nwrite := WriteNetwork.network Q)
            hExec
  | write =>
      rcases WriteNetwork.exec_of_phaseStep?_write
          (s := s) M hc hphase hstep with
        ⟨is, hExec, hLen⟩
      rcases List.exists_eq_singleton_of_length_eq_one hLen with
        ⟨i, his⟩
      subst his
      refine ⟨Sum.inr (Sum.inr i), ?_, ?_⟩
      · exact ⟨i, rfl⟩
      · simpa [network, phaseParallel4] using
          phaseParallel4_exec_write
            (Nread := ReadNetwork.network (s := s) M)
            (Nerase := EraseNetwork.network Q s)
            (Nshift := ShiftGadget.network Q s)
            hExec

theorem exists_phaseIndex_execFootprintWithin_of_phaseStep?
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    exists i : (network (s := s) M).I,
      (match c.state.phase with
        | Phase4.read => IsReadIndex (s := s) M i
        | Phase4.erase => IsEraseIndex (s := s) M i
        | Phase4.shift => IsShiftIndex (s := s) M i
        | Phase4.write => IsWriteIndex (s := s) M i) /\
        (network (s := s) M).ExecFootprintWithin
          (localFootprint M i)
          (FourPhaseEncoding.enc c)
          (FourPhaseEncoding.enc c') := by
  rcases exists_phaseIndex_singleton_exec_of_phaseStep?
      (s := s) M hc hstep with
    ⟨i, hPhase, hExec⟩
  exact ⟨i, hPhase,
    Network.ExecFootprintWithin.of_exec_scheduleFootprintWithin hExec
      (Network.scheduleFootprintWithin_singleton
        (rxn_footprintWithin (s := s) M i))⟩

theorem scheduleFootprintWithin_of_forall_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {is : List (network (s := s) M).I}
    {P : FourPhaseSpecies Q -> Prop}
    (hSub :
      forall i, i ∈ is -> forall species,
        localFootprint M i species -> P species) :
    (network (s := s) M).ScheduleFootprintWithin is P := by
  intro i hi species hTouches
  exact hSub i hi species
    ((rxn_footprintWithin (s := s) M i) species hTouches)

theorem execFootprintWithin_of_exec_forall_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {is : List (network (s := s) M).I}
    {z z' : State (FourPhaseSpecies Q)}
    {P : FourPhaseSpecies Q -> Prop}
    (hExec : (network (s := s) M).Exec z z' is)
    (hSub :
      forall i, i ∈ is -> forall species,
        localFootprint M i species -> P species) :
    (network (s := s) M).ExecFootprintWithin P z z' :=
  Network.ExecFootprintWithin.of_exec_scheduleFootprintWithin hExec
    (scheduleFootprintWithin_of_forall_local (s := s) M hSub)

theorem exec_agreesOutside_of_forall_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {is : List (network (s := s) M).I}
    {z z' : State (FourPhaseSpecies Q)}
    {P : FourPhaseSpecies Q -> Prop}
    (hExec : (network (s := s) M).Exec z z' is)
    (hSub :
      forall i, i ∈ is -> forall species,
        localFootprint M i species -> P species) :
    State.AgreesOutside P z z' :=
  Network.Exec.agreesOutside_of_scheduleFootprintWithin hExec
    (scheduleFootprintWithin_of_forall_local (s := s) M hSub)

/--
The footprint induced by the actual macro schedule.

A species is in this footprint iff it is in the local footprint of some reaction
index appearing in the schedule. This is a deterministic schedule certificate;
it is not a global network footprint claim.
-/
def scheduleLocalFootprint
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (is : List (network (s := s) M).I) :
    FourPhaseSpecies Q -> Prop :=
  fun species =>
    exists i, i ∈ is /\ localFootprint M i species

theorem scheduleFootprintWithin_scheduleLocalFootprint
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (is : List (network (s := s) M).I) :
    (network (s := s) M).ScheduleFootprintWithin is
      (scheduleLocalFootprint M is) := by
  intro i hi species hTouches
  exact ⟨i, hi,
    (rxn_footprintWithin (s := s) M i) species hTouches⟩

theorem execFootprintWithin_of_exec_scheduleLocalFootprint
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {is : List (network (s := s) M).I}
    {z z' : State (FourPhaseSpecies Q)}
    (hExec : (network (s := s) M).Exec z z' is) :
    (network (s := s) M).ExecFootprintWithin
      (scheduleLocalFootprint M is) z z' :=
  Network.ExecFootprintWithin.of_exec_scheduleFootprintWithin hExec
    (scheduleFootprintWithin_scheduleLocalFootprint (s := s) M is)

theorem exec_agreesOutside_of_exec_scheduleLocalFootprint
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {is : List (network (s := s) M).I}
    {z z' : State (FourPhaseSpecies Q)}
    (hExec : (network (s := s) M).Exec z z' is) :
    State.AgreesOutside (scheduleLocalFootprint M is) z z' :=
  Network.Exec.agreesOutside_of_scheduleFootprintWithin hExec
    (scheduleFootprintWithin_scheduleLocalFootprint (s := s) M is)

/--
One successful four-phase micro-step has a deterministic macro execution whose
footprint is certified by the actual schedule's local footprints.
-/
theorem execFootprintWithin_of_phaseStep
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    exists is : List (network (s := s) M).I,
      (network (s := s) M).Exec
        (FourPhaseEncoding.enc c)
        (FourPhaseEncoding.enc c') is /\
      (network (s := s) M).ExecFootprintWithin
        (scheduleLocalFootprint M is)
        (FourPhaseEncoding.enc c)
        (FourPhaseEncoding.enc c') /\
      is.length <= 1 := by
  rcases (boundedModule (s := s) M).step_exec_bounded hc hstep with
    ⟨is, hExec, hLen⟩
  exact ⟨is, hExec,
    execFootprintWithin_of_exec_scheduleLocalFootprint (s := s) M hExec,
    by simpa [boundedModule] using hLen⟩

/--
One successful four-phase micro-step has footprint within any predicate `P`
containing all macro local footprints.
-/
theorem execFootprintWithin_of_phaseStep_within
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s}
    {P : FourPhaseSpecies Q -> Prop}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hSub :
      forall i : (network (s := s) M).I,
        forall species, localFootprint M i species -> P species) :
    (network (s := s) M).ExecFootprintWithin P
      (FourPhaseEncoding.enc c)
      (FourPhaseEncoding.enc c') := by
  rcases (module (s := s) M).step_exec hc hstep with ⟨is, hExec⟩
  exact execFootprintWithin_of_exec_forall_local (s := s) M hExec
    (by
      intro i _hi species hLocal
      exact hSub i species hLocal)

/--
One successful four-phase micro-step preserves every species outside any
predicate containing all macro local footprints.
-/
theorem phaseStep_agreesOutside_of_forall_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s}
    {P : FourPhaseSpecies Q -> Prop}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hSub :
      forall i : (network (s := s) M).I,
        forall species, localFootprint M i species -> P species) :
    State.AgreesOutside P
      (FourPhaseEncoding.enc c)
      (FourPhaseEncoding.enc c') :=
  Network.ExecFootprintWithin.agreesOutside
    (execFootprintWithin_of_phaseStep_within (s := s) M hc hstep hSub)

theorem phaseStep_coord_eq_of_forall_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s}
    {P : FourPhaseSpecies Q -> Prop}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hSub :
      forall i : (network (s := s) M).I,
        forall species, localFootprint M i species -> P species)
    {species : FourPhaseSpecies Q}
    (hnot : Not (P species)) :
    FourPhaseEncoding.enc c' species =
      FourPhaseEncoding.enc c species :=
  (phaseStep_agreesOutside_of_forall_local
    (s := s) M hc hstep hSub).coord hnot

theorem phaseStep_eqOn_of_forall_local_within_disjoint
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s}
    {P Protected : FourPhaseSpecies Q -> Prop}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hSub :
      forall i : (network (s := s) M).I,
        forall species, localFootprint M i species -> P species)
    (hDisjoint :
      forall species, P species -> Protected species -> False) :
    State.EqOn Protected
      (FourPhaseEncoding.enc c')
      (FourPhaseEncoding.enc c) :=
  Network.ExecFootprintWithin.eqOn_of_disjoint
    (execFootprintWithin_of_phaseStep_within
      (s := s) M hc hstep hSub)
    hDisjoint

theorem phaseStep_eqOn_of_forall_local_disjoint
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s}
    {Protected : FourPhaseSpecies Q -> Prop}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c')
    (hDisjoint :
      forall i : (network (s := s) M).I,
        forall species,
          localFootprint M i species -> Protected species -> False) :
    State.EqOn Protected
      (FourPhaseEncoding.enc c')
      (FourPhaseEncoding.enc c) :=
  phaseStep_eqOn_of_forall_local_within_disjoint
    (s := s) M hc hstep
    (P := fun species =>
      exists i : (network (s := s) M).I, localFootprint M i species)
    (by
      intro i species hLocal
      exact ⟨i, hLocal⟩)
    (by
      intro species hLocal hProtected
      rcases hLocal with ⟨i, hLocal⟩
      exact hDisjoint i species hLocal hProtected)

/--
One CTM step has a deterministic macro execution with certified local schedule
footprint and firing count at most `4`.
-/
theorem execFootprintWithin_of_ctm_step
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (hstep : M.step? cfg = some cfg') :
    exists is : List (network (s := s) M).I,
      (network (s := s) M).Exec
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) is /\
      (network (s := s) M).ExecFootprintWithin
        (scheduleLocalFootprint M is)
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) /\
      is.length <= 4 := by
  have hsteps :
      (M.detSystem (s := s)).steps? 1 cfg = some cfg' :=
    DetSystem.steps?_one_of_step? (M.detSystem (s := s)) hstep
  rcases exec_of_ctm_steps_bounded (s := s) M hsteps with
    ⟨is, hExec, hLen⟩
  exact ⟨is, hExec,
    execFootprintWithin_of_exec_scheduleLocalFootprint (s := s) M hExec,
    by simpa using hLen⟩

/--
One CTM step has footprint within any predicate `P` containing all macro local
footprints.
-/
theorem execFootprintWithin_of_ctm_step_within
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {P : FourPhaseSpecies Q -> Prop}
    (hstep : M.step? cfg = some cfg')
    (hSub :
      forall i : (network (s := s) M).I,
        forall species, localFootprint M i species -> P species) :
    (network (s := s) M).ExecFootprintWithin P
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) := by
  have hsteps :
      (M.detSystem (s := s)).steps? 1 cfg = some cfg' :=
    DetSystem.steps?_one_of_step? (M.detSystem (s := s)) hstep
  rcases exec_of_ctm_steps (s := s) M hsteps with ⟨is, hExec⟩
  exact execFootprintWithin_of_exec_forall_local (s := s) M hExec
    (by
      intro i _hi species hLocal
      exact hSub i species hLocal)

/--
One CTM step preserves every species outside any predicate containing all macro
local footprints.
-/
theorem ctm_step_agreesOutside_of_forall_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {P : FourPhaseSpecies Q -> Prop}
    (hstep : M.step? cfg = some cfg')
    (hSub :
      forall i : (network (s := s) M).I,
        forall species, localFootprint M i species -> P species) :
    State.AgreesOutside P
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) :=
  Network.ExecFootprintWithin.agreesOutside
    (execFootprintWithin_of_ctm_step_within (s := s) M hstep hSub)

theorem ctm_step_coord_eq_of_forall_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {P : FourPhaseSpecies Q -> Prop}
    (hstep : M.step? cfg = some cfg')
    (hSub :
      forall i : (network (s := s) M).I,
        forall species, localFootprint M i species -> P species)
    {species : FourPhaseSpecies Q}
    (hnot : Not (P species)) :
    FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species =
      FourPhaseEncoding.enc (MicroCfg.ofCTM cfg) species :=
  (ctm_step_agreesOutside_of_forall_local
    (s := s) M hstep hSub).coord hnot

theorem ctm_step_eqOn_of_forall_local_within_disjoint
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {P Protected : FourPhaseSpecies Q -> Prop}
    (hstep : M.step? cfg = some cfg')
    (hSub :
      forall i : (network (s := s) M).I,
        forall species, localFootprint M i species -> P species)
    (hDisjoint :
      forall species, P species -> Protected species -> False) :
    State.EqOn Protected
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg)) :=
  Network.ExecFootprintWithin.eqOn_of_disjoint
    (execFootprintWithin_of_ctm_step_within
      (s := s) M hstep hSub)
    hDisjoint

/--
`n` CTM steps have a deterministic macro execution with certified local schedule
footprint and firing count at most `4 * n`.
-/
theorem execFootprintWithin_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (hsteps : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists is : List (network (s := s) M).I,
      (network (s := s) M).Exec
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) is /\
      (network (s := s) M).ExecFootprintWithin
        (scheduleLocalFootprint M is)
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) /\
      is.length <= 4 * n := by
  rcases exec_of_ctm_steps_bounded (s := s) M hsteps with
    ⟨is, hExec, hLen⟩
  exact ⟨is, hExec,
    execFootprintWithin_of_exec_scheduleLocalFootprint (s := s) M hExec,
    hLen⟩

/--
`n` CTM steps have a deterministic macro execution whose final encoded state
agrees with the initial encoded state outside that schedule's local footprint.
-/
theorem exists_ctm_steps_frame_of_scheduleLocalFootprint
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (hsteps : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists is : List (network (s := s) M).I,
      (network (s := s) M).Exec
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) is /\
      (forall species : FourPhaseSpecies Q,
        Not (scheduleLocalFootprint M is species) ->
          FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species =
            FourPhaseEncoding.enc (MicroCfg.ofCTM cfg) species) /\
      is.length <= 4 * n := by
  rcases execFootprintWithin_of_ctm_steps (s := s) M hsteps with
    ⟨is, hExec, hFoot, hLen⟩
  refine ⟨is, hExec, ?_, hLen⟩
  intro species hnot
  exact hFoot.coord_eq hnot

/--
`n` CTM steps have footprint within any predicate `P` containing all macro local
footprints.
-/
theorem execFootprintWithin_of_ctm_steps_within
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {P : FourPhaseSpecies Q -> Prop}
    (hsteps : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hSub :
      forall i : (network (s := s) M).I,
        forall species, localFootprint M i species -> P species) :
    (network (s := s) M).ExecFootprintWithin P
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) := by
  rcases exec_of_ctm_steps (s := s) M hsteps with ⟨is, hExec⟩
  exact execFootprintWithin_of_exec_forall_local (s := s) M hExec
    (by
      intro i _hi species hLocal
      exact hSub i species hLocal)

/--
`n` CTM steps preserve every species outside any predicate containing all macro
local footprints.
-/
theorem ctm_steps_agreesOutside_of_forall_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {P : FourPhaseSpecies Q -> Prop}
    (hsteps : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hSub :
      forall i : (network (s := s) M).I,
        forall species, localFootprint M i species -> P species) :
    State.AgreesOutside P
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) :=
  Network.ExecFootprintWithin.agreesOutside
    (execFootprintWithin_of_ctm_steps_within (s := s) M hsteps hSub)

theorem ctm_steps_coord_eq_of_forall_local
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {P : FourPhaseSpecies Q -> Prop}
    (hsteps : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hSub :
      forall i : (network (s := s) M).I,
        forall species, localFootprint M i species -> P species)
    {species : FourPhaseSpecies Q}
    (hnot : Not (P species)) :
    FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species =
      FourPhaseEncoding.enc (MicroCfg.ofCTM cfg) species :=
  (ctm_steps_agreesOutside_of_forall_local
    (s := s) M hsteps hSub).coord hnot

theorem ctm_steps_eqOn_of_forall_local_within_disjoint
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {P Protected : FourPhaseSpecies Q -> Prop}
    (hsteps : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hSub :
      forall i : (network (s := s) M).I,
        forall species, localFootprint M i species -> P species)
    (hDisjoint :
      forall species, P species -> Protected species -> False) :
    State.EqOn Protected
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg)) :=
  Network.ExecFootprintWithin.eqOn_of_disjoint
    (execFootprintWithin_of_ctm_steps_within
      (s := s) M hsteps hSub)
    hDisjoint

/--
`n` CTM steps preserve every protected species if every possible macro local
footprint is disjoint from the protected predicate.
-/
theorem ctm_steps_eqOn_of_forall_local_disjoint
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {Protected : FourPhaseSpecies Q -> Prop}
    (hsteps : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hDisjoint :
      forall i : (network (s := s) M).I,
        forall species,
          localFootprint M i species -> Protected species -> False) :
    State.EqOn Protected
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg)) := by
  rcases execFootprintWithin_of_ctm_steps (s := s) M hsteps with
    ⟨is, _hExec, hFoot, _hLen⟩
  rcases hFoot with ⟨js, hExec, hSchedFoot⟩
  exact Network.Exec.eqOn_of_scheduleTouchesOnly_disjoint hExec hSchedFoot
    (by
      intro species hSchedLocal hProtected
      rcases hSchedLocal with ⟨i, _hi, hLocal⟩
      exact hDisjoint i species hLocal hProtected)

/--
One CTM step preserves every protected species if every possible macro local
footprint is disjoint from the protected predicate.
-/
theorem ctm_step_eqOn_of_forall_local_disjoint
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {Protected : FourPhaseSpecies Q -> Prop}
    (hstep : M.step? cfg = some cfg')
    (hDisjoint :
      forall i : (network (s := s) M).I,
        forall species,
          localFootprint M i species -> Protected species -> False) :
    State.EqOn Protected
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg)) := by
  have hsteps :
      (M.detSystem (s := s)).steps? 1 cfg = some cfg' :=
    DetSystem.steps?_one_of_step? (M.detSystem (s := s)) hstep
  exact ctm_steps_eqOn_of_forall_local_disjoint
    (s := s) (n := 1) M hsteps hDisjoint

end FourPhaseMacroModule

end CTM

end Ripple.sCRNUniversality
