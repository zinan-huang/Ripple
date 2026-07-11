/-
  Extended four-phase species type with cascade shift support.

  Adds tapeShifted (M† in the paper) and cascade shift sub-phase
  control tokens to the existing FourPhaseSpecies.

  The cascade shift replaces the finite-table ShiftGadget:
  instead of one reaction per tail value (with spurious enabledness),
  uses per-molecule M → 3M† tripling (fully deterministic).
-/
import Ripple.sCRNUniversality.Computation.CTM.FourPhaseMacroModule

namespace Ripple.sCRNUniversality.CTM

universe u

inductive ShiftSubPhase
  | multA | multB | multC | multBarA | multBarB | restore
deriving DecidableEq, Repr, Fintype

inductive CascadeSpecies (Q : Type u) where
  | ctrl :
      Q → Phase4 → Option Bool → Option Bool → Option Q →
      CascadeSpecies Q
  | shiftCtrl : ShiftSubPhase → CascadeSpecies Q
  | tape : CascadeSpecies Q
  | tapeBar : CascadeSpecies Q
  | tapeShifted : CascadeSpecies Q
deriving DecidableEq, Repr, Fintype

namespace CascadeSpecies

variable {Q : Type u} [DecidableEq Q]

def ofFourPhase : FourPhaseSpecies Q → CascadeSpecies Q
  | .ctrl q p r w s => .ctrl q p r w s
  | .tape => .tape
  | .tapeBar => .tapeBar

theorem ofFourPhase_injective : Function.Injective (ofFourPhase (Q := Q)) := by
  intro a b h
  cases a <;> cases b <;> simp [ofFourPhase] at h
  · obtain ⟨h1, h2, h3, h4, h5⟩ := h; subst h1; subst h2; subst h3; subst h4; subst h5; rfl
  · rfl
  · rfl

def ctrlOf (st : MicroState Q) : CascadeSpecies Q :=
  .ctrl st.q st.phase st.readSymbol st.pendingWrite st.pendingState

theorem ctrlOf_eq_ofFourPhase_ctrlOf (st : MicroState Q) :
    ctrlOf st = ofFourPhase (FourPhaseSpecies.ctrlOf st) := by
  rfl

end CascadeSpecies

namespace CascadeShiftReactions

variable {Q : Type u} [DecidableEq Q]

open CascadeSpecies in
def rxnMultA (st : MicroState Q) : Reaction (CascadeSpecies Q) where
  l := fun | ctrl q p r w s => if ctrl q p r w s = ctrlOf st then 1 else 0
           | tape => 1
           | _ => 0
  r := fun | shiftCtrl .multB => 1 | tapeShifted => 1 | _ => 0
  k := 1

open CascadeSpecies in
def rxnMultB : Reaction (CascadeSpecies Q) where
  l := fun | shiftCtrl .multB => 1 | _ => 0
  r := fun | shiftCtrl .multC => 1 | tapeShifted => 1 | _ => 0
  k := 1

open CascadeSpecies in
def rxnMultC : Reaction (CascadeSpecies Q) where
  l := fun | shiftCtrl .multC => 1 | _ => 0
  r := fun | shiftCtrl .multBarA => 1 | tapeShifted => 1 | _ => 0
  k := 1

open CascadeSpecies in
def rxnMultBarA : Reaction (CascadeSpecies Q) where
  l := fun | shiftCtrl .multBarA => 1 | tapeBar => 1 | _ => 0
  r := fun | shiftCtrl .multBarB => 1 | _ => 0
  k := 1

open CascadeSpecies in
def rxnMultBarB : Reaction (CascadeSpecies Q) where
  l := fun | shiftCtrl .multBarB => 1 | tapeBar => 1 | _ => 0
  r := fun | shiftCtrl .multA => 1 | _ => 0
  k := 1

open CascadeSpecies in
def rxnMultA_cont : Reaction (CascadeSpecies Q) where
  l := fun | shiftCtrl .multA => 1 | tape => 1 | _ => 0
  r := fun | shiftCtrl .multB => 1 | tapeShifted => 1 | _ => 0
  k := 1

open CascadeSpecies in
def rxnRestore : Reaction (CascadeSpecies Q) where
  l := fun | shiftCtrl .restore => 1 | tapeShifted => 1 | _ => 0
  r := fun | shiftCtrl .restore => 1 | tape => 1 | _ => 0
  k := 1

open CascadeSpecies in
def rxnShiftDone (st : MicroState Q) : Reaction (CascadeSpecies Q) where
  l := fun | shiftCtrl .multA => 1 | _ => 0
  r := fun | ctrl q p r w s =>
              if ctrl q p r w s = ctrlOf (MicroState.afterShift st) then 1 else 0
           | _ => 0
  k := 1

open CascadeSpecies in
def rxnRestoreInit : Reaction (CascadeSpecies Q) where
  l := fun | shiftCtrl .multA => 1 | _ => 0
  r := fun | shiftCtrl .restore => 1 | _ => 0
  k := 1

open CascadeSpecies in
def rxnRestoreDone (st : MicroState Q) : Reaction (CascadeSpecies Q) where
  l := fun | shiftCtrl .restore => 1 | _ => 0
  r := fun | ctrl q p r w s =>
              if ctrl q p r w s = ctrlOf (MicroState.afterShift st) then 1 else 0
           | _ => 0
  k := 1

open CascadeSpecies in
def rxnBypass (st : MicroState Q) : Reaction (CascadeSpecies Q) where
  l := fun | ctrl q p r w s => if ctrl q p r w s = ctrlOf st then 1 else 0
           | _ => 0
  r := fun | ctrl q p r w s =>
              if ctrl q p r w s = ctrlOf (MicroState.afterShift st) then 1 else 0
           | _ => 0
  k := 1

end CascadeShiftReactions

namespace CascadeMacroModule

variable {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}

def liftedReadNetwork (M : Binary Q) : Network (CascadeSpecies Q) :=
  Network.embed CascadeSpecies.ofFourPhase (ReadNetwork.network (s := s) M)

def liftedEraseNetwork : Network (CascadeSpecies Q) :=
  Network.embed CascadeSpecies.ofFourPhase (EraseNetwork.network Q s)

def liftedWriteNetwork : Network (CascadeSpecies Q) :=
  Network.embed CascadeSpecies.ofFourPhase (WriteNetwork.network Q)

theorem liftedReadNetwork_allUnitRate (M : Binary Q) :
    (liftedReadNetwork (s := s) M).allUnitRate := by
  intro i; exact ReadNetwork.network_allUnitRate (s := s) M i

theorem liftedEraseNetwork_allUnitRate :
    (liftedEraseNetwork (Q := Q) (s := s)).allUnitRate := by
  intro i; exact EraseNetwork.network_allUnitRate (Q := Q) s i

theorem liftedWriteNetwork_allUnitRate :
    (liftedWriteNetwork (Q := Q)).allUnitRate := by
  intro i; exact WriteNetwork.network_allUnitRate Q i

/-- Index type for the cascade shift network. -/
inductive CascadeShiftIdx (Q : Type u) where
  | initiate : EraseNetwork.Idx Q → CascadeShiftIdx Q
  | cont : CascadeShiftIdx Q
  | multB : CascadeShiftIdx Q
  | multC : CascadeShiftIdx Q
  | multBarA : CascadeShiftIdx Q
  | multBarB : CascadeShiftIdx Q
  | restoreInit : CascadeShiftIdx Q
  | restore : CascadeShiftIdx Q
  | restoreDone : EraseNetwork.Idx Q → CascadeShiftIdx Q
  | done : EraseNetwork.Idx Q → CascadeShiftIdx Q
  | bypass : EraseNetwork.Idx Q → CascadeShiftIdx Q
deriving DecidableEq, Repr, Fintype

def cascadeShiftNetwork : Network (CascadeSpecies Q) where
  I := CascadeShiftIdx Q
  fintypeI := inferInstance
  rxn := fun
    | .initiate i =>
        CascadeShiftReactions.rxnMultA
          (ShiftGadget.sourceState i.q i.r i.w i.qNext)
    | .cont => CascadeShiftReactions.rxnMultA_cont
    | .multB => CascadeShiftReactions.rxnMultB
    | .multC => CascadeShiftReactions.rxnMultC
    | .multBarA => CascadeShiftReactions.rxnMultBarA
    | .multBarB => CascadeShiftReactions.rxnMultBarB
    | .restoreInit => CascadeShiftReactions.rxnRestoreInit
    | .restore => CascadeShiftReactions.rxnRestore
    | .restoreDone i =>
        CascadeShiftReactions.rxnRestoreDone
          (ShiftGadget.sourceState i.q i.r i.w i.qNext)
    | .done i =>
        CascadeShiftReactions.rxnShiftDone
          (ShiftGadget.sourceState i.q i.r i.w i.qNext)
    | .bypass i =>
        CascadeShiftReactions.rxnBypass
          (ShiftGadget.sourceState i.q i.r i.w i.qNext)

theorem cascadeShiftNetwork_allUnitRate :
    (cascadeShiftNetwork (Q := Q)).allUnitRate := by
  intro i
  cases i <;> rfl

/-- The assembled cascade four-phase macro network:
  read ‖ erase ‖ cascadeShift ‖ write -/
def cascadeMacroNetwork (M : Binary Q) : Network (CascadeSpecies Q) :=
  phaseParallel4
    (liftedReadNetwork (s := s) M)
    (liftedEraseNetwork (Q := Q) (s := s))
    cascadeShiftNetwork
    liftedWriteNetwork

theorem cascadeMacroNetwork_allUnitRate (M : Binary Q) :
    (cascadeMacroNetwork (s := s) M).allUnitRate := by
  unfold cascadeMacroNetwork
  exact phaseParallel4_allUnitRate
    (liftedReadNetwork_allUnitRate (s := s) M)
    (liftedEraseNetwork_allUnitRate (Q := Q) (s := s))
    cascadeShiftNetwork_allUnitRate
    liftedWriteNetwork_allUnitRate

/-! ### Embedding transport: read, erase, write sub-networks -/

/-- The lifted read network exec transports from the original via embedding. -/
theorem liftedReadNetwork_exec_of_phaseStep?_read
    (M : Binary Q) {c c' : MicroCfg Q s}
    (hc : CanonicalMicroCfg c)
    (hphase : c.state.phase = Phase4.read)
    (hstep : phaseStep? (s := s) M c = some c') :
    ∃ is : List (liftedReadNetwork (s := s) M).I,
      (liftedReadNetwork (s := s) M).Exec
        (State.embed CascadeSpecies.ofFourPhase (FourPhaseEncoding.enc c))
        (State.embed CascadeSpecies.ofFourPhase (FourPhaseEncoding.enc c')) is := by
  rcases ReadNetwork.exec_of_phaseStep?_read (s := s) M hc hphase hstep with
    ⟨is, hExec, _hLen⟩
  exact ⟨is, Network.embed_exec_of_injective
    CascadeSpecies.ofFourPhase_injective hExec⟩

/-- The lifted erase network exec transports from the original via embedding. -/
theorem liftedEraseNetwork_exec_of_phaseStep?_erase
    (M : Binary Q) {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = Phase4.erase)
    (hstep : phaseStep? (s := s) M c = some c') :
    ∃ is : List (liftedEraseNetwork (Q := Q) (s := s)).I,
      (liftedEraseNetwork (Q := Q) (s := s)).Exec
        (State.embed CascadeSpecies.ofFourPhase (FourPhaseEncoding.enc c))
        (State.embed CascadeSpecies.ofFourPhase (FourPhaseEncoding.enc c')) is := by
  rcases EraseNetwork.exec_of_phaseStep?_erase (s := s) M hc hphase hstep with
    ⟨is, hExec, _hLen⟩
  exact ⟨is, Network.embed_exec_of_injective
    CascadeSpecies.ofFourPhase_injective hExec⟩

/-- The lifted write network exec transports from the original via embedding. -/
theorem liftedWriteNetwork_exec_of_phaseStep?_write
    (M : Binary Q) {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = Phase4.write)
    (hstep : phaseStep? (s := s) M c = some c') :
    ∃ is : List (liftedWriteNetwork (Q := Q)).I,
      (liftedWriteNetwork (Q := Q)).Exec
        (State.embed CascadeSpecies.ofFourPhase (FourPhaseEncoding.enc c))
        (State.embed CascadeSpecies.ofFourPhase (FourPhaseEncoding.enc c')) is := by
  rcases WriteNetwork.exec_of_phaseStep?_write (s := s) M hc hphase hstep with
    ⟨is, hExec, _hLen⟩
  exact ⟨is, Network.embed_exec_of_injective
    CascadeSpecies.ofFourPhase_injective hExec⟩

/-! ### Cascade shift intermediate states -/

/-- Intermediate CascadeSpecies state during cascade shift.
  `ctrl_phase = none` means original ctrl token is present;
  `ctrl_phase = some sp` means the shiftCtrl token `sp` is present instead. -/
private def csState (st : MicroState Q)
    (ctrl_phase : Option ShiftSubPhase)
    (t tb sh : Nat) : State (CascadeSpecies Q) := fun
  | CascadeSpecies.ctrl q p r w x =>
      if ctrl_phase = none then
        (if CascadeSpecies.ctrl q p r w x = CascadeSpecies.ctrlOf st then 1 else 0)
      else 0
  | CascadeSpecies.shiftCtrl sp =>
      match ctrl_phase with
      | some sp' => if sp = sp' then 1 else 0
      | none => 0
  | CascadeSpecies.tape => t
  | CascadeSpecies.tapeBar => tb
  | CascadeSpecies.tapeShifted => sh

/-- Final state after cascade shift with afterShift control. -/
private def csFinal (st : MicroState Q) (t tb : Nat) : State (CascadeSpecies Q) := fun
  | CascadeSpecies.ctrl q p r w x =>
      if CascadeSpecies.ctrl q p r w x =
        CascadeSpecies.ctrlOf (MicroState.afterShift st) then 1 else 0
  | CascadeSpecies.shiftCtrl _ => 0
  | CascadeSpecies.tape => t
  | CascadeSpecies.tapeBar => tb
  | CascadeSpecies.tapeShifted => 0

/-! ### Embedding equals intermediate state -/

private theorem embed_enc_eq_csState (st : MicroState Q) (tape : Nat) :
    State.embed CascadeSpecies.ofFourPhase
      (FourPhaseEncoding.enc ({ state := st, tape := tape } : MicroCfg Q s)) =
      csState st none tape (FourPhaseEncoding.maxTape s - tape) 0 := by
  funext sp
  have hi := @State.embed_apply_of_injective (FourPhaseSpecies Q) (CascadeSpecies Q)
    _ _ _ CascadeSpecies.ofFourPhase_injective
  cases sp with
  | ctrl q p r w x =>
      rw [show CascadeSpecies.ctrl q p r w x =
        CascadeSpecies.ofFourPhase (FourPhaseSpecies.ctrl q p r w x) from rfl, hi]
      simp [csState, FourPhaseEncoding.enc, FourPhaseEncoding.control,
        FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar,
        State.add, State.single, FourPhaseSpecies.ctrlOf,
        CascadeSpecies.ofFourPhase, CascadeSpecies.ctrlOf,
        FourPhaseSpecies.ctrl.injEq]
  | shiftCtrl sp =>
      have : ¬ ∃ x : FourPhaseSpecies Q, CascadeSpecies.ofFourPhase x = CascadeSpecies.shiftCtrl sp :=
        fun ⟨x, hx⟩ => by cases x <;> simp [CascadeSpecies.ofFourPhase] at hx
      rw [State.embed_eq_zero_of_not_exists this]; rfl
  | tape =>
      rw [show (CascadeSpecies.tape : CascadeSpecies Q) =
        CascadeSpecies.ofFourPhase FourPhaseSpecies.tape from rfl, hi]
      simp [csState, FourPhaseEncoding.enc, FourPhaseEncoding.control,
        FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar,
        State.add, State.single, FourPhaseSpecies.ctrlOf,
        CascadeSpecies.ofFourPhase]
  | tapeBar =>
      rw [show (CascadeSpecies.tapeBar : CascadeSpecies Q) =
        CascadeSpecies.ofFourPhase FourPhaseSpecies.tapeBar from rfl, hi]
      simp [csState, FourPhaseEncoding.enc, FourPhaseEncoding.control,
        FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar,
        State.add, State.single, FourPhaseSpecies.ctrlOf,
        CascadeSpecies.ofFourPhase]
  | tapeShifted =>
      have : ¬ ∃ x : FourPhaseSpecies Q, CascadeSpecies.ofFourPhase x = CascadeSpecies.tapeShifted :=
        fun ⟨x, hx⟩ => by cases x <;> simp [CascadeSpecies.ofFourPhase] at hx
      rw [State.embed_eq_zero_of_not_exists this]; rfl

private theorem embed_enc_afterShift_eq_csFinal (st : MicroState Q) (tape : Nat) :
    State.embed CascadeSpecies.ofFourPhase
      (FourPhaseEncoding.enc
        ({ state := MicroState.afterShift st,
           tape := Encoding.shiftTail tape } : MicroCfg Q s)) =
      csFinal st (Encoding.shiftTail tape)
        (FourPhaseEncoding.maxTape s - Encoding.shiftTail tape) := by
  funext sp
  have hi := @State.embed_apply_of_injective (FourPhaseSpecies Q) (CascadeSpecies Q)
    _ _ _ CascadeSpecies.ofFourPhase_injective
  cases sp with
  | ctrl q p r w x =>
      rw [show CascadeSpecies.ctrl q p r w x =
        CascadeSpecies.ofFourPhase (FourPhaseSpecies.ctrl q p r w x) from rfl, hi]
      simp [csFinal, FourPhaseEncoding.enc, FourPhaseEncoding.control,
        FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar,
        State.add, State.single, FourPhaseSpecies.ctrlOf,
        CascadeSpecies.ofFourPhase, CascadeSpecies.ctrlOf, MicroState.afterShift,
        FourPhaseSpecies.ctrl.injEq]
  | shiftCtrl sp =>
      have : ¬ ∃ x : FourPhaseSpecies Q, CascadeSpecies.ofFourPhase x = CascadeSpecies.shiftCtrl sp :=
        fun ⟨x, hx⟩ => by cases x <;> simp [CascadeSpecies.ofFourPhase] at hx
      rw [State.embed_eq_zero_of_not_exists this]; rfl
  | tape =>
      rw [show (CascadeSpecies.tape : CascadeSpecies Q) =
        CascadeSpecies.ofFourPhase FourPhaseSpecies.tape from rfl, hi]
      simp [csFinal, FourPhaseEncoding.enc, FourPhaseEncoding.control,
        FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar,
        State.add, State.single, FourPhaseSpecies.ctrlOf,
        CascadeSpecies.ofFourPhase]
  | tapeBar =>
      rw [show (CascadeSpecies.tapeBar : CascadeSpecies Q) =
        CascadeSpecies.ofFourPhase FourPhaseSpecies.tapeBar from rfl, hi]
      simp [csFinal, FourPhaseEncoding.enc, FourPhaseEncoding.control,
        FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar,
        State.add, State.single, FourPhaseSpecies.ctrlOf,
        CascadeSpecies.ofFourPhase]
  | tapeShifted =>
      have : ¬ ∃ x : FourPhaseSpecies Q, CascadeSpecies.ofFourPhase x = CascadeSpecies.tapeShifted :=
        fun ⟨x, hx⟩ => by cases x <;> simp [CascadeSpecies.ofFourPhase] at hx
      rw [State.embed_eq_zero_of_not_exists this]; rfl

/-! ### Step lemmas -/

/-- Tactic for proving cascade shift step goals: case-split all species
  including ShiftSubPhase sub-cases, then simp + omega. -/
local macro "cascade_step" : tactic =>
  `(tactic|
    (constructor
     · intro sp; cases sp <;> (try rename_i sp'; cases sp') <;>
        simp [cascadeShiftNetwork, csState, csFinal,
          CascadeShiftReactions.rxnMultA, CascadeShiftReactions.rxnMultA_cont,
          CascadeShiftReactions.rxnMultB, CascadeShiftReactions.rxnMultC,
          CascadeShiftReactions.rxnMultBarA, CascadeShiftReactions.rxnMultBarB,
          CascadeShiftReactions.rxnRestoreInit, CascadeShiftReactions.rxnRestore,
          CascadeShiftReactions.rxnRestoreDone, CascadeShiftReactions.rxnShiftDone,
          CascadeShiftReactions.rxnBypass,
          Reaction.fire, CascadeSpecies.ctrlOf,
          ShiftGadget.sourceState, MicroState.readPhase,
          MicroState.afterRead, MicroState.afterErase, MicroState.afterShift] <;> omega
     · funext sp; cases sp <;> (try rename_i sp'; cases sp') <;>
        simp [cascadeShiftNetwork, csState, csFinal,
          CascadeShiftReactions.rxnMultA, CascadeShiftReactions.rxnMultA_cont,
          CascadeShiftReactions.rxnMultB, CascadeShiftReactions.rxnMultC,
          CascadeShiftReactions.rxnMultBarA, CascadeShiftReactions.rxnMultBarB,
          CascadeShiftReactions.rxnRestoreInit, CascadeShiftReactions.rxnRestore,
          CascadeShiftReactions.rxnRestoreDone, CascadeShiftReactions.rxnShiftDone,
          CascadeShiftReactions.rxnBypass,
          Reaction.fire, CascadeSpecies.ctrlOf,
          ShiftGadget.sourceState, MicroState.readPhase,
          MicroState.afterRead, MicroState.afterErase, MicroState.afterShift] <;> omega))

private theorem bypass_step (st : MicroState Q)
    (idx : EraseNetwork.Idx Q)
    (hst : st = ShiftGadget.sourceState idx.q idx.r idx.w idx.qNext)
    (tb : Nat) :
    cascadeShiftNetwork.StepAt (.bypass idx)
      (csState st none 0 tb 0) (csFinal st 0 tb) := by
  subst hst; cascade_step

private theorem initiate_step' (st : MicroState Q)
    (idx : EraseNetwork.Idx Q)
    (hst : st = ShiftGadget.sourceState idx.q idx.r idx.w idx.qNext)
    (t tb : Nat) (ht : 0 < t) :
    cascadeShiftNetwork.StepAt (.initiate idx)
      (csState st none t tb 0)
      (csState st (some .multB) (t - 1) tb 1) := by
  subst hst; cascade_step

private theorem multB_step' (st : MicroState Q) (t tb sh : Nat) :
    cascadeShiftNetwork.StepAt .multB
      (csState st (some .multB) t tb sh)
      (csState st (some .multC) t tb (sh + 1)) := by
  cascade_step

private theorem multC_step' (st : MicroState Q) (t tb sh : Nat) :
    cascadeShiftNetwork.StepAt .multC
      (csState st (some .multC) t tb sh)
      (csState st (some .multBarA) t tb (sh + 1)) := by
  cascade_step

private theorem multBarA_step' (st : MicroState Q) (t tb sh : Nat) (htb : 0 < tb) :
    cascadeShiftNetwork.StepAt .multBarA
      (csState st (some .multBarA) t tb sh)
      (csState st (some .multBarB) t (tb - 1) sh) := by
  cascade_step

private theorem multBarB_step' (st : MicroState Q) (t tb sh : Nat) (htb : 0 < tb) :
    cascadeShiftNetwork.StepAt .multBarB
      (csState st (some .multBarB) t tb sh)
      (csState st (some .multA) t (tb - 1) sh) := by
  cascade_step

private theorem cont_step' (st : MicroState Q) (t tb sh : Nat) (ht : 0 < t) :
    cascadeShiftNetwork.StepAt .cont
      (csState st (some .multA) t tb sh)
      (csState st (some .multB) (t - 1) tb (sh + 1)) := by
  cascade_step

private theorem restoreInit_step' (st : MicroState Q) (tb sh : Nat) :
    cascadeShiftNetwork.StepAt .restoreInit
      (csState st (some .multA) 0 tb sh)
      (csState st (some .restore) 0 tb sh) := by
  cascade_step

private theorem restore_step' (st : MicroState Q) (t tb sh : Nat) (hsh : 0 < sh) :
    cascadeShiftNetwork.StepAt .restore
      (csState st (some .restore) t tb sh)
      (csState st (some .restore) (t + 1) tb (sh - 1)) := by
  cascade_step

private theorem restoreDone_step' (st : MicroState Q)
    (idx : EraseNetwork.Idx Q)
    (hst : st = ShiftGadget.sourceState idx.q idx.r idx.w idx.qNext)
    (t tb : Nat) :
    cascadeShiftNetwork.StepAt (.restoreDone idx)
      (csState st (some .restore) t tb 0) (csFinal st t tb) := by
  subst hst; cascade_step

/-! ### Composite lemmas -/

/-- One multiply cycle from multA: 5 steps, consumes 1 tape + 2 tapeBar, produces 3 shifted. -/
private theorem one_mult_cycle (st : MicroState Q) (t tb sh : Nat)
    (ht : 0 < t) (htb : 1 < tb) :
    cascadeShiftNetwork.Reaches
      (csState st (some .multA) t tb sh)
      (csState st (some .multA) (t - 1) (tb - 2) (sh + 3)) :=
  ⟨[.cont, .multB, .multC, .multBarA, .multBarB],
    ExecOf.cons (cont_step' st t tb sh ht)
    (ExecOf.cons (multB_step' st (t - 1) tb (sh + 1))
    (ExecOf.cons (multC_step' st (t - 1) tb (sh + 2))
    (ExecOf.cons (multBarA_step' st (t - 1) tb (sh + 3) (by omega))
    (ExecOf.cons (multBarB_step' st (t - 1) (tb - 1) (sh + 3) (by omega))
    (ExecOf.nil _)))))⟩

/-- Multiply cont phase: k cycles from multA, consuming k tape + 2k tapeBar. -/
private theorem mult_cont (st : MicroState Q) (k tb sh : Nat)
    (htb : 2 * k ≤ tb) :
    cascadeShiftNetwork.Reaches
      (csState st (some .multA) k tb sh)
      (csState st (some .multA) 0 (tb - 2 * k) (sh + 3 * k)) := by
  induction k generalizing tb sh with
  | zero => simpa using ⟨[], ExecOf.nil _⟩
  | succ n ih =>
      rcases one_mult_cycle st (n + 1) tb sh (by omega) (by omega) with ⟨is₁, h₁⟩
      have : n + 1 - 1 = n := by omega
      rw [this] at h₁
      rcases ih (tb - 2) (sh + 3) (by omega) with ⟨is₂, h₂⟩
      have h1 : tb - 2 - 2 * n = tb - 2 * (n + 1) := by omega
      have h2 : sh + 3 + 3 * n = sh + 3 * (n + 1) := by omega
      rw [h1, h2] at h₂
      exact ⟨is₁ ++ is₂, ExecOf.append h₁ h₂⟩

/-- Restore loop: sh steps, each converts 1 shifted → 1 tape. -/
private theorem restore_loop (st : MicroState Q) (t tb sh : Nat) :
    cascadeShiftNetwork.Reaches
      (csState st (some .restore) t tb sh)
      (csState st (some .restore) (t + sh) tb 0) := by
  induction sh generalizing t with
  | zero =>
      have : t + 0 = t := by omega
      rw [this]; exact ⟨[], ExecOf.nil _⟩
  | succ n ih =>
      have hsub : n + 1 - 1 = n := by omega
      have hstep : cascadeShiftNetwork.Reaches
          (csState st (some .restore) t tb (n + 1))
          (csState st (some .restore) (t + 1) tb n) :=
        ⟨[.restore], ExecOf.cons (by rw [← hsub]; exact restore_step' st t tb (n + 1) (by omega)) (ExecOf.nil _)⟩
      rcases ih (t + 1) with ⟨is₂, h₂⟩
      have hshift : t + 1 + n = t + (n + 1) := by omega
      rw [hshift] at h₂
      rcases hstep with ⟨is₁, h₁⟩
      exact ⟨is₁ ++ is₂, ExecOf.append h₁ h₂⟩

/-! ### Main cascade shift exec theorem -/

theorem cascadeShiftNetwork_exec_of_phaseStep?_shift
    (M : Binary Q) {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = Phase4.shift)
    (hstep : phaseStep? (s := s) M c = some c') :
    ∃ is : List (cascadeShiftNetwork (Q := Q)).I,
      (cascadeShiftNetwork (Q := Q)).Exec
        (State.embed CascadeSpecies.ofFourPhase (FourPhaseEncoding.enc c))
        (State.embed CascadeSpecies.ofFourPhase (FourPhaseEncoding.enc c')) is := by
  have hc'eq := phaseStep?_eq_shiftTail_of_shift (s := s) M hphase hstep
  subst hc'eq
  cases c with
  | mk st tape =>
      cases st with
      | mk q phase readSymbol pendingWrite pendingState =>
          cases phase <;> try cases hphase
          have hCanon : MicroState.Canonical
              ({ q := q, phase := Phase4.shift,
                 readSymbol := readSymbol,
                 pendingWrite := pendingWrite,
                 pendingState := pendingState } : MicroState Q) := hc.1
          have hTapeWF : Encoding.IsBase3BoolTape s tape := hc.2
          rcases (by simpa [MicroState.Canonical] using hCanon :
            ∃ r w qNext, readSymbol = some r ∧ pendingWrite = some w ∧
              pendingState = some qNext) with ⟨r, w, qNext, rfl, rfl, rfl⟩
          set st : MicroState Q :=
            { q := q, phase := Phase4.shift,
              readSymbol := some r, pendingWrite := some w,
              pendingState := some qNext }
          set idx : EraseNetwork.Idx Q := ⟨q, r, w, qNext⟩
          have hst : st = ShiftGadget.sourceState idx.q idx.r idx.w idx.qNext := by
            simp [st, idx, ShiftGadget.sourceState, MicroState.readPhase,
              MicroState.afterRead, MicroState.afterErase]
          rw [embed_enc_eq_csState st tape,
              embed_enc_afterShift_eq_csFinal st tape]
          rcases Nat.eq_zero_or_pos tape with htape | htape
          · -- tape = 0: bypass
            subst htape
            have h0 : Encoding.shiftTail 0 = 0 := by simp [Encoding.shiftTail]
            rw [h0]
            exact ⟨[.bypass idx],
              ExecOf.cons (bypass_step st idx hst _) (ExecOf.nil _)⟩
          · -- tape > 0: full cascade
            have htapeLt := hTapeWF.lt_pow
            have htbar : 2 * tape ≤ FourPhaseEncoding.maxTape s - tape :=
              FourPhaseEncoding.two_mul_le_tapeBar_of_lt_pow htapeLt
            have hShiftTail : Encoding.shiftTail tape = 3 * tape := by
              unfold Encoding.shiftTail; ring
            rw [hShiftTail]
            -- Prove Reaches (= ∃ is, Exec) by composing phases
            -- Phase 1: Initiate
            have h1 : cascadeShiftNetwork.Reaches
                (csState st none tape (FourPhaseEncoding.maxTape s - tape) 0)
                (csState st (some .multB) (tape - 1) (FourPhaseEncoding.maxTape s - tape) 1) :=
              ⟨[.initiate idx],
                ExecOf.cons (initiate_step' st idx hst tape _ htape)
                  (ExecOf.nil _)⟩
            -- Phase 2: B → C → BarA → BarB
            have h2 : cascadeShiftNetwork.Reaches
                (csState st (some .multB) (tape - 1) (FourPhaseEncoding.maxTape s - tape) 1)
                (csState st (some .multA) (tape - 1) (FourPhaseEncoding.maxTape s - tape - 2) 3) :=
              ⟨[.multB, .multC, .multBarA, .multBarB],
                ExecOf.cons (multB_step' st (tape - 1) _ 1)
                (ExecOf.cons (multC_step' st (tape - 1) _ 2)
                (ExecOf.cons (multBarA_step' st (tape - 1) _ 3 (by omega))
                (ExecOf.cons (multBarB_step' st (tape - 1) _ 3 (by omega))
                (ExecOf.nil _))))⟩
            -- Phase 3: Remaining tape-1 cont cycles
            have h3 : cascadeShiftNetwork.Reaches
                (csState st (some .multA) (tape - 1) (FourPhaseEncoding.maxTape s - tape - 2) 3)
                (csState st (some .multA) 0 (FourPhaseEncoding.maxTape s - 3 * tape) (3 * tape)) := by
              rcases mult_cont st (tape - 1) (FourPhaseEncoding.maxTape s - tape - 2) 3
                (by omega) with ⟨is₂, hExec₂⟩
              have e1 : FourPhaseEncoding.maxTape s - tape - 2 - 2 * (tape - 1) =
                FourPhaseEncoding.maxTape s - 3 * tape := by omega
              have e2 : 3 + 3 * (tape - 1) = 3 * tape := by omega
              rw [e1, e2] at hExec₂
              exact ⟨is₂, hExec₂⟩
            -- Phase 4: RestoreInit
            have h4 : cascadeShiftNetwork.Reaches
                (csState st (some .multA) 0 (FourPhaseEncoding.maxTape s - 3 * tape) (3 * tape))
                (csState st (some .restore) 0 (FourPhaseEncoding.maxTape s - 3 * tape) (3 * tape)) :=
              ⟨[.restoreInit],
                ExecOf.cons (restoreInit_step' st _ _) (ExecOf.nil _)⟩
            -- Phase 5: Restore loop
            have h5 : cascadeShiftNetwork.Reaches
                (csState st (some .restore) 0 (FourPhaseEncoding.maxTape s - 3 * tape) (3 * tape))
                (csState st (some .restore) (3 * tape) (FourPhaseEncoding.maxTape s - 3 * tape) 0) := by
              rcases restore_loop st 0 (FourPhaseEncoding.maxTape s - 3 * tape) (3 * tape)
                with ⟨is₅, hExec₅⟩
              have e0 : 0 + 3 * tape = 3 * tape := by omega
              rw [e0] at hExec₅
              exact ⟨is₅, hExec₅⟩
            -- Phase 6: RestoreDone
            have h6 : cascadeShiftNetwork.Reaches
                (csState st (some .restore) (3 * tape) (FourPhaseEncoding.maxTape s - 3 * tape) 0)
                (csFinal st (3 * tape) (FourPhaseEncoding.maxTape s - 3 * tape)) :=
              ⟨[.restoreDone idx],
                ExecOf.cons (restoreDone_step' st idx hst _ _) (ExecOf.nil _)⟩
            -- Compose all phases
            exact Network.reaches_trans h1
              (Network.reaches_trans h2
              (Network.reaches_trans h3
              (Network.reaches_trans h4
              (Network.reaches_trans h5 h6))))

/-! ### Main simulation theorem -/

/-- Each phase step of the four-phase system can be executed by the
  cascade macro network on CascadeSpecies-embedded states. -/
theorem cascadeMacroNetwork_exec_of_phaseStep
    (M : Binary Q) {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    ∃ is : List (cascadeMacroNetwork (s := s) M).I,
      (cascadeMacroNetwork (s := s) M).Exec
        (State.embed CascadeSpecies.ofFourPhase (FourPhaseEncoding.enc c))
        (State.embed CascadeSpecies.ofFourPhase (FourPhaseEncoding.enc c')) is := by
  cases hphase : c.state.phase with
  | read =>
      rcases liftedReadNetwork_exec_of_phaseStep?_read (s := s) M
        hc.1 hphase hstep with ⟨is, hExec⟩
      exact ⟨is.map (fun i => Sum.inl (Sum.inl i)),
        phaseParallel4_exec_read hExec⟩
  | erase =>
      rcases liftedEraseNetwork_exec_of_phaseStep?_erase (s := s) M
        hc hphase hstep with ⟨is, hExec⟩
      exact ⟨is.map (fun i => Sum.inl (Sum.inr i)),
        phaseParallel4_exec_erase hExec⟩
  | shift =>
      rcases cascadeShiftNetwork_exec_of_phaseStep?_shift (s := s) M
        hc hphase hstep with ⟨is, hExec⟩
      exact ⟨is.map (fun i => Sum.inr (Sum.inl i)),
        phaseParallel4_exec_shift hExec⟩
  | write =>
      rcases liftedWriteNetwork_exec_of_phaseStep?_write (s := s) M
        hc hphase hstep with ⟨is, hExec⟩
      exact ⟨is.map (fun i => Sum.inr (Sum.inr i)),
        phaseParallel4_exec_write hExec⟩

/-- The cascade macro network simulates the four-phase system. -/
theorem cascadeMacroNetwork_exec_of_fourPhase_steps
    (M : Binary Q) {n : Nat} {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c') :
    ∃ is : List (cascadeMacroNetwork (s := s) M).I,
      (cascadeMacroNetwork (s := s) M).Exec
        (State.embed CascadeSpecies.ofFourPhase (FourPhaseEncoding.enc c))
        (State.embed CascadeSpecies.ofFourPhase (FourPhaseEncoding.enc c')) is := by
  induction n generalizing c with
  | zero =>
      have hEq : (some c : Option (MicroCfg Q s)) = some c' := h
      cases hEq
      exact ⟨[], ExecOf.nil _⟩
  | succ n ih =>
      cases hstep : (fourPhaseSystem (s := s) M).step? c with
      | none =>
          simp [DetSystem.steps?, DetSystem.iter, hstep] at h
      | some c₁ =>
          have hc₁ : GadgetMicroCfgWF c₁ :=
            phaseStep?_preserves_gadgetWF (s := s) M hc
              (by simpa [fourPhaseSystem] using hstep)
          have htail :
              (fourPhaseSystem (s := s) M).steps? n c₁ = some c' := by
            simpa [DetSystem.steps?, DetSystem.iter, hstep] using h
          have hphase :
              phaseStep? (s := s) M c = some c₁ := by
            simpa [fourPhaseSystem] using hstep
          rcases cascadeMacroNetwork_exec_of_phaseStep (s := s) M
            hc hphase with ⟨is₁, hExec₁⟩
          rcases ih hc₁ htail with ⟨is₂, hExec₂⟩
          exact ⟨is₁ ++ is₂, ExecOf.append hExec₁ hExec₂⟩

/-- The cascade macro network reaches the target encoding from the source
  encoding for any multi-step CTM computation. -/
theorem cascadeMacroNetwork_reaches_of_ctm_steps
    (M : Binary Q) {n : Nat}
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (cascadeMacroNetwork (s := s) M).Reaches
      (State.embed CascadeSpecies.ofFourPhase
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg)))
      (State.embed CascadeSpecies.ofFourPhase
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))) := by
  rcases cascadeMacroNetwork_exec_of_fourPhase_steps (s := s) M
    (MicroCfg.ofCTM_gadgetWF cfg)
    (fourPhaseKStepSim_steps (s := s) M h) with ⟨is, hExec⟩
  exact ⟨is, hExec⟩

/-- The cascade macro network simulates one CTM step. -/
theorem cascadeMacroNetwork_reaches_of_ctm_step
    (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    (cascadeMacroNetwork (s := s) M).Reaches
      (State.embed CascadeSpecies.ofFourPhase
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg)))
      (State.embed CascadeSpecies.ofFourPhase
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))) :=
  cascadeMacroNetwork_reaches_of_ctm_steps (s := s) M
    (DetSystem.steps?_one_of_step? (M.detSystem (s := s)) h)

end CascadeMacroModule

end Ripple.sCRNUniversality.CTM
