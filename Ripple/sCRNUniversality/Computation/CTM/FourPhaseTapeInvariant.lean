import Ripple.sCRNUniversality.Computation.CTM.GadgetArithmetic

namespace Ripple.sCRNUniversality

namespace CTM

universe u

namespace MicroCfg

def TapeWF {Q : Type u} {s : Nat} (c : MicroCfg Q s) : Prop :=
  match c.state.phase with
  | Phase4.read =>
      Encoding.IsBase3BoolTape (s + 1) c.tape
  | Phase4.erase =>
      Encoding.IsBase3BoolTape (s + 1) c.tape /\
        forall r : Bool,
          c.state.readSymbol = some r ->
            r = Encoding.readMSB? s c.tape
  | Phase4.shift =>
      Encoding.IsBase3BoolTape s c.tape
  | Phase4.write =>
      Encoding.IsShiftedBase3BoolTape s c.tape

def GadgetWF {Q : Type u} {s : Nat} (c : MicroCfg Q s) : Prop :=
  MicroState.Canonical c.state /\ TapeWF c

theorem ofCTM_tapeWF {Q : Type u} {s : Nat} (c : Cfg Q Bool s) :
    TapeWF (ofCTM c) := by
  cases c
  exact Encoding.IsBase3BoolTape.of_base3Val _

theorem ofCTM_gadgetWF {Q : Type u} {s : Nat} (c : Cfg Q Bool s) :
    GadgetWF (ofCTM c) := by
  exact ⟨ofCTM_state_canonical c, ofCTM_tapeWF c⟩

end MicroCfg

def GadgetMicroCfgWF {Q : Type u} {s : Nat} (c : MicroCfg Q s) : Prop :=
  c.GadgetWF

theorem phaseStep?_preserves_tapeWF {Q : Type u} {s : Nat}
    (M : Binary Q) {c c' : MicroCfg Q s}
    (hc : c.TapeWF)
    (hstep : phaseStep? (s := s) M c = some c') :
    c'.TapeWF := by
  cases c with
  | mk st tape =>
      cases st with
      | mk q phase readSymbol pendingWrite pendingState =>
          cases phase
          · have hTape :
                Encoding.IsBase3BoolTape (s + 1) tape := by
              simpa [MicroCfg.TapeWF] using hc
            cases hδ : M.delta q (Encoding.readMSB? s tape) with
            | none =>
                simp [phaseStep?, hδ] at hstep
            | some out =>
                rcases out with ⟨w, qNext⟩
                have hEq :
                    some
                      ({ state :=
                          MicroState.afterRead
                            ({ q := q, phase := Phase4.read,
                               readSymbol := readSymbol,
                               pendingWrite := pendingWrite,
                               pendingState := pendingState } : MicroState Q)
                            (Encoding.readMSB? s tape) w qNext,
                         tape := tape } : MicroCfg Q s) = some c' := by
                  simpa [phaseStep?, hδ] using hstep
                cases hEq
                refine ⟨hTape, ?_⟩
                intro r hr
                simp [MicroState.afterRead] at hr
                exact hr.symm
          · have hTape :
                Encoding.IsBase3BoolTape (s + 1) tape := by
              exact hc.1
            have hRead :
                forall r : Bool,
                  readSymbol = some r -> r = Encoding.readMSB? s tape := by
              exact hc.2
            cases hsym : readSymbol with
            | none =>
                simp [phaseStep?, hsym] at hstep
            | some r =>
                have hr : r = Encoding.readMSB? s tape :=
                  hRead r hsym
                have hEq :
                    some
                      ({ state :=
                          MicroState.afterErase
                            ({ q := q, phase := Phase4.erase,
                               readSymbol := some r,
                               pendingWrite := pendingWrite,
                               pendingState := pendingState } : MicroState Q),
                         tape := Encoding.eraseMSBWith s r tape } :
                        MicroCfg Q s) = some c' := by
                  simpa [phaseStep?, hsym] using hstep
                cases hEq
                exact Encoding.eraseMSBWith_preserves_IsBase3BoolTape
                  hTape hr
          · have hTape :
                Encoding.IsBase3BoolTape s tape := by
              simpa [MicroCfg.TapeWF] using hc
            have hEq :
                some
                  ({ state :=
                      MicroState.afterShift
                        ({ q := q, phase := Phase4.shift,
                           readSymbol := readSymbol,
                           pendingWrite := pendingWrite,
                           pendingState := pendingState } : MicroState Q),
                     tape := Encoding.shiftTail tape } : MicroCfg Q s) =
                    some c' := by
              simpa [phaseStep?] using hstep
            cases hEq
            exact hTape.shiftTail
          · have hTape :
                Encoding.IsShiftedBase3BoolTape s tape := by
              simpa [MicroCfg.TapeWF] using hc
            cases hpw : pendingWrite with
            | none =>
                simp [phaseStep?, hpw] at hstep
            | some w =>
                cases hps : pendingState with
                | none =>
                    simp [phaseStep?, hpw, hps] at hstep
                | some qNext =>
                    have hEq :
                        some
                          ({ state := MicroState.afterWrite qNext,
                             tape := Encoding.writeLSB tape w } :
                            MicroCfg Q s) = some c' := by
                      simpa [phaseStep?, hpw, hps] using hstep
                    cases hEq
                    exact hTape.writeLSB w

theorem phaseStep?_preserves_gadgetWF {Q : Type u} {s : Nat}
    (M : Binary Q) {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hstep : phaseStep? (s := s) M c = some c') :
    GadgetMicroCfgWF c' := by
  exact ⟨phaseStep?_preserves_canonical (s := s) M hc.1 hstep,
    phaseStep?_preserves_tapeWF (s := s) M hc.2 hstep⟩

end CTM

end Ripple.sCRNUniversality
