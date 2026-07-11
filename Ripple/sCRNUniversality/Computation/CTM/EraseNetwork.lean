import Ripple.sCRNUniversality.Computation.CTM.EraseGadget
import Ripple.sCRNUniversality.Computation.CTM.FourPhaseTapeInvariant

namespace Ripple.sCRNUniversality

namespace CTM

namespace EraseNetwork

universe u

structure Idx (Q : Type u) where
  q : Q
  r : Bool
  w : Bool
  qNext : Q
deriving DecidableEq, Repr, Fintype

def network (Q : Type u) [Fintype Q] [DecidableEq Q] (s : Nat) :
    Network (FourPhaseSpecies Q) where
  I := Idx Q
  fintypeI := inferInstance
  rxn := fun i => EraseGadget.reaction (s := s) i.q i.r i.w i.qNext

theorem network_allUnitRate {Q : Type u} [Fintype Q] [DecidableEq Q]
    (s : Nat) :
    (network Q s).allUnitRate := by
  intro i
  rfl

theorem network_hasPositiveRates {Q : Type u} [Fintype Q] [DecidableEq Q]
    (s : Nat) :
    (network Q s).hasPositiveRates :=
  Network.hasPositiveRates_of_allUnitRate
    (network_allUnitRate (Q := Q) s)

theorem network_equalRates {Q : Type u} [Fintype Q] [DecidableEq Q]
    (s : Nat) :
    (network Q s).equalRates :=
  Network.equalRates_of_allUnitRate
    (network_allUnitRate (Q := Q) s)

theorem exec_idx {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (i : Idx Q) (tape : Nat)
    (hTape : Encoding.IsBase3BoolTape (s + 1) tape)
    (hread : i.r = Encoding.readMSB? s tape) :
    (network Q s).Exec
      (FourPhaseEncoding.enc
        (EraseGadget.sourceCfg (s := s) i.q i.r i.w i.qNext tape))
      (FourPhaseEncoding.enc
        (EraseGadget.targetCfg (s := s) i.q i.r i.w i.qNext tape))
      [i] := by
  exact ExecOf.cons
    (by
      simpa [network, Network.StepAt] using
        EraseGadget.reaction_firesTo (s := s)
          i.q i.r i.w i.qNext tape hTape hread)
    (ExecOf.nil _)

theorem exec_of_phaseStep?_erase {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = Phase4.erase)
    (hstep : phaseStep? (s := s) M c = some c') :
    exists is : List (network Q s).I,
      (network Q s).Exec
        (FourPhaseEncoding.enc c)
        (FourPhaseEncoding.enc c') is /\
      is.length = 1 := by
  cases c with
  | mk st tape =>
      cases st with
      | mk q phase readSymbol pendingWrite pendingState =>
          cases phase <;> try cases hphase
          have hCanon : MicroState.Canonical
              ({ q := q, phase := Phase4.erase,
                 readSymbol := readSymbol,
                 pendingWrite := pendingWrite,
                 pendingState := pendingState } : MicroState Q) :=
            hc.1
          have hWF :
              (MicroCfg.TapeWF
                ({ state :=
                    ({ q := q, phase := Phase4.erase,
                       readSymbol := readSymbol,
                       pendingWrite := pendingWrite,
                       pendingState := pendingState } : MicroState Q),
                   tape := tape } : MicroCfg Q s)) :=
            hc.2
          have hPayload :
              exists r w qNext,
                readSymbol = some r /\
                  pendingWrite = some w /\
                  pendingState = some qNext := by
            simpa [MicroState.Canonical] using hCanon
          rcases hPayload with ⟨r, w, qNext, hReadSym, hWrite, hState⟩
          cases hReadSym
          cases hWrite
          cases hState
          have hTape : Encoding.IsBase3BoolTape (s + 1) tape :=
            hWF.1
          have hread : r = Encoding.readMSB? s tape :=
            hWF.2 r rfl
          have hEq :
              some (EraseGadget.targetCfg (s := s) q r w qNext tape) =
                some c' := by
            simpa [EraseGadget.sourceCfg, EraseGadget.targetCfg,
              EraseGadget.sourceState, EraseGadget.targetState,
              phaseStep?, MicroState.readPhase, MicroState.afterRead,
              MicroState.afterErase] using hstep
          cases hEq
          let i : Idx Q := { q := q, r := r, w := w, qNext := qNext }
          refine ⟨[i], ?_, by simp⟩
          simpa [i, EraseGadget.sourceCfg, EraseGadget.targetCfg,
            EraseGadget.sourceState, EraseGadget.targetState]
            using exec_idx (Q := Q) (s := s) i tape hTape hread

end EraseNetwork

end CTM

end Ripple.sCRNUniversality
