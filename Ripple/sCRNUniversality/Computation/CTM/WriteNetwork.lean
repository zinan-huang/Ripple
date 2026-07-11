import Ripple.sCRNUniversality.Computation.CTM.WriteGadget
import Ripple.sCRNUniversality.Computation.CTM.FourPhaseTapeInvariant

namespace Ripple.sCRNUniversality

namespace CTM

namespace WriteNetwork

universe u

structure Idx (Q : Type u) where
  q : Q
  r : Bool
  w : Bool
  qNext : Q
deriving DecidableEq, Repr, Fintype

def network (Q : Type u) [Fintype Q] [DecidableEq Q] :
    Network (FourPhaseSpecies Q) where
  I := Idx Q
  fintypeI := inferInstance
  rxn := fun i => WriteGadget.reaction i.q i.r i.w i.qNext

theorem network_allUnitRate (Q : Type u) [Fintype Q] [DecidableEq Q] :
    (network Q).allUnitRate := by
  intro i
  rfl

theorem network_hasPositiveRates (Q : Type u) [Fintype Q] [DecidableEq Q] :
    (network Q).hasPositiveRates :=
  Network.hasPositiveRates_of_allUnitRate
    (network_allUnitRate Q)

theorem network_equalRates (Q : Type u) [Fintype Q] [DecidableEq Q] :
    (network Q).equalRates :=
  Network.equalRates_of_allUnitRate
    (network_allUnitRate Q)

theorem exec_idx {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (i : Idx Q) (tape : Nat)
    (hTape : Encoding.IsShiftedBase3BoolTape s tape) :
    (network Q).Exec
      (FourPhaseEncoding.enc
        (WriteGadget.sourceCfg (s := s) i.q i.r i.w i.qNext tape))
      (FourPhaseEncoding.enc
        (WriteGadget.targetCfg (s := s) i.q i.r i.w i.qNext tape))
      [i] := by
  exact ExecOf.cons
    (by
      simpa [network, Network.StepAt] using
        WriteGadget.reaction_firesTo (s := s)
          i.q i.r i.w i.qNext tape hTape)
    (ExecOf.nil _)

theorem exec_of_phaseStep?_write {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = Phase4.write)
    (hstep : phaseStep? (s := s) M c = some c') :
    exists is : List (network Q).I,
      (network Q).Exec
        (FourPhaseEncoding.enc c)
        (FourPhaseEncoding.enc c') is /\
      is.length = 1 := by
  cases c with
  | mk st tape =>
      cases st with
      | mk q phase readSymbol pendingWrite pendingState =>
          cases phase <;> try cases hphase
          have hCanon : MicroState.Canonical
              ({ q := q, phase := Phase4.write,
                 readSymbol := readSymbol,
                 pendingWrite := pendingWrite,
                 pendingState := pendingState } : MicroState Q) :=
            hc.1
          have hTape : Encoding.IsShiftedBase3BoolTape s tape :=
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
          have hEq :
              some (WriteGadget.targetCfg (s := s) q r w qNext tape) =
                some c' := by
            simpa [WriteGadget.sourceCfg, WriteGadget.targetCfg,
              WriteGadget.sourceState, WriteGadget.targetState,
              phaseStep?, MicroState.readPhase, MicroState.afterRead,
              MicroState.afterErase, MicroState.afterShift,
              MicroState.afterWrite] using hstep
          cases hEq
          let i : Idx Q := { q := q, r := r, w := w, qNext := qNext }
          refine ⟨[i], ?_, by simp⟩
          simpa [i, WriteGadget.sourceCfg, WriteGadget.targetCfg,
            WriteGadget.sourceState, WriteGadget.targetState]
            using exec_idx (Q := Q) (s := s) i tape hTape

end WriteNetwork

end CTM

end Ripple.sCRNUniversality
