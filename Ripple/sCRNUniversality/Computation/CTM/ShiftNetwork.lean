import Ripple.sCRNUniversality.Computation.CTM.ShiftGadget
import Ripple.sCRNUniversality.Computation.CTM.FourPhaseTapeInvariant

namespace Ripple.sCRNUniversality

namespace CTM

namespace ShiftNetwork

universe u

theorem exec_of_phaseStep?_shift {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = Phase4.shift)
    (hstep : phaseStep? (s := s) M c = some c') :
    exists is : List (ShiftGadget.network Q s).I,
      (ShiftGadget.network Q s).Exec
        (FourPhaseEncoding.enc c)
        (FourPhaseEncoding.enc c') is /\
      is.length = 1 := by
  cases c with
  | mk st tape =>
      cases st with
      | mk q phase readSymbol pendingWrite pendingState =>
          cases phase <;> try cases hphase
          have hCanon : MicroState.Canonical
              ({ q := q, phase := Phase4.shift,
                 readSymbol := readSymbol,
                 pendingWrite := pendingWrite,
                 pendingState := pendingState } : MicroState Q) :=
            hc.1
          have hTape : Encoding.IsBase3BoolTape s tape :=
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
              some (ShiftGadget.targetCfg (s := s) q r w qNext tape) =
                some c' := by
            simpa [ShiftGadget.sourceCfg, ShiftGadget.targetCfg,
              ShiftGadget.sourceState, ShiftGadget.targetState,
              phaseStep?, MicroState.readPhase, MicroState.afterRead,
              MicroState.afterErase, MicroState.afterShift] using hstep
          cases hEq
          refine ⟨[ShiftGadget.idxOfTape q r w qNext hTape.lt_pow], ?_, by simp⟩
          simpa [ShiftGadget.sourceCfg, ShiftGadget.targetCfg,
            ShiftGadget.sourceState, ShiftGadget.targetState]
            using ShiftGadget.exec (Q := Q) (s := s)
              q r w qNext tape hTape.lt_pow

end ShiftNetwork

end CTM

end Ripple.sCRNUniversality
