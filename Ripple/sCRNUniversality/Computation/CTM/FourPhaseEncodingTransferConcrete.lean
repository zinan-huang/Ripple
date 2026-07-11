import Ripple.sCRNUniversality.Computation.CTM.FourPhaseConcreteModule
import Ripple.sCRNUniversality.Computation.CTM.FourPhaseEncodingTransferFootprint

namespace Ripple.sCRNUniversality

namespace CTM

namespace FourPhaseEncoding

universe u

variable {Q : Type u} [Fintype Q] [DecidableEq Q]

def aggregateLocalFootprint {s : Nat}
    (c c' : MicroCfg Q s) :
    Species Q -> Prop :=
  FourPhaseSpecies.IsLocalMacroFootprint
    (FourPhaseSpecies.ctrlOf c.state)
    (FourPhaseSpecies.ctrlOf c'.state)

def aggregateNetwork_concreteGoodStepSchedule
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m') :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (aggregateNetwork st st' tapeIn tapeBarIn tapeOut tapeBarOut)
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      1
      ({ state := st, tape := m } : MicroCfg Q s)
      ({ state := st', tape := m' } : MicroCfg Q s) where
  schedule := [Network.OneRxnIdx.step]
  exec :=
    aggregateNetwork_exec
      (s := s) st st' m m'
      tapeIn tapeBarIn tapeOut tapeBarOut
      hTape hTapeBar hTapeEq hTapeBarEq
  length_le := by simp
  footprint := by
    simpa [aggregateLocalFootprint] using
      aggregateNetwork_scheduleFootprintWithin_singleton
        (Q := Q) st st'
        tapeIn tapeBarIn tapeOut tapeBarOut

def preserveTapeUnitNetwork_concreteGoodStepSchedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= m) :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (preserveTapeUnitNetwork st st')
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      1
      ({ state := st, tape := m } : MicroCfg Q s)
      ({ state := st', tape := m } : MicroCfg Q s) where
  schedule := [Network.OneRxnIdx.step]
  exec := preserveTapeUnitNetwork_exec (s := s) st st' m hm
  length_le := by simp
  footprint := by
    simpa [aggregateLocalFootprint] using
      preserveTapeUnitNetwork_scheduleFootprintWithin (Q := Q) st st'

def preserveTapeBarUnitNetwork_concreteGoodStepSchedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= maxTape s - m) :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (preserveTapeBarUnitNetwork st st')
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      1
      ({ state := st, tape := m } : MicroCfg Q s)
      ({ state := st', tape := m } : MicroCfg Q s) where
  schedule := [Network.OneRxnIdx.step]
  exec := preserveTapeBarUnitNetwork_exec (s := s) st st' m hm
  length_le := by simp
  footprint := by
    simpa [aggregateLocalFootprint] using
      preserveTapeBarUnitNetwork_scheduleFootprintWithin (Q := Q) st st'

def transferTapeToTapeBarUnitNetwork_concreteGoodStepSchedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : m <= maxTape s)
    (hpos : 1 <= m) :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (transferTapeToTapeBarUnitNetwork st st')
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      1
      ({ state := st, tape := m } : MicroCfg Q s)
      ({ state := st', tape := m - 1 } : MicroCfg Q s) where
  schedule := [Network.OneRxnIdx.step]
  exec :=
    transferTapeToTapeBarUnitNetwork_exec
      (s := s) st st' m hm hpos
  length_le := by simp
  footprint := by
    simpa [aggregateLocalFootprint] using
      transferTapeToTapeBarUnitNetwork_scheduleFootprintWithin
        (Q := Q) st st'

def transferTapeToTapeBarUnitNetwork_concreteGoodStepSchedule_replicate
    {s : Nat}
    (st : MicroState Q) (m k : Nat)
    (hm : m <= maxTape s)
    (hk : k <= m) :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (transferTapeToTapeBarUnitNetwork st st)
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      k
      ({ state := st, tape := m } : MicroCfg Q s)
      ({ state := st, tape := m - k } : MicroCfg Q s) where
  schedule := List.replicate k Network.OneRxnIdx.step
  exec :=
    transferTapeToTapeBarUnitNetwork_exec_replicate
      (s := s) st m k hm hk
  length_le := by simp
  footprint := by
    simpa [aggregateLocalFootprint] using
      transferTapeToTapeBarUnitNetwork_scheduleFootprintWithin_replicate
        (Q := Q) st k

def transferTapeBarToTapeUnitNetwork_concreteGoodStepSchedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= maxTape s - m) :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (transferTapeBarToTapeUnitNetwork st st')
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      1
      ({ state := st, tape := m } : MicroCfg Q s)
      ({ state := st', tape := m + 1 } : MicroCfg Q s) where
  schedule := [Network.OneRxnIdx.step]
  exec :=
    transferTapeBarToTapeUnitNetwork_exec
      (s := s) st st' m hm
  length_le := by simp
  footprint := by
    simpa [aggregateLocalFootprint] using
      transferTapeBarToTapeUnitNetwork_scheduleFootprintWithin
        (Q := Q) st st'

def transferTapeBarToTapeUnitNetwork_concreteGoodStepSchedule_replicate
    {s : Nat}
    (st : MicroState Q) (m k : Nat)
    (hk : k <= maxTape s - m) :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (transferTapeBarToTapeUnitNetwork st st)
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      k
      ({ state := st, tape := m } : MicroCfg Q s)
      ({ state := st, tape := m + k } : MicroCfg Q s) where
  schedule := List.replicate k Network.OneRxnIdx.step
  exec :=
    transferTapeBarToTapeUnitNetwork_exec_replicate
      (s := s) st m k hk
  length_le := by simp
  footprint := by
    simpa [aggregateLocalFootprint] using
      transferTapeBarToTapeUnitNetwork_scheduleFootprintWithin_replicate
        (Q := Q) st k

def tapeTransferUnitNetwork_concreteGoodStepSchedule_toTapeBar_replicate
    {s : Nat}
    (st : MicroState Q) (m k : Nat)
    (hm : m <= maxTape s)
    (hk : k <= m) :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (tapeTransferUnitNetwork st)
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      k
      ({ state := st, tape := m } : MicroCfg Q s)
      ({ state := st, tape := m - k } : MicroCfg Q s) where
  schedule := (List.replicate k Network.OneRxnIdx.step).map Sum.inl
  exec :=
    tapeTransferUnitNetwork_exec_toTapeBar_replicate
      (s := s) st m k hm hk
  length_le := by
    rw [List.length_map]
    exact le_of_eq List.length_replicate
  footprint := by
    simpa [aggregateLocalFootprint] using
      tapeTransferUnitNetwork_scheduleFootprintWithin_toTapeBar_replicate
        (Q := Q) st k

def tapeTransferUnitNetwork_concreteGoodStepSchedule_toTape_replicate
    {s : Nat}
    (st : MicroState Q) (m k : Nat)
    (hk : k <= maxTape s - m) :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (tapeTransferUnitNetwork st)
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      k
      ({ state := st, tape := m } : MicroCfg Q s)
      ({ state := st, tape := m + k } : MicroCfg Q s) where
  schedule := (List.replicate k Network.OneRxnIdx.step).map Sum.inr
  exec :=
    tapeTransferUnitNetwork_exec_toTape_replicate
      (s := s) st m k hk
  length_le := by
    rw [List.length_map]
    exact le_of_eq List.length_replicate
  footprint := by
    simpa [aggregateLocalFootprint] using
      tapeTransferUnitNetwork_scheduleFootprintWithin_toTape_replicate
        (Q := Q) st k

def tapeTransferWithControlNetwork_concreteGoodStepSchedule_toTapeBar
    {s : Nat}
    (st st' : MicroState Q) (m k : Nat)
    (hm : m <= maxTape s)
    (hk : k <= m) :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (tapeTransferWithControlNetwork st st')
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      (k + 1)
      ({ state := st, tape := m } : MicroCfg Q s)
      ({ state := st', tape := m - k } : MicroCfg Q s) where
  schedule := tapeTransferWithControlToTapeBarSchedule st st' k
  exec :=
    tapeTransferWithControlNetwork_exec_toTapeBar
      (s := s) st st' m k hm hk
  length_le := by
    rw [tapeTransferWithControlToTapeBarSchedule_length]
  footprint := by
    simpa [aggregateLocalFootprint] using
      tapeTransferWithControlNetwork_scheduleFootprintWithin_toTapeBar
        (Q := Q) st st' k

def tapeTransferWithControlNetwork_concreteGoodStepSchedule_toTape
    {s : Nat}
    (st st' : MicroState Q) (m k : Nat)
    (hk : k <= maxTape s - m) :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (tapeTransferWithControlNetwork st st')
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      (k + 1)
      ({ state := st, tape := m } : MicroCfg Q s)
      ({ state := st', tape := m + k } : MicroCfg Q s) where
  schedule := tapeTransferWithControlToTapeSchedule st st' k
  exec :=
    tapeTransferWithControlNetwork_exec_toTape
      (s := s) st st' m k hk
  length_le := by
    rw [tapeTransferWithControlToTapeSchedule_length]
  footprint := by
    simpa [aggregateLocalFootprint] using
      tapeTransferWithControlNetwork_scheduleFootprintWithin_toTape
        (Q := Q) st st' k

def tapeTransferWithControlNetwork_concreteGoodStepSchedule_eraseMSBWith
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) (r : Bool)
    (hm : m <= maxTape s)
    (hk : Encoding.bitDigit r * 3 ^ s <= m) :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (tapeTransferWithControlNetwork st st')
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      (Encoding.bitDigit r * 3 ^ s + 1)
      ({ state := st, tape := m } : MicroCfg Q s)
      ({ state := st',
          tape := Encoding.eraseMSBWith s r m } : MicroCfg Q s) where
  schedule :=
    tapeTransferWithControlToTapeBarSchedule
      st st' (Encoding.bitDigit r * 3 ^ s)
  exec :=
    tapeTransferWithControlNetwork_exec_eraseMSBWith
      (s := s) st st' m r hm hk
  length_le := by
    rw [tapeTransferWithControlToTapeBarSchedule_length]
  footprint := by
    simpa [aggregateLocalFootprint] using
      tapeTransferWithControlNetwork_scheduleFootprintWithin_toTapeBar
        (Q := Q) st st' (Encoding.bitDigit r * 3 ^ s)

def tapeTransferWithControlNetwork_concreteGoodStepSchedule_writeLSB
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) (b : Bool)
    (hk : Encoding.bitDigit b <= maxTape s - m) :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (tapeTransferWithControlNetwork st st')
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      (Encoding.bitDigit b + 1)
      ({ state := st, tape := m } : MicroCfg Q s)
      ({ state := st',
          tape := Encoding.writeLSB m b } : MicroCfg Q s) where
  schedule := tapeTransferWithControlToTapeSchedule st st' (Encoding.bitDigit b)
  exec :=
    tapeTransferWithControlNetwork_exec_writeLSB
      (s := s) st st' m b hk
  length_le := by
    rw [tapeTransferWithControlToTapeSchedule_length]
  footprint := by
    simpa [aggregateLocalFootprint] using
      tapeTransferWithControlNetwork_scheduleFootprintWithin_toTape
        (Q := Q) st st' (Encoding.bitDigit b)

def tapeTransferWithControlNetwork_concreteGoodStepSchedule_shiftTail
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hTape : Encoding.IsBase3BoolTape s m) :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (tapeTransferWithControlNetwork st st')
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      (2 * m + 1)
      ({ state := st, tape := m } : MicroCfg Q s)
      ({ state := st',
          tape := Encoding.shiftTail m } : MicroCfg Q s) := by
  have hk : 2 * m <= maxTape s - m :=
    two_mul_le_tapeBar_of_lt_pow hTape.lt_pow
  have hshift : m + 2 * m = Encoding.shiftTail m := by
    unfold Encoding.shiftTail
    omega
  simpa [hshift] using
    tapeTransferWithControlNetwork_concreteGoodStepSchedule_toTape
      (s := s) st st' m (2 * m) hk

def tapeTransferWithControlNetwork_concreteGoodStepSchedule_of_phaseStep?_erase_exactBound
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s} {r : Bool}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = Phase4.erase)
    (hr : c.state.readSymbol = some r)
    (hstep : phaseStep? (s := s) M c = some c') :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (tapeTransferWithControlNetwork c.state c'.state)
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      (Encoding.bitDigit r * 3 ^ s + 1)
      c c' := by
  cases c with
  | mk st tape =>
      cases st with
      | mk q phase readSymbol pendingWrite pendingState =>
          cases phase <;> try cases hphase
          have hWF :
              (MicroCfg.TapeWF
                ({ state :=
                    ({ q := q, phase := Phase4.erase,
                       readSymbol := readSymbol,
                       pendingWrite := pendingWrite,
                       pendingState := pendingState } : MicroState Q),
                   tape := tape } : MicroCfg Q s)) :=
            hc.2
          cases readSymbol with
          | none =>
              simp at hr
          | some r0 =>
              cases hr
              have hTape : Encoding.IsBase3BoolTape (s + 1) tape :=
                hWF.1
              have hread : r = Encoding.readMSB? s tape :=
                hWF.2 r rfl
              have hm : tape <= maxTape s :=
                FourPhaseEncoding.le_maxTape_of_IsBase3BoolTape hTape
              have hk : Encoding.bitDigit r * 3 ^ s <= tape := by
                simpa using
                  Encoding.bitDigit_mul_pow_le_of_IsBase3BoolTape_read
                    hTape hread
              have hEq :
                  some
                    ({ state :=
                        MicroState.afterErase
                          ({ q := q, phase := Phase4.erase,
                             readSymbol := some r,
                             pendingWrite := pendingWrite,
                             pendingState := pendingState } : MicroState Q),
                       tape := Encoding.eraseMSBWith s r tape } :
                      MicroCfg Q s) =
                    some c' := by
                simpa [phaseStep?] using hstep
              cases hEq
              exact
                tapeTransferWithControlNetwork_concreteGoodStepSchedule_eraseMSBWith
                  (s := s)
                  ({ q := q, phase := Phase4.erase,
                     readSymbol := some r,
                     pendingWrite := pendingWrite,
                     pendingState := pendingState } : MicroState Q)
                  (MicroState.afterErase
                    ({ q := q, phase := Phase4.erase,
                       readSymbol := some r,
                       pendingWrite := pendingWrite,
                       pendingState := pendingState } : MicroState Q))
                  tape r hm hk

def tapeTransferWithControlNetwork_concreteGoodStepSchedule_of_phaseStep?_write_exactBound
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s} {b : Bool} {q' : Q}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = Phase4.write)
    (hwrite : c.state.pendingWrite = some b)
    (hstate : c.state.pendingState = some q')
    (hstep : phaseStep? (s := s) M c = some c') :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (tapeTransferWithControlNetwork c.state c'.state)
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      (Encoding.bitDigit b + 1)
      c c' := by
  cases c with
  | mk st tape =>
      cases st with
      | mk q phase readSymbol pendingWrite pendingState =>
          cases phase <;> try cases hphase
          have hTape : Encoding.IsShiftedBase3BoolTape s tape :=
            hc.2
          cases pendingWrite with
          | none =>
              simp at hwrite
          | some b0 =>
              cases hwrite
              cases pendingState with
              | none =>
                  simp at hstate
              | some q0 =>
                  cases hstate
                  have hk : Encoding.bitDigit b <= maxTape s - tape :=
                    FourPhaseEncoding.bitDigit_le_tapeBar_of_shifted hTape b
                  have hEq :
                      some
                        ({ state := MicroState.afterWrite q',
                           tape := Encoding.writeLSB tape b } :
                          MicroCfg Q s) =
                        some c' := by
                    simpa [phaseStep?] using hstep
                  cases hEq
                  exact
                    tapeTransferWithControlNetwork_concreteGoodStepSchedule_writeLSB
                      (s := s)
                      ({ q := q, phase := Phase4.write,
                         readSymbol := readSymbol,
                         pendingWrite := some b,
                         pendingState := some q' } : MicroState Q)
                      (MicroState.afterWrite q')
                      tape b hk

def tapeTransferWithControlNetwork_concreteGoodStepSchedule_of_phaseStep?_shift_exactBound
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = Phase4.shift)
    (hstep : phaseStep? (s := s) M c = some c') :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (tapeTransferWithControlNetwork c.state c'.state)
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      (2 * c.tape + 1)
      c c' := by
  have hTape : Encoding.IsBase3BoolTape s c.tape := by
    simpa [MicroCfg.TapeWF, hphase] using hc.2
  have hc' :
      c' =
        { state := MicroState.afterShift c.state,
          tape := Encoding.shiftTail c.tape } :=
    phaseStep?_eq_shiftTail_of_shift (s := s) M hphase hstep
  subst c'
  exact
    tapeTransferWithControlNetwork_concreteGoodStepSchedule_shiftTail
      (s := s) c.state (MicroState.afterShift c.state) c.tape hTape

def tapeTransferWithControlNetwork_concreteGoodStepSchedule_of_phaseStep?_erase
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = Phase4.erase)
    (hstep : phaseStep? (s := s) M c = some c') :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (tapeTransferWithControlNetwork c.state c'.state)
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      (maxTape s + 1)
      c c' := by
  cases c with
  | mk st tape =>
      cases st with
      | mk q phase readSymbol pendingWrite pendingState =>
          cases phase <;> try cases hphase
          have hWF :
              (MicroCfg.TapeWF
                ({ state :=
                    ({ q := q, phase := Phase4.erase,
                       readSymbol := readSymbol,
                       pendingWrite := pendingWrite,
                       pendingState := pendingState } : MicroState Q),
                   tape := tape } : MicroCfg Q s)) :=
            hc.2
          cases hReadSym : readSymbol with
          | none =>
              simp [phaseStep?, hReadSym] at hstep
          | some r =>
              have hTape : Encoding.IsBase3BoolTape (s + 1) tape :=
                hWF.1
              have hread : r = Encoding.readMSB? s tape :=
                hWF.2 r hReadSym
              have hm : tape <= maxTape s :=
                FourPhaseEncoding.le_maxTape_of_IsBase3BoolTape hTape
              have hk : Encoding.bitDigit r * 3 ^ s <= tape := by
                simpa using
                  Encoding.bitDigit_mul_pow_le_of_IsBase3BoolTape_read
                    hTape hread
              have hEq :
                  some
                    ({ state :=
                        MicroState.afterErase
                          ({ q := q, phase := Phase4.erase,
                             readSymbol := some r,
                             pendingWrite := pendingWrite,
                             pendingState := pendingState } : MicroState Q),
                       tape := Encoding.eraseMSBWith s r tape } :
                      MicroCfg Q s) =
                    some c' := by
                simpa [phaseStep?, hReadSym] using hstep
              cases hEq
              have hBound :
                  Encoding.bitDigit r * 3 ^ s + 1 <= maxTape s + 1 :=
                Nat.add_le_add_right (le_trans hk hm) 1
              exact
                (tapeTransferWithControlNetwork_concreteGoodStepSchedule_eraseMSBWith
                  (s := s)
                  ({ q := q, phase := Phase4.erase,
                     readSymbol := some r,
                     pendingWrite := pendingWrite,
                     pendingState := pendingState } : MicroState Q)
                  (MicroState.afterErase
                    ({ q := q, phase := Phase4.erase,
                       readSymbol := some r,
                       pendingWrite := pendingWrite,
                       pendingState := pendingState } : MicroState Q))
                  tape r hm hk).monoLength hBound

def tapeTransferWithControlNetwork_concreteGoodStepSchedule_of_phaseStep?_write
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = Phase4.write)
    (hstep : phaseStep? (s := s) M c = some c') :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (tapeTransferWithControlNetwork c.state c'.state)
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      3
      c c' := by
  cases c with
  | mk st tape =>
      cases st with
      | mk q phase readSymbol pendingWrite pendingState =>
          cases phase <;> try cases hphase
          have hTape : Encoding.IsShiftedBase3BoolTape s tape :=
            hc.2
          cases hWrite : pendingWrite with
          | none =>
              simp [phaseStep?, hWrite] at hstep
          | some w =>
              cases hState : pendingState with
              | none =>
                  simp [phaseStep?, hWrite, hState] at hstep
              | some qNext =>
                  have hk : Encoding.bitDigit w <= maxTape s - tape :=
                    FourPhaseEncoding.bitDigit_le_tapeBar_of_shifted hTape w
                  have hEq :
                      some
                        ({ state := MicroState.afterWrite qNext,
                           tape := Encoding.writeLSB tape w } :
                          MicroCfg Q s) =
                        some c' := by
                    simpa [phaseStep?, hWrite, hState] using hstep
                  cases hEq
                  have hBound : Encoding.bitDigit w + 1 <= 3 := by
                    cases w <;> simp [Encoding.bitDigit]
                  exact
                    (tapeTransferWithControlNetwork_concreteGoodStepSchedule_writeLSB
                      (s := s)
                      ({ q := q, phase := Phase4.write,
                         readSymbol := readSymbol,
                         pendingWrite := some w,
                         pendingState := some qNext } : MicroState Q)
                      (MicroState.afterWrite qNext)
                      tape w hk).monoLength hBound

def tapeTransferWithControlNetwork_concreteGoodStepSchedule_of_phaseStep?_shift
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = Phase4.shift)
    (hstep : phaseStep? (s := s) M c = some c') :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (tapeTransferWithControlNetwork c.state c'.state)
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      (maxTape s + 1)
      c c' := by
  have hTape : Encoding.IsBase3BoolTape s c.tape := by
    simpa [MicroCfg.TapeWF, hphase] using hc.2
  have hk : 2 * c.tape <= maxTape s - c.tape :=
    two_mul_le_tapeBar_of_lt_pow hTape.lt_pow
  have hBound : 2 * c.tape + 1 <= maxTape s + 1 :=
    Nat.add_le_add_right (le_trans hk (Nat.sub_le _ _)) 1
  exact
    (tapeTransferWithControlNetwork_concreteGoodStepSchedule_of_phaseStep?_shift_exactBound
      (s := s) M hc hphase hstep).monoLength hBound

def controlSwapNetwork_concreteGoodStepSchedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (controlSwapNetwork st st')
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      1
      ({ state := st, tape := m } : MicroCfg Q s)
      ({ state := st', tape := m } : MicroCfg Q s) where
  schedule := [Network.OneRxnIdx.step]
  exec := controlSwapNetwork_exec (s := s) st st' m
  length_le := by simp
  footprint := by
    simpa [aggregateLocalFootprint] using
      controlSwapNetwork_scheduleFootprintWithin (Q := Q) st st'

def controlSwapNetwork_concreteGoodStepSchedule_of_phaseStep?_read_exactBound
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s} {w : Bool} {q' : Q}
    (hphase : c.state.phase = Phase4.read)
    (hdelta :
      M.delta c.state.q (Encoding.readMSB? s c.tape) = some (w, q'))
    (hstep : phaseStep? (s := s) M c = some c') :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (controlSwapNetwork c.state c'.state)
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      1
      c c' := by
  have hc' :
      c' =
        { state :=
            MicroState.afterRead c.state
              (Encoding.readMSB? s c.tape) w q',
          tape := c.tape } :=
    phaseStep?_eq_afterRead_of_read (s := s) M hphase hdelta hstep
  subst c'
  exact
    controlSwapNetwork_concreteGoodStepSchedule
      (s := s)
      c.state
      (MicroState.afterRead c.state (Encoding.readMSB? s c.tape) w q')
      c.tape

def controlSwapNetwork_concreteGoodStepSchedule_of_phaseStep?_read
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s}
    (hphase : c.state.phase = Phase4.read)
    (hstep : phaseStep? (s := s) M c = some c') :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (controlSwapNetwork c.state c'.state)
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      1
      c c' := by
  cases hdelta :
      M.delta c.state.q (Encoding.readMSB? s c.tape) with
  | none =>
      cases c with
      | mk st tape =>
          cases st with
          | mk q phase readSymbol pendingWrite pendingState =>
              cases phase <;> try cases hphase
              simp [phaseStep?, hdelta] at hstep
  | some out =>
      rcases out with ⟨w, q'⟩
      exact
        controlSwapNetwork_concreteGoodStepSchedule_of_phaseStep?_read_exactBound
          (s := s) M hphase hdelta hstep

def statePairNetwork
    (Npair : MicroState Q -> MicroState Q -> Network (Species Q)) :
    Network (Species Q) :=
  Network.sigma
    (fun pair : MicroState Q × MicroState Q =>
      Npair pair.1 pair.2)

omit [DecidableEq Q] in
theorem statePairNetwork_allAtMostBimolecularFull
    (Npair : MicroState Q -> MicroState Q -> Network (Species Q))
    (h : forall st st', (Npair st st').allAtMostBimolecularFull) :
    (statePairNetwork Npair).allAtMostBimolecularFull := by
  exact
    (Network.sigma_allAtMostBimolecularFull_iff
      (fun pair : MicroState Q × MicroState Q =>
        Npair pair.1 pair.2)).2
      (by
        intro pair
        exact h pair.1 pair.2)

omit [DecidableEq Q] in
theorem statePairNetwork_allAtMostBimolecularInput
    (Npair : MicroState Q -> MicroState Q -> Network (Species Q))
    (h : forall st st', (Npair st st').allAtMostBimolecularFull) :
    (statePairNetwork Npair).allAtMostBimolecularInput :=
  Network.allAtMostBimolecularInput_of_full
    (statePairNetwork_allAtMostBimolecularFull Npair h)

omit [DecidableEq Q] in
theorem statePairNetwork_allAtMostBimolecularOutput
    (Npair : MicroState Q -> MicroState Q -> Network (Species Q))
    (h : forall st st', (Npair st st').allAtMostBimolecularFull) :
    (statePairNetwork Npair).allAtMostBimolecularOutput :=
  Network.allAtMostBimolecularOutput_of_full
    (statePairNetwork_allAtMostBimolecularFull Npair h)

omit [DecidableEq Q] in
theorem statePairNetwork_allUnitRate
    (Npair : MicroState Q -> MicroState Q -> Network (Species Q))
    (h : forall st st', (Npair st st').allUnitRate) :
    (statePairNetwork Npair).allUnitRate := by
  exact
    (Network.sigma_allUnitRate_iff
      (fun pair : MicroState Q × MicroState Q =>
        Npair pair.1 pair.2)).2
      (by
        intro pair
        exact h pair.1 pair.2)

omit [DecidableEq Q] in
theorem statePairNetwork_hasPositiveRates
    (Npair : MicroState Q -> MicroState Q -> Network (Species Q))
    (h : forall st st', (Npair st st').allUnitRate) :
    (statePairNetwork Npair).hasPositiveRates :=
  Network.hasPositiveRates_of_allUnitRate
    (statePairNetwork_allUnitRate Npair h)

omit [DecidableEq Q] in
theorem statePairNetwork_equalRates
    (Npair : MicroState Q -> MicroState Q -> Network (Species Q))
    (h : forall st st', (Npair st st').allUnitRate) :
    (statePairNetwork Npair).equalRates :=
  Network.equalRates_of_allUnitRate
    (statePairNetwork_allUnitRate Npair h)

def statePairNetwork_concreteGoodStepSchedule
    {s : Nat}
    (Npair : MicroState Q -> MicroState Q -> Network (Species Q))
    {Foot : MicroCfg Q s -> MicroCfg Q s -> Species Q -> Prop}
    {L : Nat} {c c' : MicroCfg Q s}
    (Sched :
      FourPhaseConcrete.ConcreteGoodStepSchedule
        (Npair c.state c'.state)
        (enc : MicroCfg Q s -> State (Species Q))
        Foot L c c') :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (statePairNetwork Npair)
      (enc : MicroCfg Q s -> State (Species Q))
      Foot L c c' :=
  FourPhaseConcrete.ConcreteGoodStepSchedule.liftSigma
    (fun pair : MicroState Q × MicroState Q =>
      Npair pair.1 pair.2)
    (c.state, c'.state)
    Sched

def controlSwapStatePairNetwork :
    Network (Species Q) :=
  statePairNetwork
    (fun st st' => controlSwapNetwork st st')

theorem controlSwapStatePairNetwork_allAtMostBimolecularFull :
    (controlSwapStatePairNetwork (Q := Q)).allAtMostBimolecularFull :=
  statePairNetwork_allAtMostBimolecularFull
    (fun st st' => controlSwapNetwork st st')
    (by
      intro st st'
      exact controlSwapNetwork_allAtMostBimolecularFull st st')

theorem controlSwapStatePairNetwork_allAtMostBimolecularInput :
    (controlSwapStatePairNetwork (Q := Q)).allAtMostBimolecularInput :=
  Network.allAtMostBimolecularInput_of_full
    controlSwapStatePairNetwork_allAtMostBimolecularFull

theorem controlSwapStatePairNetwork_allAtMostBimolecularOutput :
    (controlSwapStatePairNetwork (Q := Q)).allAtMostBimolecularOutput :=
  Network.allAtMostBimolecularOutput_of_full
    controlSwapStatePairNetwork_allAtMostBimolecularFull

theorem controlSwapStatePairNetwork_allUnitRate :
    (controlSwapStatePairNetwork (Q := Q)).allUnitRate :=
  statePairNetwork_allUnitRate
    (fun st st' => controlSwapNetwork st st')
    (by
      intro st st'
      exact controlSwapNetwork_allUnitRate st st')

theorem controlSwapStatePairNetwork_hasPositiveRates :
    (controlSwapStatePairNetwork (Q := Q)).hasPositiveRates :=
  Network.hasPositiveRates_of_allUnitRate
    controlSwapStatePairNetwork_allUnitRate

theorem controlSwapStatePairNetwork_equalRates :
    (controlSwapStatePairNetwork (Q := Q)).equalRates :=
  Network.equalRates_of_allUnitRate
    controlSwapStatePairNetwork_allUnitRate

def controlSwapStatePairNetwork_concreteGoodStepSchedule
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (controlSwapStatePairNetwork (Q := Q))
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      1
      ({ state := st, tape := m } : MicroCfg Q s)
      ({ state := st', tape := m } : MicroCfg Q s) :=
  statePairNetwork_concreteGoodStepSchedule
    (fun st st' => controlSwapNetwork st st')
    (controlSwapNetwork_concreteGoodStepSchedule
      (s := s) st st' m)

def controlSwapStatePairNetwork_concreteGoodStepSchedule_of_phaseStep?_read_exactBound
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s} {w : Bool} {q' : Q}
    (hphase : c.state.phase = Phase4.read)
    (hdelta :
      M.delta c.state.q (Encoding.readMSB? s c.tape) = some (w, q'))
    (hstep : phaseStep? (s := s) M c = some c') :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (controlSwapStatePairNetwork (Q := Q))
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      1
      c c' :=
  statePairNetwork_concreteGoodStepSchedule
    (fun st st' => controlSwapNetwork st st')
    (controlSwapNetwork_concreteGoodStepSchedule_of_phaseStep?_read_exactBound
      (s := s) M hphase hdelta hstep)

def controlSwapStatePairNetwork_concreteGoodStepSchedule_of_phaseStep?_read
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s}
    (hphase : c.state.phase = Phase4.read)
    (hstep : phaseStep? (s := s) M c = some c') :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (controlSwapStatePairNetwork (Q := Q))
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      1
      c c' :=
  statePairNetwork_concreteGoodStepSchedule
    (fun st st' => controlSwapNetwork st st')
    (controlSwapNetwork_concreteGoodStepSchedule_of_phaseStep?_read
      (s := s) M hphase hstep)

def tapeTransferWithControlStatePairNetwork :
    Network (Species Q) :=
  statePairNetwork
    (fun st st' => tapeTransferWithControlNetwork st st')

theorem tapeTransferWithControlStatePairNetwork_allAtMostBimolecularFull :
    (tapeTransferWithControlStatePairNetwork (Q := Q)).allAtMostBimolecularFull :=
  statePairNetwork_allAtMostBimolecularFull
    (fun st st' => tapeTransferWithControlNetwork st st')
    (by
      intro st st'
      exact tapeTransferWithControlNetwork_allAtMostBimolecularFull st st')

theorem tapeTransferWithControlStatePairNetwork_allAtMostBimolecularInput :
    (tapeTransferWithControlStatePairNetwork (Q := Q)).allAtMostBimolecularInput :=
  Network.allAtMostBimolecularInput_of_full
    tapeTransferWithControlStatePairNetwork_allAtMostBimolecularFull

theorem tapeTransferWithControlStatePairNetwork_allAtMostBimolecularOutput :
    (tapeTransferWithControlStatePairNetwork (Q := Q)).allAtMostBimolecularOutput :=
  Network.allAtMostBimolecularOutput_of_full
    tapeTransferWithControlStatePairNetwork_allAtMostBimolecularFull

theorem tapeTransferWithControlStatePairNetwork_allUnitRate :
    (tapeTransferWithControlStatePairNetwork (Q := Q)).allUnitRate :=
  statePairNetwork_allUnitRate
    (fun st st' => tapeTransferWithControlNetwork st st')
    (by
      intro st st'
      exact tapeTransferWithControlNetwork_allUnitRate st st')

theorem tapeTransferWithControlStatePairNetwork_hasPositiveRates :
    (tapeTransferWithControlStatePairNetwork (Q := Q)).hasPositiveRates :=
  Network.hasPositiveRates_of_allUnitRate
    tapeTransferWithControlStatePairNetwork_allUnitRate

theorem tapeTransferWithControlStatePairNetwork_equalRates :
    (tapeTransferWithControlStatePairNetwork (Q := Q)).equalRates :=
  Network.equalRates_of_allUnitRate
    tapeTransferWithControlStatePairNetwork_allUnitRate

def tapeTransferWithControlStatePairNetwork_concreteGoodStepSchedule_toTapeBar
    {s : Nat}
    (st st' : MicroState Q) (m k : Nat)
    (hm : m <= maxTape s)
    (hk : k <= m) :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (tapeTransferWithControlStatePairNetwork (Q := Q))
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      (k + 1)
      ({ state := st, tape := m } : MicroCfg Q s)
      ({ state := st', tape := m - k } : MicroCfg Q s) :=
  statePairNetwork_concreteGoodStepSchedule
    (fun st st' => tapeTransferWithControlNetwork st st')
    (tapeTransferWithControlNetwork_concreteGoodStepSchedule_toTapeBar
      (s := s) st st' m k hm hk)

def tapeTransferWithControlStatePairNetwork_concreteGoodStepSchedule_toTape
    {s : Nat}
    (st st' : MicroState Q) (m k : Nat)
    (hk : k <= maxTape s - m) :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (tapeTransferWithControlStatePairNetwork (Q := Q))
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      (k + 1)
      ({ state := st, tape := m } : MicroCfg Q s)
      ({ state := st', tape := m + k } : MicroCfg Q s) :=
  statePairNetwork_concreteGoodStepSchedule
    (fun st st' => tapeTransferWithControlNetwork st st')
    (tapeTransferWithControlNetwork_concreteGoodStepSchedule_toTape
      (s := s) st st' m k hk)

def tapeTransferWithControlStatePairNetwork_concreteGoodStepSchedule_eraseMSBWith
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) (r : Bool)
    (hm : m <= maxTape s)
    (hk : Encoding.bitDigit r * 3 ^ s <= m) :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (tapeTransferWithControlStatePairNetwork (Q := Q))
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      (Encoding.bitDigit r * 3 ^ s + 1)
      ({ state := st, tape := m } : MicroCfg Q s)
      ({ state := st',
          tape := Encoding.eraseMSBWith s r m } : MicroCfg Q s) :=
  statePairNetwork_concreteGoodStepSchedule
    (fun st st' => tapeTransferWithControlNetwork st st')
    (tapeTransferWithControlNetwork_concreteGoodStepSchedule_eraseMSBWith
      (s := s) st st' m r hm hk)

def tapeTransferWithControlStatePairNetwork_concreteGoodStepSchedule_writeLSB
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) (b : Bool)
    (hk : Encoding.bitDigit b <= maxTape s - m) :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (tapeTransferWithControlStatePairNetwork (Q := Q))
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      (Encoding.bitDigit b + 1)
      ({ state := st, tape := m } : MicroCfg Q s)
      ({ state := st',
          tape := Encoding.writeLSB m b } : MicroCfg Q s) :=
  statePairNetwork_concreteGoodStepSchedule
    (fun st st' => tapeTransferWithControlNetwork st st')
    (tapeTransferWithControlNetwork_concreteGoodStepSchedule_writeLSB
      (s := s) st st' m b hk)

def tapeTransferWithControlStatePairNetwork_concreteGoodStepSchedule_shiftTail
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hTape : Encoding.IsBase3BoolTape s m) :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (tapeTransferWithControlStatePairNetwork (Q := Q))
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      (2 * m + 1)
      ({ state := st, tape := m } : MicroCfg Q s)
      ({ state := st',
          tape := Encoding.shiftTail m } : MicroCfg Q s) :=
  statePairNetwork_concreteGoodStepSchedule
    (fun st st' => tapeTransferWithControlNetwork st st')
    (tapeTransferWithControlNetwork_concreteGoodStepSchedule_shiftTail
      (s := s) st st' m hTape)

def tapeTransferWithControlStatePairNetwork_concreteGoodStepSchedule_of_phaseStep?_erase_exactBound
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s} {r : Bool}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = Phase4.erase)
    (hr : c.state.readSymbol = some r)
    (hstep : phaseStep? (s := s) M c = some c') :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (tapeTransferWithControlStatePairNetwork (Q := Q))
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      (Encoding.bitDigit r * 3 ^ s + 1)
      c c' :=
  statePairNetwork_concreteGoodStepSchedule
    (fun st st' => tapeTransferWithControlNetwork st st')
    (tapeTransferWithControlNetwork_concreteGoodStepSchedule_of_phaseStep?_erase_exactBound
      (s := s) M hc hphase hr hstep)

def tapeTransferWithControlStatePairNetwork_concreteGoodStepSchedule_of_phaseStep?_write_exactBound
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s} {b : Bool} {q' : Q}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = Phase4.write)
    (hwrite : c.state.pendingWrite = some b)
    (hstate : c.state.pendingState = some q')
    (hstep : phaseStep? (s := s) M c = some c') :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (tapeTransferWithControlStatePairNetwork (Q := Q))
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      (Encoding.bitDigit b + 1)
      c c' :=
  statePairNetwork_concreteGoodStepSchedule
    (fun st st' => tapeTransferWithControlNetwork st st')
    (tapeTransferWithControlNetwork_concreteGoodStepSchedule_of_phaseStep?_write_exactBound
      (s := s) M hc hphase hwrite hstate hstep)

def tapeTransferWithControlStatePairNetwork_concreteGoodStepSchedule_of_phaseStep?_shift_exactBound
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = Phase4.shift)
    (hstep : phaseStep? (s := s) M c = some c') :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (tapeTransferWithControlStatePairNetwork (Q := Q))
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      (2 * c.tape + 1)
      c c' :=
  statePairNetwork_concreteGoodStepSchedule
    (fun st st' => tapeTransferWithControlNetwork st st')
    (tapeTransferWithControlNetwork_concreteGoodStepSchedule_of_phaseStep?_shift_exactBound
      (s := s) M hc hphase hstep)

def tapeTransferWithControlStatePairNetwork_concreteGoodStepSchedule_of_phaseStep?_erase
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = Phase4.erase)
    (hstep : phaseStep? (s := s) M c = some c') :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (tapeTransferWithControlStatePairNetwork (Q := Q))
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      (maxTape s + 1)
      c c' :=
  statePairNetwork_concreteGoodStepSchedule
    (fun st st' => tapeTransferWithControlNetwork st st')
    (tapeTransferWithControlNetwork_concreteGoodStepSchedule_of_phaseStep?_erase
      (s := s) M hc hphase hstep)

def tapeTransferWithControlStatePairNetwork_concreteGoodStepSchedule_of_phaseStep?_write
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = Phase4.write)
    (hstep : phaseStep? (s := s) M c = some c') :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (tapeTransferWithControlStatePairNetwork (Q := Q))
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      3
      c c' :=
  statePairNetwork_concreteGoodStepSchedule
    (fun st st' => tapeTransferWithControlNetwork st st')
    (tapeTransferWithControlNetwork_concreteGoodStepSchedule_of_phaseStep?_write
      (s := s) M hc hphase hstep)

def tapeTransferWithControlStatePairNetwork_concreteGoodStepSchedule_of_phaseStep?_shift
    {s : Nat} (M : Binary Q)
    {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (hphase : c.state.phase = Phase4.shift)
    (hstep : phaseStep? (s := s) M c = some c') :
    FourPhaseConcrete.ConcreteGoodStepSchedule
      (tapeTransferWithControlStatePairNetwork (Q := Q))
      (enc : MicroCfg Q s -> State (Species Q))
      aggregateLocalFootprint
      (maxTape s + 1)
      c c' :=
  statePairNetwork_concreteGoodStepSchedule
    (fun st st' => tapeTransferWithControlNetwork st st')
    (tapeTransferWithControlNetwork_concreteGoodStepSchedule_of_phaseStep?_shift
      (s := s) M hc hphase hstep)

def noAuxFootprint {s : Nat}
    (_c _c' : MicroCfg Q s) (_species : Species Q) : Prop :=
  False

omit [Fintype Q] [DecidableEq Q] in
theorem noAuxFootprint_disjoint_ideal {s : Nat}
    {c c' : MicroCfg Q s} (species : Species Q) :
    Not (noAuxFootprint c c' species) := by
  intro h
  exact h

omit [Fintype Q] [DecidableEq Q] in
theorem aggregateLocalFootprint_le_visibleConcreteLocalFootprint
    {s : Nat} {c c' : MicroCfg Q s} :
    forall species,
      aggregateLocalFootprint c c' species ->
        FourPhaseConcrete.ConcreteLocalFootprint
          (fun species : Species Q => species)
          noAuxFootprint c c' species := by
  intro species hLocal
  exact Or.inl ⟨species, hLocal, rfl⟩

def controlSwapStatePairNetwork_readFootprintedPhaseExpansion
    {s : Nat} (M : Binary Q) :
    FourPhaseConcrete.FootprintedConcretePhaseExpansion
      (s := s) (CSp := Species Q)
      M Phase4.read
      (enc : MicroCfg Q s -> State (Species Q))
      (fun species : Species Q => species) where
  N := controlSwapStatePairNetwork (Q := Q)
  step_len_bound := 1
  allAtMostBimolecularInput :=
    controlSwapStatePairNetwork_allAtMostBimolecularInput (Q := Q)
  hasPositiveRates :=
    controlSwapStatePairNetwork_hasPositiveRates (Q := Q)
  auxFootprint := noAuxFootprint
  auxFootprint_disjoint_ideal := by
    intro c c' species hAux
    exact hAux
  step_schedule := by
    intro c c' _hc hphase hstep
    exact
      (controlSwapStatePairNetwork_concreteGoodStepSchedule_of_phaseStep?_read
        (s := s) M hphase hstep).monoFootprint
        aggregateLocalFootprint_le_visibleConcreteLocalFootprint

def tapeTransferWithControlStatePairNetwork_eraseFootprintedPhaseExpansion
    {s : Nat} (M : Binary Q) :
    FourPhaseConcrete.FootprintedConcretePhaseExpansion
      (s := s) (CSp := Species Q)
      M Phase4.erase
      (enc : MicroCfg Q s -> State (Species Q))
      (fun species : Species Q => species) where
  N := tapeTransferWithControlStatePairNetwork (Q := Q)
  step_len_bound := maxTape s + 1
  allAtMostBimolecularInput :=
    tapeTransferWithControlStatePairNetwork_allAtMostBimolecularInput
      (Q := Q)
  hasPositiveRates :=
    tapeTransferWithControlStatePairNetwork_hasPositiveRates (Q := Q)
  auxFootprint := noAuxFootprint
  auxFootprint_disjoint_ideal := by
    intro c c' species hAux
    exact hAux
  step_schedule := by
    intro c c' hc hphase hstep
    exact
      (tapeTransferWithControlStatePairNetwork_concreteGoodStepSchedule_of_phaseStep?_erase
        (s := s) M hc hphase hstep).monoFootprint
        aggregateLocalFootprint_le_visibleConcreteLocalFootprint

def tapeTransferWithControlStatePairNetwork_shiftFootprintedPhaseExpansion
    {s : Nat} (M : Binary Q) :
    FourPhaseConcrete.FootprintedConcretePhaseExpansion
      (s := s) (CSp := Species Q)
      M Phase4.shift
      (enc : MicroCfg Q s -> State (Species Q))
      (fun species : Species Q => species) where
  N := tapeTransferWithControlStatePairNetwork (Q := Q)
  step_len_bound := maxTape s + 1
  allAtMostBimolecularInput :=
    tapeTransferWithControlStatePairNetwork_allAtMostBimolecularInput
      (Q := Q)
  hasPositiveRates :=
    tapeTransferWithControlStatePairNetwork_hasPositiveRates (Q := Q)
  auxFootprint := noAuxFootprint
  auxFootprint_disjoint_ideal := by
    intro c c' species hAux
    exact hAux
  step_schedule := by
    intro c c' hc hphase hstep
    exact
      (tapeTransferWithControlStatePairNetwork_concreteGoodStepSchedule_of_phaseStep?_shift
        (s := s) M hc hphase hstep).monoFootprint
        aggregateLocalFootprint_le_visibleConcreteLocalFootprint

def tapeTransferWithControlStatePairNetwork_writeFootprintedPhaseExpansion
    {s : Nat} (M : Binary Q) :
    FourPhaseConcrete.FootprintedConcretePhaseExpansion
      (s := s) (CSp := Species Q)
      M Phase4.write
      (enc : MicroCfg Q s -> State (Species Q))
      (fun species : Species Q => species) where
  N := tapeTransferWithControlStatePairNetwork (Q := Q)
  step_len_bound := 3
  allAtMostBimolecularInput :=
    tapeTransferWithControlStatePairNetwork_allAtMostBimolecularInput
      (Q := Q)
  hasPositiveRates :=
    tapeTransferWithControlStatePairNetwork_hasPositiveRates (Q := Q)
  auxFootprint := noAuxFootprint
  auxFootprint_disjoint_ideal := by
    intro c c' species hAux
    exact hAux
  step_schedule := by
    intro c c' hc hphase hstep
    exact
      (tapeTransferWithControlStatePairNetwork_concreteGoodStepSchedule_of_phaseStep?_write
        (s := s) M hc hphase hstep).monoFootprint
        aggregateLocalFootprint_le_visibleConcreteLocalFootprint

def statePairTransferFootprintedConcreteFourPhaseExpansionFamily
    {s : Nat} (M : Binary Q) :
    FourPhaseConcrete.FootprintedConcreteFourPhaseExpansionFamily
      (s := s) M where
  CSp := Species Q
  instFintype := inferInstance
  instDecidableEq := inferInstance
  enc := enc
  ideal := fun species => species
  ideal_injective := by
    intro species species' h
    exact h
  enc_ideal := by
    intro c species
    rfl
  read :=
    controlSwapStatePairNetwork_readFootprintedPhaseExpansion
      (s := s) M
  erase :=
    tapeTransferWithControlStatePairNetwork_eraseFootprintedPhaseExpansion
      (s := s) M
  shift :=
    tapeTransferWithControlStatePairNetwork_shiftFootprintedPhaseExpansion
      (s := s) M
  write :=
    tapeTransferWithControlStatePairNetwork_writeFootprintedPhaseExpansion
      (s := s) M

def statePairTransferConcreteFourPhaseExpansionFamily
    {s : Nat} (M : Binary Q) :
    FourPhaseConcrete.ConcreteFourPhaseExpansionFamily
      (s := s) M :=
  (statePairTransferFootprintedConcreteFourPhaseExpansionFamily
    (s := s) M).toConcreteFourPhaseExpansionFamily

def statePairTransferFootprintedConcreteFourPhaseModule
    {s : Nat} (M : Binary Q) :
    FourPhaseConcrete.FootprintedConcreteFourPhaseModule
      (s := s) M :=
  (statePairTransferFootprintedConcreteFourPhaseExpansionFamily
    (s := s) M).toFootprintedConcreteFourPhaseModule

def statePairTransferConcreteFourPhaseModule
    {s : Nat} (M : Binary Q) :
    ConcreteFourPhaseModule
      (s := s) M :=
  (statePairTransferConcreteFourPhaseExpansionFamily
    (s := s) M).toConcreteFourPhaseModule

end FourPhaseEncoding

end CTM

end Ripple.sCRNUniversality
