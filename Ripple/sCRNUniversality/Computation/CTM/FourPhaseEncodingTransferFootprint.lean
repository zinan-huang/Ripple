import Ripple.sCRNUniversality.Computation.CTM.FourPhaseEncodingTransfer
import Ripple.sCRNUniversality.Computation.CTM.FourPhaseFootprint

namespace Ripple.sCRNUniversality

namespace CTM

namespace FourPhaseEncoding

universe u

variable {Q : Type u} [DecidableEq Q]

set_option linter.flexible false in
theorem aggregateReaction_footprintWithin
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat) :
    (aggregateReaction st st'
      tapeIn tapeBarIn tapeOut tapeBarOut).FootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st')) := by
  intro species hTouches
  cases species with
  | ctrl q phase readSymbol pendingWrite pendingState =>
      rcases hTouches with hInput | hOutput
      · exact Or.inl (by
          by_contra hne
          exact hInput (by
            simp [aggregateReaction, aggregateInput, State.add,
              State.single, FourPhaseSpecies.ctrlOf]
            intro hq hphase hread hwrite hstate
            exact hne (by
              cases hq
              cases hphase
              cases hread
              cases hwrite
              cases hstate
              rfl)))
      · exact Or.inr (Or.inl (by
          by_contra hne
          exact hOutput (by
            simp [aggregateReaction, aggregateOutput, State.add,
              State.single, FourPhaseSpecies.ctrlOf]
            intro hq hphase hread hwrite hstate
            exact hne (by
              cases hq
              cases hphase
              cases hread
              cases hwrite
              cases hstate
              rfl))))
  | tape =>
      exact FourPhaseSpecies.localMacroFootprint_tape
        (FourPhaseSpecies.ctrlOf st) (FourPhaseSpecies.ctrlOf st')
  | tapeBar =>
      exact FourPhaseSpecies.localMacroFootprint_tapeBar
        (FourPhaseSpecies.ctrlOf st) (FourPhaseSpecies.ctrlOf st')

theorem preserveTapeReaction_footprintWithin
    (st st' : MicroState Q) (k : Nat) :
    (preserveTapeReaction st st' k).FootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st')) := by
  simpa [preserveTapeReaction] using
    aggregateReaction_footprintWithin
      (Q := Q) st st' k 0 k 0

theorem preserveTapeBarReaction_footprintWithin
    (st st' : MicroState Q) (k : Nat) :
    (preserveTapeBarReaction st st' k).FootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st')) := by
  simpa [preserveTapeBarReaction] using
    aggregateReaction_footprintWithin
      (Q := Q) st st' 0 k 0 k

theorem transferTapeToTapeBarReaction_footprintWithin
    (st st' : MicroState Q) (k : Nat) :
    (transferTapeToTapeBarReaction st st' k).FootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st')) := by
  simpa [transferTapeToTapeBarReaction] using
    aggregateReaction_footprintWithin
      (Q := Q) st st' k 0 0 k

theorem transferTapeBarToTapeReaction_footprintWithin
    (st st' : MicroState Q) (k : Nat) :
    (transferTapeBarToTapeReaction st st' k).FootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st')) := by
  simpa [transferTapeBarToTapeReaction] using
    aggregateReaction_footprintWithin
      (Q := Q) st st' 0 k k 0

theorem controlSwapReaction_footprintWithin
    (st st' : MicroState Q) :
    (controlSwapReaction st st').FootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st')) := by
  simpa [controlSwapReaction] using
    aggregateReaction_footprintWithin
      (Q := Q) st st' 0 0 0 0

theorem aggregateNetwork_footprintWithin
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat) :
    (aggregateNetwork st st'
      tapeIn tapeBarIn tapeOut tapeBarOut).FootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st')) :=
  Network.oneRxnNetwork_footprintWithin (by
    simpa [aggregateNetwork] using
      aggregateReaction_footprintWithin
        (Q := Q) st st'
        tapeIn tapeBarIn tapeOut tapeBarOut)

theorem preserveTapeUnitNetwork_footprintWithin
    (st st' : MicroState Q) :
    (preserveTapeUnitNetwork st st').FootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st')) :=
  Network.oneRxnNetwork_footprintWithin (by
    simpa [preserveTapeUnitNetwork] using
      preserveTapeReaction_footprintWithin (Q := Q) st st' 1)

theorem preserveTapeBarUnitNetwork_footprintWithin
    (st st' : MicroState Q) :
    (preserveTapeBarUnitNetwork st st').FootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st')) :=
  Network.oneRxnNetwork_footprintWithin (by
    simpa [preserveTapeBarUnitNetwork] using
      preserveTapeBarReaction_footprintWithin (Q := Q) st st' 1)

theorem transferTapeToTapeBarUnitNetwork_footprintWithin
    (st st' : MicroState Q) :
    (transferTapeToTapeBarUnitNetwork st st').FootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st')) :=
  Network.oneRxnNetwork_footprintWithin (by
    simpa [transferTapeToTapeBarUnitNetwork] using
      transferTapeToTapeBarReaction_footprintWithin (Q := Q) st st' 1)

theorem transferTapeBarToTapeUnitNetwork_footprintWithin
    (st st' : MicroState Q) :
    (transferTapeBarToTapeUnitNetwork st st').FootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st')) :=
  Network.oneRxnNetwork_footprintWithin (by
    simpa [transferTapeBarToTapeUnitNetwork] using
      transferTapeBarToTapeReaction_footprintWithin (Q := Q) st st' 1)

theorem controlSwapNetwork_footprintWithin
    (st st' : MicroState Q) :
    (controlSwapNetwork st st').FootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st')) :=
  Network.oneRxnNetwork_footprintWithin (by
    simpa [controlSwapNetwork] using
      controlSwapReaction_footprintWithin (Q := Q) st st')

theorem aggregateNetwork_scheduleFootprintWithin_singleton
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat) :
    (aggregateNetwork st st'
      tapeIn tapeBarIn tapeOut tapeBarOut).ScheduleFootprintWithin
      [Network.OneRxnIdx.step]
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st')) :=
  Network.oneRxnNetwork_scheduleFootprintWithin (by
    simpa [aggregateNetwork] using
      aggregateReaction_footprintWithin
        (Q := Q) st st'
        tapeIn tapeBarIn tapeOut tapeBarOut)

theorem preserveTapeUnitNetwork_scheduleFootprintWithin
    (st st' : MicroState Q) :
    (preserveTapeUnitNetwork st st').ScheduleFootprintWithin
      [Network.OneRxnIdx.step]
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st')) :=
  Network.oneRxnNetwork_scheduleFootprintWithin (by
    simpa [preserveTapeUnitNetwork] using
      preserveTapeReaction_footprintWithin (Q := Q) st st' 1)

theorem preserveTapeBarUnitNetwork_scheduleFootprintWithin
    (st st' : MicroState Q) :
    (preserveTapeBarUnitNetwork st st').ScheduleFootprintWithin
      [Network.OneRxnIdx.step]
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st')) :=
  Network.oneRxnNetwork_scheduleFootprintWithin (by
    simpa [preserveTapeBarUnitNetwork] using
      preserveTapeBarReaction_footprintWithin (Q := Q) st st' 1)

theorem transferTapeToTapeBarUnitNetwork_scheduleFootprintWithin
    (st st' : MicroState Q) :
    (transferTapeToTapeBarUnitNetwork st st').ScheduleFootprintWithin
      [Network.OneRxnIdx.step]
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st')) :=
  Network.oneRxnNetwork_scheduleFootprintWithin (by
    simpa [transferTapeToTapeBarUnitNetwork] using
      transferTapeToTapeBarReaction_footprintWithin (Q := Q) st st' 1)

theorem transferTapeBarToTapeUnitNetwork_scheduleFootprintWithin
    (st st' : MicroState Q) :
    (transferTapeBarToTapeUnitNetwork st st').ScheduleFootprintWithin
      [Network.OneRxnIdx.step]
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st')) :=
  Network.oneRxnNetwork_scheduleFootprintWithin (by
    simpa [transferTapeBarToTapeUnitNetwork] using
      transferTapeBarToTapeReaction_footprintWithin (Q := Q) st st' 1)

theorem controlSwapNetwork_scheduleFootprintWithin
    (st st' : MicroState Q) :
    (controlSwapNetwork st st').ScheduleFootprintWithin
      [Network.OneRxnIdx.step]
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st')) :=
  Network.oneRxnNetwork_scheduleFootprintWithin (by
    simpa [controlSwapNetwork] using
      controlSwapReaction_footprintWithin (Q := Q) st st')

theorem transferTapeToTapeBarUnitNetwork_scheduleFootprintWithin_replicate
    (st : MicroState Q) (k : Nat) :
    (transferTapeToTapeBarUnitNetwork st st).ScheduleFootprintWithin
      (List.replicate k Network.OneRxnIdx.step)
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st)) := by
  intro i hi
  have hiStep : i = Network.OneRxnIdx.step :=
    List.eq_of_mem_replicate hi
  cases hiStep
  simpa [transferTapeToTapeBarUnitNetwork] using
    transferTapeToTapeBarReaction_footprintWithin (Q := Q) st st 1

theorem transferTapeBarToTapeUnitNetwork_scheduleFootprintWithin_replicate
    (st : MicroState Q) (k : Nat) :
    (transferTapeBarToTapeUnitNetwork st st).ScheduleFootprintWithin
      (List.replicate k Network.OneRxnIdx.step)
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st)) := by
  intro i hi
  have hiStep : i = Network.OneRxnIdx.step :=
    List.eq_of_mem_replicate hi
  cases hiStep
  simpa [transferTapeBarToTapeUnitNetwork] using
    transferTapeBarToTapeReaction_footprintWithin (Q := Q) st st 1

theorem tapeTransferUnitNetwork_scheduleFootprintWithin_toTapeBar_replicate
    (st : MicroState Q) (k : Nat) :
    (tapeTransferUnitNetwork st).ScheduleFootprintWithin
      ((List.replicate k Network.OneRxnIdx.step).map Sum.inl)
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st)) := by
  exact Network.parallel_scheduleFootprintWithin_inl
    (N := transferTapeToTapeBarUnitNetwork st st)
    (M := transferTapeBarToTapeUnitNetwork st st)
    (transferTapeToTapeBarUnitNetwork_scheduleFootprintWithin_replicate
      (Q := Q) st k)

theorem tapeTransferUnitNetwork_scheduleFootprintWithin_toTape_replicate
    (st : MicroState Q) (k : Nat) :
    (tapeTransferUnitNetwork st).ScheduleFootprintWithin
      ((List.replicate k Network.OneRxnIdx.step).map Sum.inr)
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st)) := by
  exact Network.parallel_scheduleFootprintWithin_inr
    (N := transferTapeToTapeBarUnitNetwork st st)
    (M := transferTapeBarToTapeUnitNetwork st st)
    (transferTapeBarToTapeUnitNetwork_scheduleFootprintWithin_replicate
      (Q := Q) st k)

theorem tapeTransferWithControlNetwork_scheduleFootprintWithin_toTapeBar
    (st st' : MicroState Q) (k : Nat) :
    (tapeTransferWithControlNetwork st st').ScheduleFootprintWithin
      (tapeTransferWithControlToTapeBarSchedule st st' k)
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st')) := by
  change
    (tapeTransferWithControlNetwork st st').ScheduleFootprintWithin
      (((List.replicate k Network.OneRxnIdx.step).map Sum.inl).map
        Sum.inl ++ [Network.OneRxnIdx.step].map Sum.inr)
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st'))
  exact Network.scheduleFootprintWithin_append
    (Network.parallel_scheduleFootprintWithin_inl
      (N := tapeTransferUnitNetwork st)
      (M := controlSwapNetwork st st')
      (Network.scheduleFootprintWithin_mono
        (tapeTransferUnitNetwork_scheduleFootprintWithin_toTapeBar_replicate
          (Q := Q) st k)
        (fun species hLocal =>
          FourPhaseSpecies.localMacroFootprint_mono
            (oldCtrl := FourPhaseSpecies.ctrlOf st)
            (newCtrl := FourPhaseSpecies.ctrlOf st)
            (P := FourPhaseSpecies.IsLocalMacroFootprint
              (FourPhaseSpecies.ctrlOf st)
              (FourPhaseSpecies.ctrlOf st'))
            (FourPhaseSpecies.localMacroFootprint_oldCtrl
              (FourPhaseSpecies.ctrlOf st)
              (FourPhaseSpecies.ctrlOf st'))
            (FourPhaseSpecies.localMacroFootprint_oldCtrl
              (FourPhaseSpecies.ctrlOf st)
              (FourPhaseSpecies.ctrlOf st'))
            (FourPhaseSpecies.localMacroFootprint_tape
              (FourPhaseSpecies.ctrlOf st)
              (FourPhaseSpecies.ctrlOf st'))
            (FourPhaseSpecies.localMacroFootprint_tapeBar
              (FourPhaseSpecies.ctrlOf st)
              (FourPhaseSpecies.ctrlOf st'))
            hLocal)))
    (Network.parallel_scheduleFootprintWithin_inr
      (N := tapeTransferUnitNetwork st)
      (M := controlSwapNetwork st st')
      (controlSwapNetwork_scheduleFootprintWithin (Q := Q) st st'))

theorem tapeTransferWithControlNetwork_scheduleFootprintWithin_toTape
    (st st' : MicroState Q) (k : Nat) :
    (tapeTransferWithControlNetwork st st').ScheduleFootprintWithin
      (tapeTransferWithControlToTapeSchedule st st' k)
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st')) := by
  change
    (tapeTransferWithControlNetwork st st').ScheduleFootprintWithin
      (((List.replicate k Network.OneRxnIdx.step).map Sum.inr).map
        Sum.inl ++ [Network.OneRxnIdx.step].map Sum.inr)
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st'))
  exact Network.scheduleFootprintWithin_append
    (Network.parallel_scheduleFootprintWithin_inl
      (N := tapeTransferUnitNetwork st)
      (M := controlSwapNetwork st st')
      (Network.scheduleFootprintWithin_mono
        (tapeTransferUnitNetwork_scheduleFootprintWithin_toTape_replicate
          (Q := Q) st k)
        (fun species hLocal =>
          FourPhaseSpecies.localMacroFootprint_mono
            (oldCtrl := FourPhaseSpecies.ctrlOf st)
            (newCtrl := FourPhaseSpecies.ctrlOf st)
            (P := FourPhaseSpecies.IsLocalMacroFootprint
              (FourPhaseSpecies.ctrlOf st)
              (FourPhaseSpecies.ctrlOf st'))
            (FourPhaseSpecies.localMacroFootprint_oldCtrl
              (FourPhaseSpecies.ctrlOf st)
              (FourPhaseSpecies.ctrlOf st'))
            (FourPhaseSpecies.localMacroFootprint_oldCtrl
              (FourPhaseSpecies.ctrlOf st)
              (FourPhaseSpecies.ctrlOf st'))
            (FourPhaseSpecies.localMacroFootprint_tape
              (FourPhaseSpecies.ctrlOf st)
              (FourPhaseSpecies.ctrlOf st'))
            (FourPhaseSpecies.localMacroFootprint_tapeBar
              (FourPhaseSpecies.ctrlOf st)
              (FourPhaseSpecies.ctrlOf st'))
            hLocal)))
    (Network.parallel_scheduleFootprintWithin_inr
      (N := tapeTransferUnitNetwork st)
      (M := controlSwapNetwork st st')
      (controlSwapNetwork_scheduleFootprintWithin (Q := Q) st st'))

theorem aggregateNetwork_execFootprintWithin
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m') :
    (aggregateNetwork st st'
      tapeIn tapeBarIn tapeOut tapeBarOut).ExecFootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st'))
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m' } : MicroCfg Q s)) :=
  Network.oneRxnNetwork_execFootprintWithin
    (aggregateReaction_firesTo
      (s := s) st st' m m'
      tapeIn tapeBarIn tapeOut tapeBarOut
      hTape hTapeBar hTapeEq hTapeBarEq)
    (aggregateReaction_footprintWithin
      (Q := Q) st st'
      tapeIn tapeBarIn tapeOut tapeBarOut)

theorem aggregateNetwork_coord_eq_of_not_localMacroFootprint
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m')
    {species : Species Q}
    (hnot :
      Not
        (FourPhaseSpecies.IsLocalMacroFootprint
          (FourPhaseSpecies.ctrlOf st)
          (FourPhaseSpecies.ctrlOf st')
          species)) :
    enc ({ state := st', tape := m' } : MicroCfg Q s) species =
      enc ({ state := st, tape := m } : MicroCfg Q s) species :=
  Network.ExecFootprintWithin.coord_eq
    (aggregateNetwork_execFootprintWithin
      (s := s) st st' m m'
      tapeIn tapeBarIn tapeOut tapeBarOut
      hTape hTapeBar hTapeEq hTapeBarEq)
    hnot

theorem aggregateNetwork_eqOn_of_disjoint_localMacroFootprint
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m')
    {Protected : Species Q -> Prop}
    (hDisjoint :
      forall species,
        FourPhaseSpecies.IsLocalMacroFootprint
          (FourPhaseSpecies.ctrlOf st)
          (FourPhaseSpecies.ctrlOf st')
          species ->
        Protected species ->
        False) :
    State.EqOn Protected
      (enc ({ state := st', tape := m' } : MicroCfg Q s))
      (enc ({ state := st, tape := m } : MicroCfg Q s)) :=
  Network.ExecFootprintWithin.eqOn_of_disjoint
    (aggregateNetwork_execFootprintWithin
      (s := s) st st' m m'
      tapeIn tapeBarIn tapeOut tapeBarOut
      hTape hTapeBar hTapeEq hTapeBarEq)
    hDisjoint

theorem preserveTapeUnitNetwork_execFootprintWithin
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= m) :
    (preserveTapeUnitNetwork st st').ExecFootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st'))
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m } : MicroCfg Q s)) :=
  Network.oneRxnNetwork_execFootprintWithin
    (preserveTapeReaction_firesTo (s := s) st st' m 1 hm)
    (preserveTapeReaction_footprintWithin (Q := Q) st st' 1)

theorem preserveTapeBarUnitNetwork_execFootprintWithin
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= maxTape s - m) :
    (preserveTapeBarUnitNetwork st st').ExecFootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st'))
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m } : MicroCfg Q s)) :=
  Network.oneRxnNetwork_execFootprintWithin
    (preserveTapeBarReaction_firesTo (s := s) st st' m 1 hm)
    (preserveTapeBarReaction_footprintWithin (Q := Q) st st' 1)

theorem transferTapeToTapeBarUnitNetwork_execFootprintWithin
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : m <= maxTape s)
    (hpos : 1 <= m) :
    (transferTapeToTapeBarUnitNetwork st st').ExecFootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st'))
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m - 1 } : MicroCfg Q s)) :=
  Network.oneRxnNetwork_execFootprintWithin
    (transferTapeToTapeBarReaction_firesTo
      (s := s) st st' m 1 hm hpos)
    (transferTapeToTapeBarReaction_footprintWithin (Q := Q) st st' 1)

theorem transferTapeBarToTapeUnitNetwork_execFootprintWithin
    {s : Nat}
    (st st' : MicroState Q) (m : Nat)
    (hm : 1 <= maxTape s - m) :
    (transferTapeBarToTapeUnitNetwork st st').ExecFootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st'))
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m + 1 } : MicroCfg Q s)) :=
  Network.oneRxnNetwork_execFootprintWithin
    (transferTapeBarToTapeReaction_firesTo (s := s) st st' m 1 hm)
    (transferTapeBarToTapeReaction_footprintWithin (Q := Q) st st' 1)

theorem transferTapeToTapeBarUnitNetwork_execFootprintWithin_replicate
    {s : Nat}
    (st : MicroState Q) (m k : Nat)
    (hm : m <= maxTape s)
    (hk : k <= m) :
    (transferTapeToTapeBarUnitNetwork st st).ExecFootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st))
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st, tape := m - k } : MicroCfg Q s)) :=
  Network.ExecFootprintWithin.of_exec_scheduleFootprintWithin
    (transferTapeToTapeBarUnitNetwork_exec_replicate
      (s := s) st m k hm hk)
    (transferTapeToTapeBarUnitNetwork_scheduleFootprintWithin_replicate
      st k)

theorem transferTapeBarToTapeUnitNetwork_execFootprintWithin_replicate
    {s : Nat}
    (st : MicroState Q) (m k : Nat)
    (hk : k <= maxTape s - m) :
    (transferTapeBarToTapeUnitNetwork st st).ExecFootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st))
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st, tape := m + k } : MicroCfg Q s)) :=
  Network.ExecFootprintWithin.of_exec_scheduleFootprintWithin
    (transferTapeBarToTapeUnitNetwork_exec_replicate
      (s := s) st m k hk)
    (transferTapeBarToTapeUnitNetwork_scheduleFootprintWithin_replicate
      st k)

theorem tapeTransferUnitNetwork_execFootprintWithin_toTapeBar_replicate
    {s : Nat}
    (st : MicroState Q) (m k : Nat)
    (hm : m <= maxTape s)
    (hk : k <= m) :
    (tapeTransferUnitNetwork st).ExecFootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st))
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st, tape := m - k } : MicroCfg Q s)) :=
  Network.ExecFootprintWithin.of_exec_scheduleFootprintWithin
    (tapeTransferUnitNetwork_exec_toTapeBar_replicate
      (s := s) st m k hm hk)
    (tapeTransferUnitNetwork_scheduleFootprintWithin_toTapeBar_replicate
      st k)

theorem tapeTransferUnitNetwork_execFootprintWithin_toTape_replicate
    {s : Nat}
    (st : MicroState Q) (m k : Nat)
    (hk : k <= maxTape s - m) :
    (tapeTransferUnitNetwork st).ExecFootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st))
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st, tape := m + k } : MicroCfg Q s)) :=
  Network.ExecFootprintWithin.of_exec_scheduleFootprintWithin
    (tapeTransferUnitNetwork_exec_toTape_replicate
      (s := s) st m k hk)
    (tapeTransferUnitNetwork_scheduleFootprintWithin_toTape_replicate
      st k)

theorem tapeTransferWithControlNetwork_execFootprintWithin_toTapeBar
    {s : Nat}
    (st st' : MicroState Q) (m k : Nat)
    (hm : m <= maxTape s)
    (hk : k <= m) :
    (tapeTransferWithControlNetwork st st').ExecFootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st'))
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m - k } : MicroCfg Q s)) :=
  Network.ExecFootprintWithin.of_exec_scheduleFootprintWithin
    (tapeTransferWithControlNetwork_exec_toTapeBar
      (s := s) st st' m k hm hk)
    (tapeTransferWithControlNetwork_scheduleFootprintWithin_toTapeBar
      st st' k)

theorem tapeTransferWithControlNetwork_execFootprintWithin_toTape
    {s : Nat}
    (st st' : MicroState Q) (m k : Nat)
    (hk : k <= maxTape s - m) :
    (tapeTransferWithControlNetwork st st').ExecFootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st'))
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m + k } : MicroCfg Q s)) :=
  Network.ExecFootprintWithin.of_exec_scheduleFootprintWithin
    (tapeTransferWithControlNetwork_exec_toTape
      (s := s) st st' m k hk)
    (tapeTransferWithControlNetwork_scheduleFootprintWithin_toTape
      st st' k)

theorem controlSwapNetwork_execFootprintWithin
    {s : Nat}
    (st st' : MicroState Q) (m : Nat) :
    (controlSwapNetwork st st').ExecFootprintWithin
      (FourPhaseSpecies.IsLocalMacroFootprint
        (FourPhaseSpecies.ctrlOf st)
        (FourPhaseSpecies.ctrlOf st'))
      (enc ({ state := st, tape := m } : MicroCfg Q s))
      (enc ({ state := st', tape := m } : MicroCfg Q s)) :=
  Network.ExecFootprintWithin.of_exec_scheduleFootprintWithin
    (controlSwapNetwork_exec (s := s) st st' m)
    (controlSwapNetwork_scheduleFootprintWithin st st')

end FourPhaseEncoding

end CTM

end Ripple.sCRNUniversality
