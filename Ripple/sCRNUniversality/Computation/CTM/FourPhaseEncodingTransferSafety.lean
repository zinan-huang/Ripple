import Ripple.sCRNUniversality.Computation.CTM.FourPhaseEncodingTransfer

namespace Ripple.sCRNUniversality

namespace CTM

namespace FourPhaseEncoding

universe u

variable {Q : Type u} [DecidableEq Q]

theorem fullAggregateReaction_guardedBy_ctrlOf {s : Nat}
    (c c' : MicroCfg Q s) :
    (fullAggregateReaction c c').GuardedBy
      (FourPhaseSpecies.ctrlOf c.state) := by
  simp [Reaction.GuardedBy, Reaction.Requires, fullAggregateReaction,
    fullAggregateInput]

theorem fullAggregateNetwork_guardedByFamily_ctrlOf {s : Nat}
    (c c' : MicroCfg Q s) :
    (fullAggregateNetwork c c').GuardedByFamily
      (fun _ => FourPhaseSpecies.ctrlOf c.state) :=
  Network.oneRxnNetwork_guardedByFamily_const
    (fullAggregateReaction_guardedBy_ctrlOf c c')

theorem fullAggregateNetwork_scheduleGuardedBy_ctrlOf {s : Nat}
    (c c' : MicroCfg Q s) :
    (fullAggregateNetwork c c').ScheduleGuardedBy
      [Network.OneRxnIdx.step]
      (FourPhaseSpecies.ctrlOf c.state) :=
  Network.oneRxnNetwork_scheduleGuardedBy
    (fullAggregateReaction_guardedBy_ctrlOf c c')

theorem fullAggregateNetwork_intendedSchedule_scheduleGuardedBy_ctrlOf
    {s : Nat} (c c' : MicroCfg Q s) :
    (fullAggregateNetwork c c').ScheduleGuardedBy
      (fullAggregateNetwork_intendedSchedule c c').schedule
      (FourPhaseSpecies.ctrlOf c.state) :=
  Network.scheduleGuardedBy_of_guardedByFamily_const
    (fullAggregateNetwork_guardedByFamily_ctrlOf c c')

theorem fullAggregateNetwork_boundedIntendedSchedule_scheduleGuardedBy_ctrlOf
    {s : Nat} (c c' : MicroCfg Q s) :
    (fullAggregateNetwork c c').ScheduleGuardedBy
      (fullAggregateNetwork_boundedIntendedSchedule c c').schedule
      (FourPhaseSpecies.ctrlOf c.state) :=
  Network.scheduleGuardedBy_of_guardedByFamily_const
    (fullAggregateNetwork_guardedByFamily_ctrlOf c c')

theorem aggregateReaction_guardedBy_ctrlOf
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat) :
    (aggregateReaction st st'
      tapeIn tapeBarIn tapeOut tapeBarOut).GuardedBy
      (FourPhaseSpecies.ctrlOf st) := by
  simp [Reaction.GuardedBy, Reaction.Requires, aggregateReaction,
    aggregateInput]

theorem aggregateNetwork_guardedByFamily_ctrlOf
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat) :
    (aggregateNetwork st st'
      tapeIn tapeBarIn tapeOut tapeBarOut).GuardedByFamily
      (fun _ => FourPhaseSpecies.ctrlOf st) :=
  Network.oneRxnNetwork_guardedByFamily_const
    (aggregateReaction_guardedBy_ctrlOf
      (Q := Q) st st' tapeIn tapeBarIn tapeOut tapeBarOut)

theorem aggregateNetwork_scheduleGuardedBy_ctrlOf
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat) :
    (aggregateNetwork st st'
      tapeIn tapeBarIn tapeOut tapeBarOut).ScheduleGuardedBy
      [Network.OneRxnIdx.step]
      (FourPhaseSpecies.ctrlOf st) :=
  Network.oneRxnNetwork_scheduleGuardedBy
    (aggregateReaction_guardedBy_ctrlOf
      (Q := Q) st st' tapeIn tapeBarIn tapeOut tapeBarOut)

theorem aggregateNetwork_intendedSchedule_scheduleGuardedBy_ctrlOf
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m') :
    (aggregateNetwork st st'
      tapeIn tapeBarIn tapeOut tapeBarOut).ScheduleGuardedBy
      (aggregateNetwork_intendedSchedule
        (s := s) st st' m m'
        tapeIn tapeBarIn tapeOut tapeBarOut
        hTape hTapeBar hTapeEq hTapeBarEq).schedule
      (FourPhaseSpecies.ctrlOf st) :=
  Network.scheduleGuardedBy_of_guardedByFamily_const
    (aggregateNetwork_guardedByFamily_ctrlOf
      (Q := Q) st st' tapeIn tapeBarIn tapeOut tapeBarOut)

theorem aggregateNetwork_boundedIntendedSchedule_scheduleGuardedBy_ctrlOf
    {s : Nat}
    (st st' : MicroState Q)
    (m m' tapeIn tapeBarIn tapeOut tapeBarOut : Nat)
    (hTape : tapeIn <= m)
    (hTapeBar : tapeBarIn <= maxTape s - m)
    (hTapeEq : m - tapeIn + tapeOut = m')
    (hTapeBarEq :
      (maxTape s - m) - tapeBarIn + tapeBarOut = maxTape s - m') :
    (aggregateNetwork st st'
      tapeIn tapeBarIn tapeOut tapeBarOut).ScheduleGuardedBy
      (aggregateNetwork_boundedIntendedSchedule
        (s := s) st st' m m'
        tapeIn tapeBarIn tapeOut tapeBarOut
        hTape hTapeBar hTapeEq hTapeBarEq).schedule
      (FourPhaseSpecies.ctrlOf st) :=
  Network.scheduleGuardedBy_of_guardedByFamily_const
    (aggregateNetwork_guardedByFamily_ctrlOf
      (Q := Q) st st' tapeIn tapeBarIn tapeOut tapeBarOut)

theorem preserveTapeReaction_guardedBy_ctrlOf
    (st st' : MicroState Q) (k : Nat) :
    (preserveTapeReaction st st' k).GuardedBy
      (FourPhaseSpecies.ctrlOf st) := by
  simpa [preserveTapeReaction] using
    aggregateReaction_guardedBy_ctrlOf
      (Q := Q) st st' k 0 k 0

theorem preserveTapeBarReaction_guardedBy_ctrlOf
    (st st' : MicroState Q) (k : Nat) :
    (preserveTapeBarReaction st st' k).GuardedBy
      (FourPhaseSpecies.ctrlOf st) := by
  simpa [preserveTapeBarReaction] using
    aggregateReaction_guardedBy_ctrlOf
      (Q := Q) st st' 0 k 0 k

theorem transferTapeToTapeBarReaction_guardedBy_ctrlOf
    (st st' : MicroState Q) (k : Nat) :
    (transferTapeToTapeBarReaction st st' k).GuardedBy
      (FourPhaseSpecies.ctrlOf st) := by
  simpa [transferTapeToTapeBarReaction] using
    aggregateReaction_guardedBy_ctrlOf
      (Q := Q) st st' k 0 0 k

theorem transferTapeBarToTapeReaction_guardedBy_ctrlOf
    (st st' : MicroState Q) (k : Nat) :
    (transferTapeBarToTapeReaction st st' k).GuardedBy
      (FourPhaseSpecies.ctrlOf st) := by
  simpa [transferTapeBarToTapeReaction] using
    aggregateReaction_guardedBy_ctrlOf
      (Q := Q) st st' 0 k k 0

theorem controlSwapReaction_guardedBy_ctrlOf
    (st st' : MicroState Q) :
    (controlSwapReaction st st').GuardedBy
      (FourPhaseSpecies.ctrlOf st) := by
  simpa [controlSwapReaction] using
    aggregateReaction_guardedBy_ctrlOf
      (Q := Q) st st' 0 0 0 0

theorem preserveTapeUnitNetwork_guardedByFamily_ctrlOf
    (st st' : MicroState Q) :
    (preserveTapeUnitNetwork st st').GuardedByFamily
      (fun _ => FourPhaseSpecies.ctrlOf st) :=
  Network.oneRxnNetwork_guardedByFamily_const
    (preserveTapeReaction_guardedBy_ctrlOf (Q := Q) st st' 1)

theorem preserveTapeBarUnitNetwork_guardedByFamily_ctrlOf
    (st st' : MicroState Q) :
    (preserveTapeBarUnitNetwork st st').GuardedByFamily
      (fun _ => FourPhaseSpecies.ctrlOf st) :=
  Network.oneRxnNetwork_guardedByFamily_const
    (preserveTapeBarReaction_guardedBy_ctrlOf (Q := Q) st st' 1)

theorem transferTapeToTapeBarUnitNetwork_guardedByFamily_ctrlOf
    (st st' : MicroState Q) :
    (transferTapeToTapeBarUnitNetwork st st').GuardedByFamily
      (fun _ => FourPhaseSpecies.ctrlOf st) :=
  Network.oneRxnNetwork_guardedByFamily_const
    (transferTapeToTapeBarReaction_guardedBy_ctrlOf (Q := Q) st st' 1)

theorem transferTapeBarToTapeUnitNetwork_guardedByFamily_ctrlOf
    (st st' : MicroState Q) :
    (transferTapeBarToTapeUnitNetwork st st').GuardedByFamily
      (fun _ => FourPhaseSpecies.ctrlOf st) :=
  Network.oneRxnNetwork_guardedByFamily_const
    (transferTapeBarToTapeReaction_guardedBy_ctrlOf (Q := Q) st st' 1)

theorem transferTapeToTapeBarUnitNetwork_scheduleGuardedBy_replicate
    (st : MicroState Q) (k : Nat) :
    (transferTapeToTapeBarUnitNetwork st st).ScheduleGuardedBy
      (List.replicate k Network.OneRxnIdx.step)
      (FourPhaseSpecies.ctrlOf st) :=
  Network.oneRxnNetwork_scheduleGuardedBy_replicate
    (transferTapeToTapeBarReaction_guardedBy_ctrlOf (Q := Q) st st 1)

theorem transferTapeBarToTapeUnitNetwork_scheduleGuardedBy_replicate
    (st : MicroState Q) (k : Nat) :
    (transferTapeBarToTapeUnitNetwork st st).ScheduleGuardedBy
      (List.replicate k Network.OneRxnIdx.step)
      (FourPhaseSpecies.ctrlOf st) :=
  Network.oneRxnNetwork_scheduleGuardedBy_replicate
    (transferTapeBarToTapeReaction_guardedBy_ctrlOf (Q := Q) st st 1)

theorem controlSwapNetwork_guardedByFamily_ctrlOf
    (st st' : MicroState Q) :
    (controlSwapNetwork st st').GuardedByFamily
      (fun _ => FourPhaseSpecies.ctrlOf st) :=
  Network.oneRxnNetwork_guardedByFamily_const
    (controlSwapReaction_guardedBy_ctrlOf (Q := Q) st st')

theorem tapeTransferUnitNetwork_guardedByFamily_ctrlOf
    (st : MicroState Q) :
    (tapeTransferUnitNetwork st).GuardedByFamily
      (fun _ => FourPhaseSpecies.ctrlOf st) :=
  Network.parallel_guardedByFamily_const
    (transferTapeToTapeBarUnitNetwork_guardedByFamily_ctrlOf
      (Q := Q) st st)
    (transferTapeBarToTapeUnitNetwork_guardedByFamily_ctrlOf
      (Q := Q) st st)

theorem tapeTransferUnitNetwork_scheduleGuardedBy_toTapeBar_replicate
    (st : MicroState Q) (k : Nat) :
    (tapeTransferUnitNetwork st).ScheduleGuardedBy
      ((List.replicate k Network.OneRxnIdx.step).map Sum.inl)
      (FourPhaseSpecies.ctrlOf st) :=
  Network.parallel_scheduleGuardedBy_inl
    (N := transferTapeToTapeBarUnitNetwork st st)
    (M := transferTapeBarToTapeUnitNetwork st st)
    (transferTapeToTapeBarUnitNetwork_scheduleGuardedBy_replicate
      (Q := Q) st k)

theorem tapeTransferUnitNetwork_scheduleGuardedBy_toTape_replicate
    (st : MicroState Q) (k : Nat) :
    (tapeTransferUnitNetwork st).ScheduleGuardedBy
      ((List.replicate k Network.OneRxnIdx.step).map Sum.inr)
      (FourPhaseSpecies.ctrlOf st) :=
  Network.parallel_scheduleGuardedBy_inr
    (N := transferTapeToTapeBarUnitNetwork st st)
    (M := transferTapeBarToTapeUnitNetwork st st)
    (transferTapeBarToTapeUnitNetwork_scheduleGuardedBy_replicate
      (Q := Q) st k)

theorem tapeTransferWithControlNetwork_guardedByFamily_ctrlOf
    (st st' : MicroState Q) :
    (tapeTransferWithControlNetwork st st').GuardedByFamily
      (fun _ => FourPhaseSpecies.ctrlOf st) :=
  Network.parallel_guardedByFamily_const
    (tapeTransferUnitNetwork_guardedByFamily_ctrlOf (Q := Q) st)
    (controlSwapNetwork_guardedByFamily_ctrlOf (Q := Q) st st')

theorem tapeTransferWithControlNetwork_scheduleGuardedBy_toTapeBar
    (st st' : MicroState Q) (k : Nat) :
    (tapeTransferWithControlNetwork st st').ScheduleGuardedBy
      (tapeTransferWithControlToTapeBarSchedule st st' k)
      (FourPhaseSpecies.ctrlOf st) :=
  Network.scheduleGuardedBy_of_guardedByFamily_const
    (tapeTransferWithControlNetwork_guardedByFamily_ctrlOf
      (Q := Q) st st')

theorem tapeTransferWithControlNetwork_scheduleGuardedBy_toTape
    (st st' : MicroState Q) (k : Nat) :
    (tapeTransferWithControlNetwork st st').ScheduleGuardedBy
      (tapeTransferWithControlToTapeSchedule st st' k)
      (FourPhaseSpecies.ctrlOf st) :=
  Network.scheduleGuardedBy_of_guardedByFamily_const
    (tapeTransferWithControlNetwork_guardedByFamily_ctrlOf
      (Q := Q) st st')

end FourPhaseEncoding

end CTM

end Ripple.sCRNUniversality
