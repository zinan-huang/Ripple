/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.ByzantinePhase2BufferedRung
import Tri.ByzantinePostEntry
import Tri.Theorem4Statement

/-!
# Theorem 4 entry bridge facts

This module records the arithmetic and joint-law bridges used by the
paper-facing `theorem4_entry` capstone.  The unconditional Phase-I/Phase-II
assembly and headline compression are proved in
`Tri.Theorem4EntryUnconditional` and `Tri.Theorem4EntryHeadline`.
-/

namespace Tri.Byzantine

open scoped ENNReal NNReal

variable {n B z : Nat}

/-! ## Arithmetic handoff between phases -/

/-- The Phase-I handoff `x >= 3n/4` is exactly enough to start the zero-th
Phase-II aggregate-minority checkpoint `4(y+z) <= n`. -/
theorem phase1HalfTarget_to_phase2Checkpoint_zero
    (q : Phase2Level n B z)
    (h : Phase1HalfTarget q) :
    Phase2DyadicCheckpoint (n := n) (B := B) (z := z) 0 q := by
  apply phase2DyadicCheckpoint_zero
  unfold Phase1HalfTarget at h
  have htotal := State.total q.1
  omega

/-- The entry monitor's upper checkpoint is the same arithmetic handoff, stated
on physical states rather than fixed-`z` levels. -/
theorem entryTarget_to_phase2Checkpoint_zero
    (q : Phase2Level n B z)
    (h : EntryTarget q.1) :
    Phase2DyadicCheckpoint (n := n) (B := B) (z := z) 0 q := by
  apply phase2DyadicCheckpoint_zero
  unfold EntryTarget at h
  have htotal := State.total q.1
  omega

/-- The Phase-II strong target implies the printed relaxed `X`-consensus target
used by Theorem 4's entry clause. -/
theorem phase2StrongTarget_relaxed
    (q : Phase2Level n B z)
    (h : Phase2StrongTarget q) :
    RelaxedXConsensus q.1 := by
  exact strongXEntry_relaxed q.1 (by
    simpa [Phase2StrongTarget, StrongXEntry] using h)

/-- Equivalently, terminal relaxed-consensus failure can only happen outside
the Phase-II strong target. -/
theorem relaxedFailure_not_phase2Strong
    (q : Phase2Level n B z)
    (hfail : RelaxedXFailure q.1) :
    ¬ Phase2StrongTarget q := by
  intro hstrong
  exact (not_le_of_gt hfail) (phase2StrongTarget_relaxed q hstrong)

/-! ## Joint-history representation of public failure

The public state law is the state marginal of the history-augmented controlled
chain. Freezing the target before taking that marginal gives the exact
reached-by-deadline event needed for the theorem statement.
-/

/-- The corrected theorem-facing frozen law is exactly the state marginal of
the target-frozen joint history/state chain. -/
theorem theorem4ControlledFrozenLaw_eq_joint
    (σ : Strategy n B) (h3 : 3 ≤ n) :
    ∀ T hist s,
      (iter
        (freeze
          (fun q : ControlledJointState n B =>
            RelaxedXConsensus q.2)
          (controlledJointStep σ h3))
        T (hist, s)).map Prod.snd =
      theorem4ControlledFrozenLaw σ T hist s := by
  intro T
  induction T with
  | zero =>
      intro hist s
      change
        (PMF.pure (hist, s)).map Prod.snd =
          PMF.pure s
      unfold PMF.map
      rw [PMF.pure_bind]
      rfl
  | succ T ih =>
      intro hist s
      by_cases hs : RelaxedXConsensus s
      · rw [iter_targetFreeze_of_mem
          (fun q : ControlledJointState n B =>
            RelaxedXConsensus q.2)
          (controlledJointStep σ h3)
          (hist, s) hs (T + 1)]
        rw [theorem4ControlledFrozenLaw, if_pos hs]
        change
          (PMF.pure (hist, s)).map Prod.snd =
            PMF.pure s
        unfold PMF.map
        rw [PMF.pure_bind]
        rfl
      · rw [iter_succ,
          freeze_of_not_mem (hist, s) hs,
          PMF.map_bind]
        simp_rw [ih]
        rw [theorem4ControlledFrozenLaw,
          if_neg hs, dif_pos h3]
        unfold controlledJointStep
        rw [PMF.bind_map]
        rfl

/-- The public Theorem-4 hitting failure is the terminal failure of the
target-frozen joint chain. -/
theorem theorem4EntryHittingFailureMass_eq_joint
    (σ : Strategy n B) (h3 : 3 ≤ n)
    (T : ℕ) (hist : History n B) (s : State n B) :
    theorem4EntryHittingFailureMass σ T hist s =
      terminalFailureMass
        (iter
          (freeze
            (fun q : ControlledJointState n B =>
              RelaxedXConsensus q.2)
            (controlledJointStep σ h3))
          T (hist, s))
        (fun q => RelaxedXConsensus q.2) := by
  calc
    theorem4EntryHittingFailureMass σ T hist s =
        terminalFailureMass
          (theorem4ControlledFrozenLaw σ T hist s)
          RelaxedXConsensus := by
      rfl
    _ = terminalFailureMass
          ((iter
            (freeze
              (fun q : ControlledJointState n B =>
                RelaxedXConsensus q.2)
              (controlledJointStep σ h3))
            T (hist, s)).map Prod.snd)
          RelaxedXConsensus := by
      rw [theorem4ControlledFrozenLaw_eq_joint σ h3 T hist s]
    _ = terminalFailureMass
          (iter
            (freeze
              (fun q : ControlledJointState n B =>
                RelaxedXConsensus q.2)
              (controlledJointStep σ h3))
            T (hist, s))
          (fun q => RelaxedXConsensus q.2) :=
      terminalFailureMass_map _ Prod.snd RelaxedXConsensus

/-! ## Phase-II contribution -/

/-- Complete unconditional Phase-II contribution to the public Theorem-4
entry hitting event. -/
theorem phase2_theorem4EntryHittingFailureMass_le
    (σ : Strategy n B)
    (h3 : 3 ≤ n)
    (S : RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal))
    (d : ℕ)
    (hd : 1 ≤ d)
    (hlarge : 68 * d ≤ 3 * n)
    (hist : History n B) (s : State n B)
    (hcheckpoint :
      4 * (State.y s + State.z s) ≤ n) :
    theorem4EntryHittingFailureMass σ
        (phase2BufferedLadderHorizon S d n
          (phase2BufferedStageCount n))
        hist s ≤
      phase2BufferedLadderError S d n
        (phase2BufferedStageCount n) := by
  rw [theorem4EntryHittingFailureMass_eq_joint
    σ h3]
  exact
    phase2_controlledJoint_buffered_to_relaxed
      (n := n) (B := B)
      σ h3 S d hd hlarge (hist, s) hcheckpoint

/-! ## Executable boundary witnesses

The private examples check the exact boundary implications used at the
phase handoff, including a non-consensus checkpoint and a terminal strong
target. They are compile-time sanity checks, not additional assumptions.
-/

namespace Theorem4EntryBridgeExample

private def s : State 8 0 := by
  refine ⟨(⟨6, by decide⟩, ⟨0, by decide⟩), ?_⟩
  decide

private def q : Phase2Level 8 0 0 :=
  ⟨s, by rfl⟩

private def sStrong : State 8 0 := by
  refine ⟨(⟨8, by decide⟩, ⟨0, by decide⟩), ?_⟩
  decide

private def qStrong : Phase2Level 8 0 0 :=
  ⟨sStrong, by rfl⟩

example :
    Phase2DyadicCheckpoint (n := 8) (B := 0) (z := 0) 0 q :=
  phase1HalfTarget_to_phase2Checkpoint_zero q (by
    norm_num [Phase1HalfTarget, q, s, State.x])

example :
    RelaxedXConsensus qStrong.1 :=
  phase2StrongTarget_relaxed qStrong (by
    norm_num [Phase2StrongTarget, qStrong, sStrong, State.x, State.z])

end Theorem4EntryBridgeExample

end Tri.Byzantine

#print axioms Tri.Byzantine.phase1HalfTarget_to_phase2Checkpoint_zero
#print axioms Tri.Byzantine.entryTarget_to_phase2Checkpoint_zero
#print axioms Tri.Byzantine.phase2StrongTarget_relaxed
#print axioms Tri.Byzantine.relaxedFailure_not_phase2Strong
#print axioms Tri.Byzantine.theorem4ControlledFrozenLaw_eq_joint
#print axioms Tri.Byzantine.theorem4EntryHittingFailureMass_eq_joint
#print axioms Tri.Byzantine.phase2_theorem4EntryHittingFailureMass_le
