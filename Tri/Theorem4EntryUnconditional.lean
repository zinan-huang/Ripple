/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.ByzantinePhase1Unconditional
import Tri.Theorem4Entry
import Tri.HitThenReaches

/-!
# Unconditional assembly of the Theorem 4 entry phase

The Phase-I and Phase-II estimates are composed on the same physical
history/state chain.  The intermediate target includes the final relaxed
consensus set: a trajectory which reaches the final target during Phase I
must not be forced to leave it merely to satisfy the Phase-I handoff.
-/

namespace Tri.Byzantine

open scoped ENNReal NNReal

noncomputable section

variable {n B : ℕ}

/-- The intermediate stopped target is either the Phase-I half-population
handoff or the final relaxed-consensus target. -/
def Phase12Handoff (q : ControlledJointState n B) : Prop :=
  4 * (State.y q.2 + State.z q.2) ≤ n ∨
    RelaxedXConsensus q.2

instance phase12HandoffDecidable :
    DecidablePred (Phase12Handoff (n := n) (B := B)) := by
  intro q
  unfold Phase12Handoff
  infer_instance

/-- Freezing at the enlarged intermediate target absorbs the final-target
freeze already present in the physical kernel. -/
theorem freeze_phase12Handoff_final_eq
    (K : ControlledJointState n B → PMF (ControlledJointState n B)) :
    freeze
        (Phase12Handoff (n := n) (B := B))
        (freeze
          (fun q : ControlledJointState n B =>
            RelaxedXConsensus q.2)
          K) =
      freeze (Phase12Handoff (n := n) (B := B)) K := by
  funext q
  unfold freeze Phase12Handoff
  by_cases hp : 4 * (State.y q.2 + State.z q.2) ≤ n
  · simp [hp]
  · by_cases hr : RelaxedXConsensus q.2 <;> simp [hp, hr]

/-- The raw Phase-I horizon is positive at the logarithmic endpoint. -/
theorem phase1RawDyadicLadderHorizon_log_pos
    (h3 : 3 ≤ n) :
    0 < phase1RawDyadicLadderHorizon n (Nat.log 2 n) := by
  unfold phase1RawDyadicLadderHorizon
  have hlog : 0 < Nat.log 2 n := by
    have : 2 ≤ n := by omega
    exact Nat.log_pos (by norm_num) this
  exact Nat.mul_pos hlog (by omega)

/-- The complete buffered Phase-II horizon has at least its zero-th positive
rung whenever its large-population premise holds. -/
theorem phase2BufferedLadderHorizon_pos
    (S : RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal))
    (d : ℕ)
    (hd : 1 ≤ d)
    (hlarge : 68 * d ≤ 3 * n) :
    0 <
      phase2BufferedLadderHorizon S d n
        (phase2BufferedStageCount n) := by
  have hlog :=
    phase2BufferedStageCount_log_lower d n hd hlarge
  have hJ : 0 < phase2BufferedStageCount n := by
    unfold phase2BufferedStageCount
    omega
  have hn : 0 < n := by omega
  have hC : 0 < S.C :=
    lt_of_lt_of_le Nat.zero_lt_one S.hC
  have hR :
      ∀ j, 0 < phase2BufferedRungMultiplier S d n j := by
    intro j
    unfold phase2BufferedRungMultiplier
      relaxedDyadicAdaptiveMultiplier
    exact Nat.mul_pos
      (lt_of_lt_of_le Nat.zero_lt_one S.hR₀)
      (by
        rw [Nat.add_comm]
        exact Nat.succ_pos _)
  have hrung :
      ∀ j, 0 < phase2BufferedRungHorizon S d n j := by
    intro j
    unfold phase2BufferedRungHorizon relaxedDyadicHorizon
    exact Nat.mul_pos
      (Nat.mul_pos (by norm_num) (Nat.mul_pos hC (hR j))) hn
  unfold phase2BufferedLadderHorizon
  obtain ⟨J, hJdef⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hJ)
  rw [hJdef, Finset.sum_range_succ]
  exact Nat.add_pos_right _ (hrung J)

/-- Exact finite Phase-I/Phase-II composition from an active Phase-I dyadic
checkpoint to relaxed consensus. -/
theorem phase12_controlledJoint_from_active
    (σ : Strategy n B)
    (h3 : 3 ≤ n)
    (S : RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal))
    (d g : ℕ)
    (hd : 1 ≤ d)
    (hdhalf : d ≤ n / 2)
    (hbudget : 16 * B ≤ d)
    (hg : 1 ≤ g)
    (hlarge : 68 * g ≤ 3 * n) :
    Reaches
      (freeze
        (fun q : ControlledJointState n B =>
          RelaxedXConsensus q.2)
        (controlledJointStep σ h3))
      (phase1RawDyadicLadderHorizon n (Nat.log 2 n) +
        phase2BufferedLadderHorizon S g n
          (phase2BufferedStageCount n))
      (fun q =>
        n + phase1DyadicScale n d 0 ≤ 2 * State.x q.2 ∧
          State.z q.2 = B)
      (fun q => RelaxedXConsensus q.2)
      (phase1RawDyadicLadderError n d (Nat.log 2 n) +
        phase2BufferedLadderError S g n
          (phase2BufferedStageCount n)) := by
  let Raw : ControlledJointState n B → PMF (ControlledJointState n B) :=
    controlledJointStep σ h3
  let Final : ControlledJointState n B → PMF (ControlledJointState n B) :=
    freeze
      (fun q : ControlledJointState n B =>
        RelaxedXConsensus q.2)
      Raw
  let Half : ControlledJointState n B → Prop :=
    fun q => 4 * (State.y q.2 + State.z q.2) ≤ n
  let Mid : ControlledJointState n B → Prop :=
    Phase12Handoff (n := n) (B := B)
  let Target : ControlledJointState n B → Prop :=
    fun q => RelaxedXConsensus q.2
  let T₁ := phase1RawDyadicLadderHorizon n (Nat.log 2 n)
  let T₂ :=
    phase2BufferedLadderHorizon S g n
      (phase2BufferedStageCount n)
  let ε₁ := phase1RawDyadicLadderError n d (Nat.log 2 n)
  let ε₂ :=
    phase2BufferedLadderError S g n
      (phase2BufferedStageCount n)
  have hphase1 :=
    phase1_controlledJoint_raw_dyadic_ladder_to_half
      (n := n) (B := B) (z := B)
      σ h3 d (Nat.log 2 n) hd hdhalf hbudget
      (phase1DyadicScale_log_final n d hd)
  have hhit :
      ∀ q,
        (n + phase1DyadicScale n d 0 ≤ 2 * State.x q.2 ∧
          State.z q.2 = B) →
        terminalFailureMass
            (iter (freeze Mid Final) T₁ q) Mid ≤ ε₁ := by
    intro q hq
    have hmono :=
      targetFreeze_failure_mono_good
        Half Mid Raw
        (fun r hr => Or.inl hr)
        T₁ q
    have hphase := hphase1 q hq
    dsimp only [Final, Mid, Raw]
    rw [freeze_phase12Handoff_final_eq]
    exact hmono.trans hphase
  have hpost : Reaches Final T₂ Mid Target ε₂ := by
    intro q hq
    rcases hq with hhalf | htarget
    · exact
        phase2_controlledJoint_buffered_to_relaxed
          (n := n) (B := B)
          σ h3 S g hg hlarge q hhalf
    · have hiter :
          iter Final T₂ q = PMF.pure q := by
        exact iter_targetFreeze_of_mem Target Raw q htarget T₂
      rw [hiter]
      change terminalFailureMass (PMF.pure q) Target ≤ ε₂
      rw [terminalFailureMass_pure, if_pos htarget]
      exact bot_le
  have habs :
      ∀ q, Target q → Final q = PMF.pure q := by
    intro q hq
    exact freeze_of_mem q hq
  exact
    Reaches.comp_of_frozen_hit
      Final
      (phase1RawDyadicLadderHorizon_log_pos h3)
      (phase2BufferedLadderHorizon_pos S g hg hlarge)
      hhit hpost habs

/-- Exact finite-horizon entry theorem from the paper's initial arithmetic
data.  If the initial gap is already above the Phase-I endpoint, Phase I is
skipped and the Phase-II estimate is padded by the unused frozen time. -/
theorem theorem4EntryHittingFailureMass_le_finite
    (σ : Strategy n B)
    (h3 : 3 ≤ n)
    (S : RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal))
    (γ g x₀ y₀ d : ℕ)
    (hg : 1 ≤ g)
    (hlarge : 68 * g ≤ 3 * n)
    (hinit : Theorem4PaperInitial n γ x₀ y₀ B d) :
    theorem4EntryHittingFailureMass σ
        (phase1RawDyadicLadderHorizon n (Nat.log 2 n) +
          phase2BufferedLadderHorizon S g n
            (phase2BufferedStageCount n))
        []
        (theorem4InitialState n x₀ y₀ B hinit.1) ≤
      phase1RawDyadicLadderError n d (Nat.log 2 n) +
        phase2BufferedLadderError S g n
          (phase2BufferedStageCount n) := by
  let s₀ := theorem4InitialState n x₀ y₀ B hinit.1
  let Raw : ControlledJointState n B → PMF (ControlledJointState n B) :=
    controlledJointStep σ h3
  let Target : ControlledJointState n B → Prop :=
    fun q => RelaxedXConsensus q.2
  let T₁ := phase1RawDyadicLadderHorizon n (Nat.log 2 n)
  let T₂ :=
    phase2BufferedLadderHorizon S g n
      (phase2BufferedStageCount n)
  let ε₁ := phase1RawDyadicLadderError n d (Nat.log 2 n)
  let ε₂ :=
    phase2BufferedLadderError S g n
      (phase2BufferedStageCount n)
  have hd : 1 ≤ d := by
    have := hinit.2.2.2
    omega
  have hbudget : 16 * B ≤ d := by
    have := hinit.2.2.2
    omega
  rw [theorem4EntryHittingFailureMass_eq_joint σ h3]
  by_cases hdhalf : d ≤ n / 2
  · have hstart :
        n + phase1DyadicScale n d 0 ≤ 2 * State.x s₀ ∧
          State.z s₀ = B := by
      constructor
      · have hscale : phase1DyadicScale n d 0 = d := by
          unfold phase1DyadicScale
          rw [pow_zero, one_mul, min_eq_left]
          omega
        rw [hscale]
        change n + d ≤ 2 * x₀
        exact hinit.2.1.le
      · rfl
    exact
      phase12_controlledJoint_from_active
        (n := n) (B := B)
        σ h3 S d g hd hdhalf hbudget hg hlarge
        ([], s₀) hstart
  · have hhalf :
        4 * (State.y s₀ + State.z s₀) ≤ n := by
      have hmass := hinit.1
      have hgap := hinit.2.1
      dsimp [s₀, theorem4InitialState, State.y, State.x, State.z]
      omega
    have hphase2 :=
      phase2_controlledJoint_buffered_to_relaxed
        (n := n) (B := B)
        σ h3 S g hg hlarge ([], s₀) hhalf
    calc
      terminalFailureMass
            (iter (freeze Target Raw) (T₁ + T₂) ([], s₀))
            Target ≤
          terminalFailureMass
            (iter (freeze Target Raw) T₂ ([], s₀))
            Target := by
        exact
          terminalFailureMass_iter_freeze_antitone_of_subset
            Target Target Raw (fun _ h => h) T₂ (T₁ + T₂) (by omega)
            ([], s₀)
      _ ≤ ε₂ := hphase2
      _ ≤ ε₁ + ε₂ := le_add_left le_rfl

end

end Tri.Byzantine

#print axioms Tri.Byzantine.freeze_phase12Handoff_final_eq
#print axioms Tri.Byzantine.phase2BufferedLadderHorizon_pos
#print axioms Tri.Byzantine.phase12_controlledJoint_from_active
#print axioms Tri.Byzantine.theorem4EntryHittingFailureMass_le_finite
