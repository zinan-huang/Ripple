/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.ByzantinePhase2Rung

/-!
# Byzantine Phase-II dyadic ladder interface

This module composes Phase-II dyadic aggregate-minority checkpoints.  The
individual rungs are intentionally supplied as hypotheses: the previous file
contains the Bellman transfer layer, while the still-missing scalar work is the
state-dependent relaxed-rate proof that each displayed rung estimate holds.
-/

namespace Tri.Byzantine

open scoped ENNReal

variable {n B z : ℕ}

/-- Dyadic Phase-II denominator `K_j = 2^j * 4`. -/
def phase2DyadicK (j : ℕ) : ℕ :=
  2 ^ j * 4

/-- Phase-II dyadic checkpoint `K_j(y+z) ≤ n`. -/
def Phase2DyadicCheckpoint
    (j : ℕ) (q : Phase2Level n B z) : Prop :=
  Phase2AggregateCap (n := n) (B := B) (z := z) (phase2DyadicK j) q

instance phase2DyadicCheckpointDecidable (j : ℕ) :
    DecidablePred (Phase2DyadicCheckpoint (n := n) (B := B) (z := z) j) := by
  intro q
  unfold Phase2DyadicCheckpoint
  infer_instance

/-- Terminal Phase-II ladder target: either the strong entry `y ≤ z`, or the
declared logarithmic endpoint cap. -/
def Phase2LadderTarget
    (J : ℕ) (q : Phase2Level n B z) : Prop :=
  Phase2StrongTarget q ∨ Phase2DyadicCheckpoint (n := n) (B := B) (z := z) J q

instance phase2LadderTargetDecidable (J : ℕ) :
    DecidablePred (Phase2LadderTarget (n := n) (B := B) (z := z) J) := by
  intro q
  unfold Phase2LadderTarget
  infer_instance

/-- Rung horizon at dyadic denominator `K_j`. -/
def phase2DyadicRungHorizon (C₂ n j : ℕ) : ℕ :=
  phase2RungProductiveHorizon C₂ n (phase2DyadicK j)

/-- Exact productive-event horizon of a finite dyadic Phase-II ladder. -/
def phase2DyadicLadderHorizon (C₂ n J : ℕ) : ℕ :=
  ∑ j ∈ Finset.range J, phase2DyadicRungHorizon C₂ n j

/-- Exact finite error sum of a finite dyadic Phase-II ladder. -/
noncomputable def phase2DyadicLadderError
    (A₂ a₂ : ℝ) (γ n J : ℕ) : ℝ≥0∞ :=
  ∑ _ ∈ Finset.range J, phase2RungEnvelope A₂ a₂ γ n

/-- Closed form for the constant per-rung error sum. -/
theorem phase2DyadicLadderError_eq
    (A₂ a₂ : ℝ) (γ n J : ℕ) :
    phase2DyadicLadderError A₂ a₂ γ n J =
      (J : ℝ≥0∞) * phase2RungEnvelope A₂ a₂ γ n := by
  simp [phase2DyadicLadderError, nsmul_eq_mul]

/-- The initial Phase-I handoff `ŷ ≤ n/4` is the zero-th Phase-II checkpoint. -/
theorem phase2DyadicCheckpoint_zero
    (q : Phase2Level n B z)
    (h : 4 * (State.y q.1 + State.z q.1) ≤ n) :
    Phase2DyadicCheckpoint (n := n) (B := B) (z := z) 0 q := by
  simpa [Phase2DyadicCheckpoint, phase2DyadicK,
    Phase2AggregateCap] using h

/-- The `j+1` dyadic checkpoint is exactly the cap used as the postcondition
of the `j`-th rung. -/
theorem phase2DyadicCheckpoint_succ_eq
    (j : ℕ) :
    Phase2DyadicCheckpoint (n := n) (B := B) (z := z) (j + 1) =
      Phase2AggregateCap (n := n) (B := B) (z := z)
        (2 * phase2DyadicK j) := by
  funext q
  unfold Phase2DyadicCheckpoint phase2DyadicK
  rw [pow_succ]
  ring_nf

/-- Dyadic Phase-II reference rungs compose with the displayed summed error. -/
theorem phase2_reference_ladder_chain
    (h3 : 3 ≤ n) (C₂ γ J : ℕ) (A₂ a₂ : ℝ)
    (hrungs :
      ∀ j < J,
        Reaches
          (phase2ReferenceStep (n := n) (B := B) (z := z) h3)
          (phase2DyadicRungHorizon C₂ n j)
          (Phase2DyadicCheckpoint (n := n) (B := B) (z := z) j)
          (Phase2DyadicCheckpoint (n := n) (B := B) (z := z) (j + 1))
          (phase2RungEnvelope A₂ a₂ γ n)) :
    Reaches
      (phase2ReferenceStep (n := n) (B := B) (z := z) h3)
      (phase2DyadicLadderHorizon C₂ n J)
      (Phase2DyadicCheckpoint (n := n) (B := B) (z := z) 0)
      (Phase2DyadicCheckpoint (n := n) (B := B) (z := z) J)
      (phase2DyadicLadderError A₂ a₂ γ n J) := by
  let P : ℕ → Phase2Level n B z → Prop :=
    fun j => Phase2DyadicCheckpoint (n := n) (B := B) (z := z) j
  let T : ℕ → ℕ := fun j => phase2DyadicRungHorizon C₂ n j
  let ε : ℕ → ℝ≥0∞ := fun _ => phase2RungEnvelope A₂ a₂ γ n
  have hchain :=
    Reaches.chain
      (K := phase2ReferenceStep (n := n) (B := B) (z := z) h3)
      (P := P) (T := T) (ε := ε) (k := J)
      (by
        intro j hj
        exact hrungs j hj)
  simpa [P, T, ε, phase2DyadicLadderHorizon,
    phase2DyadicLadderError] using hchain

/-- The same ladder, with the final postcondition enlarged to the Phase-II
entry-or-endpoint target. -/
theorem phase2_reference_ladder_to_entry_or_endpoint
    (h3 : 3 ≤ n) (C₂ γ J : ℕ) (A₂ a₂ : ℝ)
    (hrungs :
      ∀ j < J,
        Reaches
          (phase2ReferenceStep (n := n) (B := B) (z := z) h3)
          (phase2DyadicRungHorizon C₂ n j)
          (Phase2DyadicCheckpoint (n := n) (B := B) (z := z) j)
          (Phase2DyadicCheckpoint (n := n) (B := B) (z := z) (j + 1))
          (phase2RungEnvelope A₂ a₂ γ n)) :
    Reaches
      (phase2ReferenceStep (n := n) (B := B) (z := z) h3)
      (phase2DyadicLadderHorizon C₂ n J)
      (Phase2DyadicCheckpoint (n := n) (B := B) (z := z) 0)
      (Phase2LadderTarget (n := n) (B := B) (z := z) J)
      (phase2DyadicLadderError A₂ a₂ γ n J) := by
  exact
    (phase2_reference_ladder_chain
      (n := n) (B := B) (z := z) h3 C₂ γ J A₂ a₂ hrungs).mono_post
      (by
        intro q hq
        exact Or.inr hq)

namespace Phase2LadderExample

private def s : State 8 0 := by
  refine ⟨(⟨6, by decide⟩, ⟨0, by decide⟩), ?_⟩
  decide

private def q : Phase2Level 8 0 0 :=
  ⟨s, by rfl⟩

example :
    Phase2DyadicCheckpoint (n := 8) (B := 0) (z := 0) 0 q := by
  apply phase2DyadicCheckpoint_zero
  norm_num [q, s, State.y, State.z, State.x]

example :
    Phase2LadderTarget (n := 8) (B := 0) (z := 0) 0 q := by
  exact Or.inr (by
    apply phase2DyadicCheckpoint_zero
    norm_num [q, s, State.y, State.z, State.x])

end Phase2LadderExample

end Tri.Byzantine

#print axioms Tri.Byzantine.phase2DyadicLadderError_eq
#print axioms Tri.Byzantine.phase2DyadicCheckpoint_zero
#print axioms Tri.Byzantine.phase2DyadicCheckpoint_succ_eq
#print axioms Tri.Byzantine.phase2_reference_ladder_chain
#print axioms Tri.Byzantine.phase2_reference_ladder_to_entry_or_endpoint
