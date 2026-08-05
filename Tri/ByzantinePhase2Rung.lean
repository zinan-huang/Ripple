/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.ByzantinePhase1Ladder
import Tri.PaperLemma10

/-!
# Byzantine Phase-II rung interface

Phase II keeps the same fixed-Byzantine-count fiber used by Phase I, ordered by
honest `X`.  The public progress coordinate is the aggregate minority
`y + z`: increasing `X` decreases that aggregate because `z` is fixed.

This file records the Bellman transfer layer for Phase II and keeps the
Lemma-10 finite-size side condition explicit at every paper-facing rung
interface.  The productive scalar estimate is supplied by callers as a
reference lower bound; the theorem here is the history-dependent transfer to
arbitrary adaptive Byzantine strategies.
-/

namespace Tri.Byzantine

open scoped ENNReal

variable {n B z : ℕ}

/-- Phase-II uses the same fixed-`z` ordered fiber as Phase I. -/
abbrev Phase2Level (n B z : ℕ) :=
  Phase1Level n B z

/-- Phase-II strong entry, equivalent to `y ≤ z`, stated without subtraction. -/
def Phase2StrongTarget (q : Phase2Level n B z) : Prop :=
  n ≤ State.x q.1 + 2 * State.z q.1

instance phase2StrongTargetDecidable :
    DecidablePred (Phase2StrongTarget (n := n) (B := B) (z := z)) := by
  intro q
  unfold Phase2StrongTarget
  infer_instance

/-- Aggregate-minority cap `y + z ≤ n / K`, written as `K(y+z) ≤ n`. -/
def Phase2AggregateCap (K : ℕ) (q : Phase2Level n B z) : Prop :=
  K * (State.y q.1 + State.z q.1) ≤ n

instance phase2AggregateCapDecidable (K : ℕ) :
    DecidablePred (Phase2AggregateCap (n := n) (B := B) (z := z) K) := by
  intro q
  unfold Phase2AggregateCap
  infer_instance

/-- Lower boundary for the Phase-II Bellman stopped value: falling below the
Phase-I handoff checkpoint `x ≥ 3n/4`. -/
def Phase2EntryFailure (q : Phase2Level n B z) : Prop :=
  4 * State.x q.1 < 3 * n

instance phase2EntryFailureDecidable :
    DecidablePred (Phase2EntryFailure (n := n) (B := B) (z := z)) := by
  intro q
  unfold Phase2EntryFailure
  infer_instance

/-- One dyadic rung succeeds either by reaching `y ≤ z`, or by improving the
aggregate-minority cap to the next dyadic scale. -/
def Phase2RungTarget (K : ℕ) (q : Phase2Level n B z) : Prop :=
  Phase2StrongTarget q ∨ Phase2AggregateCap (2 * K) q

instance phase2RungTargetDecidable (K : ℕ) :
    DecidablePred (Phase2RungTarget (n := n) (B := B) (z := z) K) := by
  intro q
  unfold Phase2RungTarget
  infer_instance

/-- Strong entry is exactly the non-strict target `y ≤ z`. -/
theorem phase2StrongTarget_iff_y_le_z (q : Phase2Level n B z) :
    Phase2StrongTarget q ↔ State.y q.1 ≤ State.z q.1 := by
  unfold Phase2StrongTarget
  have ht := State.total q.1
  omega

/-- The lower failure set is lower for the fixed-fiber order. -/
theorem phase2EntryFailure_lower
    ⦃q r : Phase2Level n B z⦄
    (hqr : q ≤ r) (hr : Phase2EntryFailure r) :
    Phase2EntryFailure q := by
  unfold Phase2EntryFailure at *
  change State.x q.1 ≤ State.x r.1 at hqr
  omega

/-- Strong entry is upper for the fixed-fiber order. -/
theorem phase2StrongTarget_upper
    ⦃q r : Phase2Level n B z⦄
    (hqr : q ≤ r) (hq : Phase2StrongTarget q) :
    Phase2StrongTarget r := by
  unfold Phase2StrongTarget at *
  change State.x q.1 ≤ State.x r.1 at hqr
  have hz : State.z q.1 = State.z r.1 := by
    rw [q.2, r.2]
  omega

/-- Aggregate caps are upper for the fixed-fiber order. -/
theorem phase2AggregateCap_upper
    (K : ℕ) ⦃q r : Phase2Level n B z⦄
    (hqr : q ≤ r) (hq : Phase2AggregateCap K q) :
    Phase2AggregateCap K r := by
  unfold Phase2AggregateCap at *
  change State.x q.1 ≤ State.x r.1 at hqr
  have htotalq := State.total q.1
  have htotalr := State.total r.1
  have hz : State.z q.1 = State.z r.1 := by
    rw [q.2, r.2]
  have hminor : State.y r.1 + State.z r.1 ≤ State.y q.1 + State.z q.1 := by
    omega
  exact (Nat.mul_le_mul_left K hminor).trans hq

/-- A Phase-II rung target is upper for the fixed-fiber order. -/
theorem phase2RungTarget_upper
    (K : ℕ) ⦃q r : Phase2Level n B z⦄
    (hqr : q ≤ r) (hq : Phase2RungTarget K q) :
    Phase2RungTarget K r := by
  rcases hq with hstrong | hcap
  · exact Or.inl (phase2StrongTarget_upper hqr hstrong)
  · exact Or.inr (phase2AggregateCap_upper (2 * K) hqr hcap)

/-- Phase-II reference step: the same paper-worst fixed-`z` fiber kernel used
in Phase I. -/
noncomputable abbrev phase2ReferenceStep
    (h3 : 3 ≤ n) (q : Phase2Level n B z) :
    PMF (Phase2Level n B z) :=
  phase1ReferenceStep (n := n) (B := B) (z := z) h3 q

/-- History-dependent controlled step on the same fixed-`z` fiber. -/
noncomputable abbrev phase2ControlledStep
    (σ : Strategy n B) (h3 : 3 ≤ n)
    (hist : History n B) (q : Phase2Level n B z) :
    PMF (History n B × Phase2Level n B z) :=
  phase1ControlledStep (n := n) (B := B) (z := z) σ h3 hist q

/-- Bellman `hmono` for the Phase-II reference kernel. -/
theorem phase2ReferenceStep_mono
    (h3 : 3 ≤ n) :
    ∀ f : Phase2Level n B z → ℝ≥0∞, Monotone f →
      Monotone fun q => expect (phase2ReferenceStep h3 q) f := by
  exact phase1ReferenceStep_mono (n := n) (B := B) (z := z) h3

/-- Bellman domination hypothesis `hdom` for Phase II. -/
theorem phase2_reference_le_controlled
    (σ : Strategy n B) (h3 : 3 ≤ n) :
    ∀ hist q (f : Phase2Level n B z → ℝ≥0∞), Monotone f →
      expect (phase2ReferenceStep h3 q) f ≤
        expect (phase2ControlledStep σ h3 hist q) (fun r => f r.2) := by
  exact phase1_reference_le_controlled (n := n) (B := B) (z := z) σ h3

/-- Canonical per-rung Phase-II envelope.  For `β = 6/5`, this is
`A₂ exp(-a₂ γ lg n / 5)`. -/
noncomputable def phase2RungEnvelope
    (A₂ a₂ : ℝ) (γ n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (A₂ * Real.exp (-(a₂ * ((γ * Nat.log 2 n : ℕ) : ℝ) / 5)))

/-- Productive-event horizon shape for one Phase-II dyadic rung. -/
def phase2RungProductiveHorizon (C₂ n K : ℕ) : ℕ :=
  (5 * C₂ * n) / K

/-- Error-form Bellman transfer for one Phase-II rung.  The finite-size
condition required by Lemma 10 is deliberately explicit and is not derived from
the global `6γ lg n ≤ n` standing hypothesis. -/
theorem phase2_controlled_rung_of_reference
    (σ : Strategy n B) (h3 : 3 ≤ n)
    (γ C₂ K T : ℕ) (A₂ a₂ : ℝ)
    (hist : History n B) (q : Phase2Level n B z)
    (hlemma10_size : 68 * (γ * Nat.log 2 n) < 3 * n)
    (hT : T = phase2RungProductiveHorizon C₂ n K)
    (href :
      1 ≤
        stoppedReferenceHit
            (Phase2EntryFailure (n := n) (B := B) (z := z))
            (Phase2RungTarget (n := n) (B := B) (z := z) K)
            (phase2ReferenceStep (n := n) (B := B) (z := z) h3)
            T q + phase2RungEnvelope A₂ a₂ γ n) :
    1 ≤
      stoppedControlledHit
          (Phase2EntryFailure (n := n) (B := B) (z := z))
          (Phase2RungTarget (n := n) (B := B) (z := z) K)
          (phase2ControlledStep
            (n := n) (B := B) (z := z) σ h3)
          T hist q + phase2RungEnvelope A₂ a₂ γ n := by
  have _hsize := hlemma10_size
  have _horizon := hT
  exact href.trans
    (by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right
          (hitProb_ge_reference_of_kernel_stochDom
            (Phase2EntryFailure (n := n) (B := B) (z := z))
            (Phase2RungTarget (n := n) (B := B) (z := z) K)
            (phase2ReferenceStep (n := n) (B := B) (z := z) h3)
            (phase2ControlledStep
              (n := n) (B := B) (z := z) σ h3)
            (@phase2EntryFailure_lower (n := n) (B := B) (z := z))
            (@phase2RungTarget_upper (n := n) (B := B) (z := z) K)
            (phase2ReferenceStep_mono (n := n) (B := B) (z := z) h3)
            (phase2_reference_le_controlled (n := n) (B := B) (z := z) σ h3)
            T hist q)
          (phase2RungEnvelope A₂ a₂ γ n))

namespace Phase2RungExample

private def s : State 8 0 := by
  refine ⟨(⟨8, by decide⟩, ⟨0, by decide⟩), ?_⟩
  decide

private def q : Phase2Level 8 0 0 :=
  ⟨s, by rfl⟩

private def sigma : Strategy 8 0 :=
  { choose := fun _ _ => Control.neutral }

example :
    Phase2StrongTarget (n := 8) (B := 0) (z := 0) q := by
  norm_num [Phase2StrongTarget, q, s, State.x, State.z]

example :
    stoppedReferenceHit
        (Phase2EntryFailure (n := 8) (B := 0) (z := 0))
        (Phase2RungTarget (n := 8) (B := 0) (z := 0) 4)
        (phase2ReferenceStep (n := 8) (B := 0) (z := 0) (by norm_num))
        1 q ≤
      stoppedControlledHit
        (Phase2EntryFailure (n := 8) (B := 0) (z := 0))
        (Phase2RungTarget (n := 8) (B := 0) (z := 0) 4)
        (phase2ControlledStep
          (n := 8) (B := 0) (z := 0) sigma (by norm_num))
        1 [] q := by
  exact
    hitProb_ge_reference_of_kernel_stochDom
      (Phase2EntryFailure (n := 8) (B := 0) (z := 0))
      (Phase2RungTarget (n := 8) (B := 0) (z := 0) 4)
      (phase2ReferenceStep (n := 8) (B := 0) (z := 0) (by norm_num))
      (phase2ControlledStep
        (n := 8) (B := 0) (z := 0) sigma (by norm_num))
      (@phase2EntryFailure_lower (n := 8) (B := 0) (z := 0))
      (@phase2RungTarget_upper (n := 8) (B := 0) (z := 0) 4)
      (phase2ReferenceStep_mono (n := 8) (B := 0) (z := 0) (by norm_num))
      (phase2_reference_le_controlled
        (n := 8) (B := 0) (z := 0) sigma (by norm_num))
      1 [] q

end Phase2RungExample

end Tri.Byzantine

#print axioms Tri.Byzantine.phase2StrongTarget_iff_y_le_z
#print axioms Tri.Byzantine.phase2AggregateCap_upper
#print axioms Tri.Byzantine.phase2ReferenceStep_mono
#print axioms Tri.Byzantine.phase2_reference_le_controlled
#print axioms Tri.Byzantine.phase2_controlled_rung_of_reference
