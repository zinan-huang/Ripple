/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.PaperLemma10
import Tri.PaperLemma7
import Tri.Ladder

/-!
# Byzantine phase-II bridge lemmas

This file connects the physical Byzantine state space to the fixed-Byzantine-
count chains used by the phase-II rung estimates.  The bridge is stated without
natural-number subtraction so that all population guards remain explicit.
-/

namespace Tri.Byzantine

open scoped ENNReal NNReal

variable {n B : ℕ}

/-- Physical Phase-II exit: either the honest minority is no larger than the
Byzantine population, or the aggregate minority reaches the next cap.

NOTE: `Tri.ByzantinePhase2Rung` already has a `Phase2RungTarget` on the fibre type
`Phase2Level`; this is the PHYSICAL-state counterpart, hence the distinct name. -/
def Phase2PhysRungTarget (Knext : ℕ) (s : State n B) : Prop :=
  State.y s ≤ State.z s ∨
    Knext * (State.y s + State.z s) ≤ n

instance phase2PhysRungTargetDecidable (Knext : ℕ) :
    DecidablePred (fun s : State n B => Phase2PhysRungTarget (n := n) (B := B) Knext s) := by
  intro s
  unfold Phase2PhysRungTarget
  infer_instance

/-- Fixed-`z` count form of `Phase2PhysRungTarget`, with no natural subtraction. -/
def Phase2CountRungTarget (n z Knext x : ℕ) : Prop :=
  n ≤ x + 2 * z ∨ Knext * n ≤ Knext * x + n

instance phase2CountRungTargetDecidable (n z Knext : ℕ) :
    DecidablePred (Phase2CountRungTarget n z Knext) := by
  intro x
  unfold Phase2CountRungTarget
  infer_instance

/-- The physical and fixed-`z` count targets agree. -/
theorem phase2CountRungTarget_iff_state
    (Knext : ℕ) (s : State n B) :
    Phase2CountRungTarget n (State.z s) Knext (State.x s) ↔
      Phase2PhysRungTarget (n := n) (B := B) Knext s := by
  have htotal :
      State.x s + (State.y s + State.z s) = n := by
    have h := State.total s
    omega
  unfold Phase2CountRungTarget Phase2PhysRungTarget
  constructor
  · rintro (hstrong | hcap)
    · left
      omega
    · right
      have hcap' :
          Knext * State.x s +
              Knext * (State.y s + State.z s) ≤
            Knext * State.x s + n := by
        simpa [← htotal, Nat.mul_add] using hcap
      exact Nat.le_of_add_le_add_left hcap'
  · rintro (hstrong | hcap)
    · left
      omega
    · right
      calc
        Knext * n =
            Knext *
              (State.x s + (State.y s + State.z s)) := by
          rw [htotal]
        _ = Knext * State.x s +
              Knext * (State.y s + State.z s) := by
          rw [Nat.mul_add]
        _ ≤ Knext * State.x s + n :=
          Nat.add_le_add_left hcap _

/-- The non-strict large-population condition is enough to put the Lemma-10
floor at or below one half. -/
theorem phase2_floor_scalar
    (K n P d xLo : ℕ)
    (hK : 4 ≤ K)
    (hshare : K * P = n)
    (hden : P + d + xLo = n)
    (hlarge : 68 * d ≤ 3 * n) :
    12 * (P + d) ≤ 5 * xLo := by
  have hquarter : 4 * P ≤ n := by
    calc
      4 * P ≤ K * P := Nat.mul_le_mul_right P hK
      _ = n := hshare
  omega

/-- `Lemma7Target` is already absorbing for `relaxedProductiveTriChain`; its
explicit `freeze` is therefore definitionally removable. -/
theorem freeze_lemma7Target_relaxedProductiveTriChain
    (r : RelaxedRate) (n : ℕ) :
    freeze (Lemma7Target n) (relaxedProductiveTriChain r n) =
      relaxedProductiveTriChain r n := by
  funext x
  by_cases hx : Lemma7Target n x
  · rw [freeze_of_mem x hx]
    unfold relaxedProductiveTriChain
    rw [dif_neg]
    intro hphys
    unfold Lemma7Target at hx
    omega
  · exact freeze_of_not_mem x hx

/-- Exact-anchor Phase-II rung for the homogeneous constant-floor productive
chain.  The rate premise is exactly the one consumed by `lemma7_paper` at
`β = 6/5`. -/
theorem phase2_floor_exactAnchor_rung
    (r0 : RelaxedRate)
    (n P d x₀ xLo z Knext : ℕ)
    (h3 : 3 ≤ n)
    (hroom : P + d < n)
    (hpop : x₀ + P = n)
    (hxLo : xLo + d = x₀)
    (hdP : d ≤ P)
    (hfire : 0 < r0.fire)
    (hrate :
      (6 / 5 : NNReal) * (((P + d : ℕ) : NNReal)) ≤
        r0.fire * ((xLo : ℕ) : NNReal)) :
    Reaches
      (relaxedProductiveTriChain r0 n)
      (lemma7PaperDeadline (6 / 5 : NNReal) P)
      (fun x => x = x₀)
      (Phase2CountRungTarget n z Knext)
      ((2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-((((6 / 5 : NNReal) : ℝ) - 1) *
              (d : ℝ) / 4096)))) := by
  intro x hx
  subst x
  change
    terminalFailureMass
        (iter
          (relaxedProductiveTriChain r0 n)
          (lemma7PaperDeadline (6 / 5 : NNReal) P)
          x₀)
        (Phase2CountRungTarget n z Knext) ≤
      (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-((((6 / 5 : NNReal) : ℝ) - 1) *
              (d : ℝ) / 4096)))
  have hpaper :=
    lemma7_paper
      r0 (6 / 5 : NNReal) n P d x₀ xLo
      h3 hroom
      (by
        -- NNReal literal comparison: settle it in `ℝ≥0` via the order embedding.
        have : (1 : NNReal) < 6 / 5 := by
          rw [← NNReal.coe_lt_coe]; push_cast; norm_num
        exact this)
      (by
        have : (6 / 5 : NNReal) ≤ 2 := by
          rw [← NNReal.coe_le_coe]; push_cast; norm_num
        exact this)
      hpop hxLo hdP hfire hrate
  rw [freeze_lemma7Target_relaxedProductiveTriChain] at hpaper
  exact
    (terminalFailureMass_mono
      (iter
        (relaxedProductiveTriChain r0 n)
        (lemma7PaperDeadline (6 / 5 : NNReal) P)
        x₀)
      (Phase2CountRungTarget n z Knext)
      (Lemma7Target n)
      (by
        intro q hq
        left
        unfold Lemma7Target at hq
        omega)).trans hpaper

end Tri.Byzantine
