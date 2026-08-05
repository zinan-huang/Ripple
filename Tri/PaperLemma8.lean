/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.ByzantinePhase1Rung
import Tri.StoppedHitMonotone
import Tri.TimeChangeHitting

/-!
# Paper Lemma 8: the worst Byzantine response minimizes upward reachability

The printed proof only compares two starting configurations under one fixed
law. The missing policy comparison is a Bellman induction. On a fixed
Byzantine-count fiber the complete physical state is determined by the honest
`X` count, so the required order is one-dimensional.

This file first proves the finite-horizon comparison against every
history-dependent strategy, then takes the supremum over all finite horizons.
The hit event is the exact paper configuration: on the fixed-`z` fiber it is
equivalent to equality of the honest `X` count. Nearest-neighbour support
identifies this exact event with the upper Bellman target.
-/

namespace Tri

open scoped ENNReal

noncomputable section

variable {α : Type*}

/-! ## Generic hitting-probability reductions

These lemmas isolate two facts used by the paper argument: removing an empty
lower stop recovers ordinary hitting probability, and nearest-neighbour
support turns an upper-threshold event into hitting the exact threshold.
-/

/-- With no lower stopping set, the stopped Bellman value is the ordinary
finite-horizon hitting probability. -/
theorem stoppedReferenceHit_false_eq_hitProb
    (G : α → Prop) [DecidablePred G] (K : α → PMF α) :
    ∀ T s,
      stoppedReferenceHit (fun _ : α => False) G K T s =
        hitProb G K T s := by
  intro T
  induction T with
  | zero =>
      intro s
      simp [stoppedReferenceHit, hitProb, ind]
  | succ T ih =>
      intro s
      by_cases hs : G s
      · rw [hitProb_eq_one_of_mem G K (T + 1) s hs]
        simp [stoppedReferenceHit, hs]
      · rw [hitProb_succ_of_not G K T s hs]
        simp only [stoppedReferenceHit, if_neg hs]
        unfold expect
        apply tsum_congr
        intro q
        rw [ih q]

/-- Hitting probability only depends on the target predicate up to pointwise
equivalence. -/
theorem lemma8_hitProb_congr
    (K : α → PMF α) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q]
    (h : ∀ s, P s ↔ Q s) (T : ℕ) (s₀ : α) :
    hitProb P K T s₀ = hitProb Q K T s₀ := by
  have hfreeze : freeze P K = freeze Q K := by
    funext s
    unfold freeze
    by_cases hs : P s
    · rw [if_pos hs, if_pos ((h s).1 hs)]
    · rw [if_neg hs, if_neg (fun hq => hs ((h s).2 hq))]
  unfold hitProb
  rw [hfreeze]
  congr 1
  funext s
  unfold ind
  by_cases hs : P s
  · rw [if_pos hs, if_pos ((h s).1 hs)]
  · rw [if_neg hs, if_neg (fun hq => hs ((h s).2 hq))]

/-- A nearest-neighbour chain started at or below an integer target hits the
upper target by time `T` exactly when it hits the target level by time `T`. -/
theorem hitProb_upper_eq_exact_of_support_le_succ
    (level : α → ℕ) (K : α → PMF α)
    (target : ℕ)
    (hstep : ∀ s q, K s q ≠ 0 → level q ≤ level s + 1) :
    ∀ T s, level s ≤ target →
      hitProb (fun q => target ≤ level q) K T s =
        hitProb (fun q => level q = target) K T s := by
  intro T
  induction T with
  | zero =>
      intro s hs
      unfold hitProb ind
      simp only [iter_zero, expect_pure]
      by_cases hEq : level s = target
      · simp [hEq]
      · have hUpper : ¬ target ≤ level s := by omega
        simp [hEq, hUpper]
  | succ T ih =>
      intro s hs
      by_cases hEq : level s = target
      · have hUpper : target ≤ level s := by omega
        rw [hitProb_eq_one_of_mem
              (fun q => target ≤ level q) K (T + 1) s hUpper,
            hitProb_eq_one_of_mem
              (fun q => level q = target) K (T + 1) s hEq]
      · have hlt : level s < target := by omega
        have hnotUpper : ¬ target ≤ level s := by omega
        rw [hitProb_succ_of_not
              (fun q => target ≤ level q) K T s hnotUpper,
            hitProb_succ_of_not
              (fun q => level q = target) K T s hEq]
        apply tsum_congr
        intro q
        by_cases hsq : K s q = 0
        · simp [hsq]
        · rw [ih q (by
            exact (hstep s q hsq).trans (by omega))]

namespace Byzantine

variable {n B z : ℕ}

/-! ## Exact fixed-fiber target -/

/-- The exact target configuration in the fixed Byzantine-count fiber. -/
noncomputable def lemma8TargetLevel
    (q : Phase1Level n B z) (ell : ℕ)
    (hroom : State.x q.1 + ell + z ≤ n) :
    Phase1Level n B z :=
  phase1LevelWithX q (State.x q.1 + ell) (by omega)

@[simp] theorem lemma8TargetLevel_x
    (q : Phase1Level n B z) (ell : ℕ)
    (hroom : State.x q.1 + ell + z ≤ n) :
    State.x (lemma8TargetLevel q ell hroom).1 =
      State.x q.1 + ell :=
  rfl

@[simp] theorem lemma8TargetLevel_z
    (q : Phase1Level n B z) (ell : ℕ)
    (hroom : State.x q.1 + ell + z ≤ n) :
    State.z (lemma8TargetLevel q ell hroom).1 = z :=
  q.2

/-- The target lowers honest `Y` by exactly `ell`, stated without natural
subtraction. -/
theorem lemma8TargetLevel_y_add
    (q : Phase1Level n B z) (ell : ℕ)
    (hroom : State.x q.1 + ell + z ≤ n) :
    State.y (lemma8TargetLevel q ell hroom).1 + ell =
      State.y q.1 := by
  have hqTotal := State.total q.1
  have htTotal := State.total (lemma8TargetLevel q ell hroom).1
  simp only [lemma8TargetLevel_x, lemma8TargetLevel_z] at htTotal
  rw [q.2] at hqTotal
  omega

/-- On a fixed-`z` fiber, equality of the `X` count is equality with the exact
paper target configuration. -/
theorem lemma8_exact_target_iff
    (q r : Phase1Level n B z) (ell : ℕ)
    (hroom : State.x q.1 + ell + z ≤ n) :
    State.x r.1 = State.x q.1 + ell ↔
      r = lemma8TargetLevel q ell hroom := by
  constructor
  · intro hr
    apply phase1Level_ext_x
    simpa using hr
  · rintro rfl
    simp

/-! ## Nearest-neighbour support -/

/-- Every fixed-control physical update increases the honest `X` count by at
most one. -/
theorem nextState_x_le_succ
    (u : Control) (s : State n B) (k : TripleComp) :
    State.x (nextState u s k) ≤ State.x s + 1 := by
  by_cases hk : TripleComp.weightAt s k = 0
  · simp [nextState, hk]
  · rw [nextState_x_of_weight_ne_zero u s k hk]
    cases haction : u.action k with
    | down =>
        simp [Action.nextX]
        omega
    | stay => simp [Action.nextX]
    | up => simp [Action.nextX]

/-- The paper-worst fixed-fiber reference step is nearest-neighbour upward. -/
theorem phase1ReferenceStep_support_le_succ
    (h3 : 3 ≤ n) (q r : Phase1Level n B z)
    (hqr : phase1ReferenceStep h3 q r ≠ 0) :
    State.x r.1 ≤ State.x q.1 + 1 := by
  unfold phase1ReferenceStep at hqr
  rw [PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hqr
  push Not at hqr
  obtain ⟨k, hk⟩ := hqr
  split_ifs at hk with hkr
  · subst r
    exact nextState_x_le_succ Control.worst q.1 k
  · exact absurd rfl hk

/-- The joint history/state step of every adaptive strategy is also
nearest-neighbour upward. -/
theorem phase1ControlledStep_support_le_succ
    (σ : Strategy n B) (h3 : 3 ≤ n)
    (q r : History n B × Phase1Level n B z)
    (hqr :
      phase1ControlledStep σ h3 q.1 q.2 r ≠ 0) :
    State.x r.2.1 ≤ State.x q.2.1 + 1 := by
  unfold phase1ControlledStep at hqr
  rw [PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hqr
  push Not at hqr
  obtain ⟨k, hk⟩ := hqr
  split_ifs at hk with hkr
  · subst r
    exact nextState_x_le_succ (σ.choose q.1 q.2.1) q.2.1 k
  · exact absurd rfl hk

/-! ## Finite-horizon policy comparison -/

/-- Exact eventual reach probability under the paper-worst fixed response. -/
noncomputable def lemma8WorstReachProbability
    (h3 : 3 ≤ n) (q : Phase1Level n B z) (ell : ℕ)
    (hroom : State.x q.1 + ell + z ≤ n) :
    ℝ≥0∞ :=
  everHit
    (fun r : Phase1Level n B z =>
      r = lemma8TargetLevel q ell hroom)
    (phase1ReferenceStep h3) q

/-- Exact eventual reach probability under an arbitrary history-dependent
Byzantine strategy. -/
noncomputable def lemma8StrategyReachProbability
    (σ : Strategy n B) (h3 : 3 ≤ n)
    (hist : History n B) (q : Phase1Level n B z) (ell : ℕ)
    (hroom : State.x q.1 + ell + z ≤ n) :
    ℝ≥0∞ :=
  everHit
    (fun r : History n B × Phase1Level n B z =>
      r.2 = lemma8TargetLevel q ell hroom)
    (fun r => phase1ControlledStep σ h3 r.1 r.2)
    (hist, q)

/-- Finite-horizon form of Paper Lemma 8. The adverse fixed response has no
larger exact-target hitting probability than any history-dependent response. -/
theorem lemma8_finite_horizon
    (σ : Strategy n B) (h3 : 3 ≤ n)
    (hist : History n B) (q : Phase1Level n B z)
    (ell T : ℕ) (hell : 0 < ell)
    (hroom : State.x q.1 + ell + z ≤ n) :
    hitProb
        (fun r : Phase1Level n B z =>
          r = lemma8TargetLevel q ell hroom)
        (phase1ReferenceStep h3) T q ≤
      hitProb
        (fun r : History n B × Phase1Level n B z =>
          r.2 = lemma8TargetLevel q ell hroom)
        (fun r => phase1ControlledStep σ h3 r.1 r.2)
        T (hist, q) := by
  let target := State.x q.1 + ell
  let Target := lemma8TargetLevel q ell hroom
  let Upper : Phase1Level n B z → Prop :=
    fun r => target ≤ State.x r.1
  let JointUpper : History n B × Phase1Level n B z → Prop :=
    fun r => target ≤ State.x r.2.1
  have hstart : State.x q.1 ≤ target := by
    dsimp only [target]
    omega
  have hrefExact :
      hitProb Upper (phase1ReferenceStep h3) T q =
        hitProb
          (fun r : Phase1Level n B z => r = Target)
          (phase1ReferenceStep h3) T q := by
    calc
      hitProb Upper (phase1ReferenceStep h3) T q =
          hitProb
            (fun r : Phase1Level n B z =>
              State.x r.1 = target)
            (phase1ReferenceStep h3) T q := by
        exact
          hitProb_upper_eq_exact_of_support_le_succ
            (fun r : Phase1Level n B z => State.x r.1)
            (phase1ReferenceStep h3) target
            (phase1ReferenceStep_support_le_succ h3)
            T q hstart
      _ =
          hitProb
            (fun r : Phase1Level n B z => r = Target)
            (phase1ReferenceStep h3) T q := by
        apply lemma8_hitProb_congr
        intro r
        exact lemma8_exact_target_iff q r ell hroom
  have hctlExact :
      hitProb JointUpper
          (fun r => phase1ControlledStep σ h3 r.1 r.2)
          T (hist, q) =
        hitProb
          (fun r : History n B × Phase1Level n B z =>
            r.2 = Target)
          (fun r => phase1ControlledStep σ h3 r.1 r.2)
          T (hist, q) := by
    calc
      hitProb JointUpper
          (fun r => phase1ControlledStep σ h3 r.1 r.2)
          T (hist, q) =
        hitProb
          (fun r : History n B × Phase1Level n B z =>
            State.x r.2.1 = target)
          (fun r => phase1ControlledStep σ h3 r.1 r.2)
          T (hist, q) := by
        exact
          hitProb_upper_eq_exact_of_support_le_succ
            (fun r : History n B × Phase1Level n B z =>
              State.x r.2.1)
            (fun r => phase1ControlledStep σ h3 r.1 r.2)
            target
            (phase1ControlledStep_support_le_succ σ h3)
            T (hist, q) hstart
      _ =
        hitProb
          (fun r : History n B × Phase1Level n B z =>
            r.2 = Target)
          (fun r => phase1ControlledStep σ h3 r.1 r.2)
          T (hist, q) := by
        apply lemma8_hitProb_congr
        intro r
        exact lemma8_exact_target_iff q r.2 ell hroom
  have hBellman :
      stoppedReferenceHit
          (fun _ : Phase1Level n B z => False)
          Upper (phase1ReferenceStep h3) T q ≤
        stoppedControlledHit
          (fun _ : Phase1Level n B z => False)
          Upper (phase1ControlledStep σ h3) T hist q := by
    exact
      hitProb_ge_reference_of_kernel_stochDom
        (fun _ : Phase1Level n B z => False)
        Upper
        (phase1ReferenceStep h3)
        (phase1ControlledStep σ h3)
        (by
          intro i j hij hj
          exact False.elim hj)
        (by
          intro i j hij hi
          exact hi.trans hij)
        (phase1ReferenceStep_mono h3)
        (phase1_reference_le_controlled σ h3)
        T hist q
  change
    hitProb
        (fun r : Phase1Level n B z => r = Target)
        (phase1ReferenceStep h3) T q ≤
      hitProb
        (fun r : History n B × Phase1Level n B z =>
          r.2 = Target)
        (fun r => phase1ControlledStep σ h3 r.1 r.2)
        T (hist, q)
  calc
    hitProb
          (fun r : Phase1Level n B z => r = Target)
          (phase1ReferenceStep h3) T q =
        hitProb Upper (phase1ReferenceStep h3) T q :=
      hrefExact.symm
    _ =
        stoppedReferenceHit
          (fun _ : Phase1Level n B z => False)
          Upper (phase1ReferenceStep h3) T q :=
      (stoppedReferenceHit_false_eq_hitProb
        Upper (phase1ReferenceStep h3) T q).symm
    _ ≤
        stoppedControlledHit
          (fun _ : Phase1Level n B z => False)
          Upper (phase1ControlledStep σ h3) T hist q :=
      hBellman
    _ =
        stoppedReferenceHit
          (fun r : History n B × Phase1Level n B z => False)
          JointUpper
          (fun r => phase1ControlledStep σ h3 r.1 r.2)
          T (hist, q) := by
      exact
        stoppedControlledHit_eq_jointReferenceHit
          (fun _ : Phase1Level n B z => False)
          Upper (phase1ControlledStep σ h3)
          T hist q
    _ =
        hitProb JointUpper
          (fun r => phase1ControlledStep σ h3 r.1 r.2)
          T (hist, q) :=
      stoppedReferenceHit_false_eq_hitProb
        JointUpper
        (fun r => phase1ControlledStep σ h3 r.1 r.2)
        T (hist, q)
    _ =
        hitProb
          (fun r : History n B × Phase1Level n B z =>
            r.2 = Target)
          (fun r => phase1ControlledStep σ h3 r.1 r.2)
          T (hist, q) :=
      hctlExact

/-! ## Passage to eventual hitting

Taking the supremum over all finite horizons converts the Bellman comparison
into the eventual exact-target hitting probability claimed in the paper.
-/

/-- **Paper Lemma 8.** Among all history-dependent Byzantine response
strategies, the paper's fixed adverse response minimizes the probability of
ever reaching the exact configuration obtained by converting `ell` honest
`Y` molecules to honest `X` molecules. -/
theorem lemma8
    (σ : Strategy n B) (h3 : 3 ≤ n)
    (hist : History n B) (q : Phase1Level n B z)
    (ell : ℕ) (hell : 0 < ell)
    (hroom : State.x q.1 + ell + z ≤ n) :
    lemma8WorstReachProbability h3 q ell hroom ≤
      lemma8StrategyReachProbability σ h3 hist q ell hroom := by
  unfold lemma8WorstReachProbability
    lemma8StrategyReachProbability everHit
  exact iSup_mono fun T =>
    lemma8_finite_horizon
      σ h3 hist q ell T hell hroom

end Byzantine

end

end Tri

#print axioms Tri.stoppedReferenceHit_false_eq_hitProb
#print axioms Tri.hitProb_upper_eq_exact_of_support_le_succ
#print axioms Tri.Byzantine.lemma8TargetLevel_y_add
#print axioms Tri.Byzantine.phase1ReferenceStep_support_le_succ
#print axioms Tri.Byzantine.phase1ControlledStep_support_le_succ
#print axioms Tri.Byzantine.lemma8_finite_horizon
#print axioms Tri.Byzantine.lemma8
