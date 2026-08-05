/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveStageLive

/-!
# Proper-stage completion in productive-event time

This file proves completion (b): unless an earlier stage boundary is hit,
`2n` productive reactions contain sufficiently many reactions involving the
plurality species.  The Chernoff argument is carried out directly on the same
deadline-stopped process used for completion (c).
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- Geometric expectation decay when the one-step estimate is only needed on
a support invariant. -/
theorem expect_iter_le_of_support_invariant
    {α : Type*} (K : α → PMF α) (P : α → Prop)
    (V : α → ℝ≥0∞) (c : ℝ≥0∞)
    (hclosed : ∀ s, P s → ∀ z, K s z ≠ 0 → P z)
    (hstep : ∀ s, P s → expect (K s) V ≤ c * V s) :
    ∀ T s, P s → expect (iter K T s) V ≤ c ^ T * V s := by
  intro T
  induction T with
  | zero =>
      intro s _hs
      simp
  | succ t ih =>
      intro s hs
      rw [iter_succ, expect_bind]
      calc
        (∑' a, K s a * expect (iter K t a) V) ≤
            ∑' a, K s a * (c ^ t * V a) := by
          apply ENNReal.tsum_le_tsum
          intro a
          by_cases hKa : K s a = 0
          · simp [hKa]
          · exact mul_le_mul_right (ih a (hclosed s hs a hKa)) _
        _ = c ^ t * ∑' a, K s a * V a := by
          rw [← ENNReal.tsum_mul_left]
          congr 1
          ext a
          ring
        _ ≤ c ^ t * (c * V s) :=
          mul_le_mul_right (hstep s hs) _
        _ = c ^ (t + 1) * V s := by ring

/-- The killed involving-count potential contracts on every state satisfying
the pathwise count envelope. -/
theorem productiveInvolvingStageDeadlineStop_count_super
    (h3 : 3 ≤ n) (X : Species m) (x0 S d target : ℕ)
    (hd2 : 2 ≤ d) (htargetn : target ≤ n)
    (w p p' : ℝ≥0∞)
    (hw : w ≤ 1) (hp : p + p' = 1)
    (hpFloor : p ≤ (x0 : ℝ≥0∞) / (2 * n : ℕ))
    (q : Config m n × ℕ)
    (hq : ProductiveInvolvingCountInv X x0 q) :
    expect
        (productiveInvolvingStageDeadlineStop h3 X S d target
          (properInvolvingTarget x0) q)
        (fun z =>
          if ProductiveProperStageLive X S d target
              (properInvolvingTarget x0) z
          then w ^ z.2 else 0) ≤
      (p' + p * w) *
        (if ProductiveProperStageLive X S d target
            (properInvolvingTarget x0) q
        then w ^ q.2 else 0) := by
  classical
  by_cases hlive :
      ProductiveProperStageLive X S d target
        (properInvolvingTarget x0) q
  · have hcond :
        HasPairwiseGap q.1 X d ∧ count q.1 X ≤ S ∧
          ¬ HasPairwiseGap q.1 X target ∧
            q.2 < properInvolvingTarget x0 := by
      simpa only [ProductiveProperStageLive] using hlive
    rw [show
        productiveInvolvingStageDeadlineStop h3 X S d target
            (properInvolvingTarget x0) q =
          productiveInvolvingCount h3 X q by
        simp [productiveInvolvingStageDeadlineStop, hcond.1,
          hcond.2.1, hcond.2.2.1, hcond.2.2.2]]
    rw [if_pos hlive]
    have hprod : productiveMass q.1 h3 ≠ 0 :=
      productiveMass_ne_zero_of_pairwiseGap_not_target
        q.1 h3 X d target hd2 htargetn hlive.1 hlive.2.2.1
    have hbounds :=
      productiveInvolvingCountInv_bounds_before_target
        X x0 q hq hlive.2.2.2
    have hpq :
        p ≤ productiveInvolvingMass q.1 h3 hprod X :=
      hpFloor.trans
        (initialCount_div_two_population_le_productive_involvingMass
          q.1 h3 hprod X x0 hbounds.1)
    calc
      expect (productiveInvolvingCount h3 X q)
          (fun z =>
            if ProductiveProperStageLive X S d target
                (properInvolvingTarget x0) z
            then w ^ z.2 else 0) ≤
          expect (productiveInvolvingCount h3 X q)
            (fun z => w ^ z.2) := by
        unfold expect
        exact ENNReal.tsum_le_tsum fun z =>
          mul_le_mul_right (by
            change
              (if ProductiveProperStageLive X S d target
                  (properInvolvingTarget x0) z
              then w ^ z.2 else 0) ≤ w ^ z.2
            split_ifs <;> simp) _
      _ ≤ (p' + p * w) * w ^ q.2 :=
        productiveInvolvingCount_step_of_lower
          q.1 h3 hprod X q.2 w p p' hw hp hpq
  · have hcond :
        ¬ (HasPairwiseGap q.1 X d ∧ count q.1 X ≤ S ∧
          ¬ HasPairwiseGap q.1 X target ∧
            q.2 < properInvolvingTarget x0) := by
      simpa only [ProductiveProperStageLive] using hlive
    rw [show
        productiveInvolvingStageDeadlineStop h3 X S d target
            (properInvolvingTarget x0) q =
          PMF.pure q by
        simp only [productiveInvolvingStageDeadlineStop, hcond, if_false]]
    rw [expect_pure]
    simp [hlive]

/-- Completion (b) on the common first-of-boundaries chain: after `2n`
productive reactions, the mass of states at which none of the other stage
boundaries has fired is at most `exp(-x0/8)`. -/
theorem productiveInvolvingStageDeadlineStop_live_two_population_deadline
    (h3 : 3 ≤ n) (X : Species m)
    (x0 S d target : ℕ) (hd2 : 2 ≤ d) (htargetn : target ≤ n)
    (c0 : Config m n) (hx0 : count c0 X = x0) :
    (∑' q : Config m n × ℕ,
      if ProductiveProperStageLive X S d target
          (properInvolvingTarget x0) q
      then
        iter
          (productiveInvolvingStageDeadlineStop h3 X S d target
            (properInvolvingTarget x0))
          (2 * n) (c0, 0) q
      else 0) ≤
      ENNReal.ofReal (Real.exp (-(x0 : ℝ) / 8)) := by
  let K :=
    productiveInvolvingStageDeadlineStop h3 X S d target
      (properInvolvingTarget x0)
  let P : Config m n × ℕ → Prop :=
    ProductiveInvolvingCountInv X x0
  let Bad : Config m n × ℕ → Prop := fun q =>
    ProductiveProperStageLive X S d target
      (properInvolvingTarget x0) q
  let w : ℝ≥0∞ := (1 : ℝ≥0∞) / 2
  let p : ℝ≥0∞ := (x0 : ℝ≥0∞) / (2 * n : ℕ)
  let p' : ℝ≥0∞ := 1 - p
  let α : ℝ≥0∞ := p' + p * w
  let V : Config m n × ℕ → ℝ≥0∞ := fun q =>
    if Bad q then w ^ q.2 else 0
  let θ : ℝ≥0∞ := w ^ (x0 / 2)
  have hx0n : x0 ≤ n := by
    rw [← hx0]
    have htotal := count_add_zSum c0 X
    omega
  have hpLe : p ≤ 1 := by
    dsimp only [p]
    have hcross : (x0 : ℝ≥0∞) ≤ (2 * n : ℕ) := by
      exact_mod_cast (hx0n.trans (by omega : n ≤ 2 * n))
    exact ENNReal.div_le_of_le_mul (by simpa using hcross)
  have hpSum : p + p' = 1 := by
    dsimp only [p']
    rw [add_comm]
    exact tsub_add_cancel_of_le hpLe
  have hP0 : P (c0, 0) := by
    dsimp only [P, ProductiveInvolvingCountInv]
    simp [hx0]
  have hclosed :
      ∀ q, P q → ∀ z, K q z ≠ 0 → P z := by
    intro q hq z hqz
    exact productiveInvolvingStageDeadlineStop_inv_of_apply_ne_zero
      h3 X x0 S d target (properInvolvingTarget x0) q hq z hqz
  have hstep :
      ∀ q, P q → expect (K q) V ≤ α * V q := by
    intro q hq
    simpa only [K, P, Bad, w, p, p', α, V] using
      productiveInvolvingStageDeadlineStop_count_super
        h3 X x0 S d target hd2 htargetn
        ((1 : ℝ≥0∞) / 2)
        ((x0 : ℝ≥0∞) / (2 * n : ℕ))
        (1 - (x0 : ℝ≥0∞) / (2 * n : ℕ))
        (by norm_num) hpSum le_rfl q hq
  have hV0 : V (c0, 0) ≤ 1 := by
    dsimp only [V, Bad]
    split_ifs <;> simp
  have hiter0 :=
    expect_iter_le_of_support_invariant
      K P V α hclosed hstep (2 * n) (c0, 0) hP0
  have hiter :
      expect (iter K (2 * n) (c0, 0)) V ≤ α ^ (2 * n) := by
    exact hiter0.trans (by
      calc
        α ^ (2 * n) * V (c0, 0) ≤ α ^ (2 * n) * 1 :=
          mul_le_mul_left' hV0 _
        _ = α ^ (2 * n) := mul_one _)
  have hθ0 : θ ≠ 0 := by
    dsimp only [θ, w]
    exact pow_ne_zero _ (by norm_num)
  have hθtop : θ ≠ ⊤ := by
    dsimp only [θ, w]
    exact ENNReal.pow_ne_top (by norm_num)
  have hsub : ∀ q,
      (if Bad q then iter K (2 * n) (c0, 0) q else 0) ≤
        (if θ ≤ V q then iter K (2 * n) (c0, 0) q else 0) := by
    intro q
    by_cases hq : Bad q
    · have hk : q.2 ≤ x0 / 2 := by
        dsimp only [Bad, ProductiveProperStageLive] at hq
        unfold properInvolvingTarget at hq
        omega
      have hθV : θ ≤ V q := by
        dsimp only [θ, V]
        rw [if_pos hq]
        exact pow_le_pow_right_of_le_one' (by
          dsimp only [w]
          norm_num) hk
      simp [hq, hθV]
    · simp [hq]
  have hmarkov :=
    markov_div (iter K (2 * n) (c0, 0)) V θ hθ0 hθtop
  have hquot :
      expect (iter K (2 * n) (c0, 0)) V / θ ≤
        α ^ (2 * n) / θ :=
    ENNReal.div_le_div_right hiter θ
  have hscalar :=
    productiveInvolving_two_population_error_le n x0 h3 hx0n
  simpa only [K, Bad, V, θ, α, p', p, w] using
    (ENNReal.tsum_le_tsum hsub).trans
      (hmarkov.trans (hquot.trans hscalar))

/-- Paper-parameter specialization of completion (b), using the capped
progress target. -/
theorem productiveProperStage_completion_b
    (h3 : 3 ≤ n) (X : Species m)
    (D x0 : ℕ) (hD4 : 4 ≤ D)
    (c0 : Config m n) (hx0 : count c0 X = x0) :
    (∑' q : Config m n × ℕ,
      if ProductiveProperStageLive X (properStageScale x0) (D / 2)
          (properStageTarget D n) (properInvolvingTarget x0) q
      then
        iter
          (productiveInvolvingStageDeadlineStop h3 X
            (properStageScale x0) (D / 2) (properStageTarget D n)
            (properInvolvingTarget x0))
          (2 * n) (c0, 0) q
      else 0) ≤
      ENNReal.ofReal (Real.exp (-(x0 : ℝ) / 8)) := by
  exact productiveInvolvingStageDeadlineStop_live_two_population_deadline
    h3 X x0 (properStageScale x0) (D / 2)
    (properStageTarget D n) (by omega)
    (properStageTarget_le_population D n) c0 hx0

/-- Fixed-competitor completion-(c) tail for any positive target no larger
than the uncapped `49D/48` target.  Capping can only improve the potential
quotient. -/
theorem productiveInvolvingStageDeadlineStop_fixed_pair_exp_tail_of_target_le
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (D x0 target T : ℕ) (hD4 : 4 ≤ D) (hDx0 : D ≤ x0)
    (htarget : 1 ≤ target) (htargetLe : target ≤ properPairTarget D)
    (c0 : Config m n) (hinit : D ≤ pairGapNat c0 X Y) :
    (∑' q : Config m n × ℕ,
      if pairGapNat q.1 X Y < target ∧ x0 ≤ 2 * q.2 then
        iter
          (productiveInvolvingStageDeadlineStop h3 X
            (properStageScale x0) (D / 2) target
            (properInvolvingTarget x0))
          T (c0, 0) q
      else 0) ≤
      ENNReal.ofReal
        (Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ))))) := by
  let q0 : ProductivePairJointState m n :=
    { config := c0, involving := 0, relevant := 0 }
  let S := properStageScale x0
  let d := D / 2
  let K := properInvolvingTarget x0
  let w := pairProperProgressTilt S d
  let φ := pairProperProgressFactor S d
  have hq0 : q0.CounterInv := by
    simp [q0, ProductivePairJointState.CounterInv]
  have htail :=
    productivePairJointStageDeadlineStop_involving_tail
      h3 X Y hXY S d target K T
      (properStageScale_pos x0 (by omega)) (by omega)
      (three_halfGap_le_properStageScale D x0 hDx0)
      htarget q0 hq0
  have hmap :=
    iter_productivePairJointStageDeadlineStop_map_involving
      h3 X Y S d target K T q0
  have hcommon :
      (∑' q : Config m n × ℕ,
        if pairGapNat q.1 X Y < target ∧ K ≤ q.2 then
          iter (productiveInvolvingStageDeadlineStop
            h3 X S d target K) T q0.toInvolving q
        else 0) =
      ∑' z : ProductivePairJointState m n,
        if pairGapNat z.config X Y < target ∧ K ≤ z.involving then
          iter (productivePairJointStageDeadlineStop
            h3 X Y S d target K) T q0 z
        else 0 := by
    let Bad : Config m n × ℕ → Prop := fun q =>
      pairGapNat q.1 X Y < target ∧ K ≤ q.2
    calc
      (∑' q : Config m n × ℕ,
          if pairGapNat q.1 X Y < target ∧ K ≤ q.2 then
            iter (productiveInvolvingStageDeadlineStop
              h3 X S d target K) T q0.toInvolving q
          else 0) =
        expect
          (iter (productiveInvolvingStageDeadlineStop
            h3 X S d target K) T q0.toInvolving)
          (fun q => (if Bad q then 1 else 0 : ℝ≥0∞)) := by
        unfold expect
        apply tsum_congr
        intro q
        by_cases hq : Bad q <;> simp [Bad, hq]
      _ = expect
          ((iter (productivePairJointStageDeadlineStop
            h3 X Y S d target K) T q0).map
              ProductivePairJointState.toInvolving)
          (fun q => (if Bad q then 1 else 0 : ℝ≥0∞)) := by
        rw [hmap]
      _ = expect
          (iter (productivePairJointStageDeadlineStop
            h3 X Y S d target K) T q0)
          (fun z => (if Bad z.toInvolving then 1 else 0 : ℝ≥0∞)) := by
        rw [expect_map]
      _ = ∑' z : ProductivePairJointState m n,
          if pairGapNat z.config X Y < target ∧ K ≤ z.involving then
            iter (productivePairJointStageDeadlineStop
              h3 X Y S d target K) T q0 z
          else 0 := by
        unfold expect
        apply tsum_congr
        intro z
        by_cases hz : Bad z.toInvolving
        · have hz' :
              pairGapNat z.config X Y < target ∧ K ≤ z.involving := by
            simpa [Bad, ProductivePairJointState.toInvolving] using hz
          simp [hz, hz']
        · have hz' :
              ¬ (pairGapNat z.config X Y < target ∧ K ≤ z.involving) := by
            simpa [Bad, ProductivePairJointState.toInvolving] using hz
          simp [hz, hz']
  have hw1 : w ≤ 1 := by
    dsimp only [w]
    exact pairProperProgressTilt_le_one S d
      (properStageScale_pos x0 (by omega))
  have hnum :
      pairProgressPotential X Y w φ q0.toRelevant ≤ w ^ D := by
    dsimp only [q0, ProductivePairJointState.toRelevant,
      pairProgressPotential]
    simp only [pow_zero, mul_one]
    exact pow_le_pow_right_of_le_one' hw1 hinit
  have hquot :
      pairProgressPotential X Y w φ q0.toRelevant /
          (w ^ (target - 1) * (φ⁻¹) ^ K) ≤
        w ^ D / (w ^ (target - 1) * (φ⁻¹) ^ K) :=
    ENNReal.div_le_div_right hnum _
  have htargetPred :
      target - 1 ≤ properPairTarget D - 1 :=
    Nat.sub_le_sub_right htargetLe 1
  have hpowDen :
      w ^ (properPairTarget D - 1) ≤ w ^ (target - 1) :=
    pow_le_pow_right_of_le_one' hw1 htargetPred
  have hden :
      w ^ (properPairTarget D - 1) * (φ⁻¹) ^ K ≤
        w ^ (target - 1) * (φ⁻¹) ^ K :=
    by
      simpa [mul_comm] using
        (mul_le_mul_right hpowDen ((φ⁻¹) ^ K))
  have hcap :
      w ^ D / (w ^ (target - 1) * (φ⁻¹) ^ K) ≤
        w ^ D /
          (w ^ (properPairTarget D - 1) * (φ⁻¹) ^ K) :=
    ENNReal.div_le_div_left hden _
  have hscalar := properProgress_quotient_le_exp D x0 hD4 hDx0
  simpa only [properInvolvingTarget_le_iff, q0,
    ProductivePairJointState.toInvolving,
    S, d, K, w, φ] using
      hcommon.le.trans
        (htail.trans (hquot.trans (hcap.trans hscalar)))

/-- Capped fixed-competitor completion-(c) tail. -/
theorem productiveInvolvingStageDeadlineStop_fixed_pair_capped_exp_tail
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (D x0 T : ℕ) (hD4 : 4 ≤ D) (hDx0 : D ≤ x0)
    (hDn : D ≤ n)
    (c0 : Config m n) (hinit : D ≤ pairGapNat c0 X Y) :
    (∑' q : Config m n × ℕ,
      if pairGapNat q.1 X Y < properStageTarget D n ∧
          x0 ≤ 2 * q.2 then
        iter
          (productiveInvolvingStageDeadlineStop h3 X
            (properStageScale x0) (D / 2) (properStageTarget D n)
            (properInvolvingTarget x0))
          T (c0, 0) q
      else 0) ≤
      ENNReal.ofReal
        (Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ))))) := by
  exact
    productiveInvolvingStageDeadlineStop_fixed_pair_exp_tail_of_target_le
      h3 X Y hXY D x0 (properStageTarget D n) T
      hD4 hDx0
      (properStageTarget_pos D n (by omega) hDn)
      (properStageTarget_le_pairTarget D n) c0 hinit

/-- Genuine all-competitor completion-(c) hitting bound with the paper's
capped target. -/
theorem productiveInvolvingStageDeadlineStop_global_capped_exp_tail
    (h3 : 3 ≤ n) (X : Species m)
    (D x0 T : ℕ) (hD4 : 4 ≤ D) (hDx0 : D ≤ x0)
    (hDn : D ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    globalProperTargetFailureMass
        (iter
          (productiveInvolvingStageDeadlineStop h3 X
            (properStageScale x0) (D / 2) (properStageTarget D n)
            (properInvolvingTarget x0))
          T (c0, 0))
        X (properStageTarget D n) (properInvolvingTarget x0) ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ))))) := by
  calc
    globalProperTargetFailureMass
        (iter
          (productiveInvolvingStageDeadlineStop h3 X
            (properStageScale x0) (D / 2) (properStageTarget D n)
            (properInvolvingTarget x0))
          T (c0, 0))
        X (properStageTarget D n) (properInvolvingTarget x0) ≤
      ∑ Y ∈ Finset.univ.erase X,
        ∑' q : Config m n × ℕ,
          if pairGapNat q.1 X Y < properStageTarget D n ∧
              properInvolvingTarget x0 ≤ q.2 then
            iter
              (productiveInvolvingStageDeadlineStop h3 X
                (properStageScale x0) (D / 2) (properStageTarget D n)
                (properInvolvingTarget x0))
              T (c0, 0) q
          else 0 :=
      globalProperTargetFailureMass_le_pair_sum
        _ X (properStageTarget D n) (properInvolvingTarget x0)
        (properStageTarget_pos D n (by omega) hDn)
    _ ≤ ∑ Y ∈ Finset.univ.erase X,
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ))))) := by
      apply Finset.sum_le_sum
      intro Y hY
      have hYX : Y ≠ X := (Finset.mem_erase.mp hY).1
      have hpair : D ≤ pairGapNat c0 X Y := by
        have hg := hinit Y hYX
        unfold pairGapNat
        omega
      simpa only [properInvolvingTarget_le_iff] using
        productiveInvolvingStageDeadlineStop_fixed_pair_capped_exp_tail
          h3 X Y (Ne.symm hYX) D x0 T hD4 hDx0 hDn c0 hpair
    _ = ((Finset.univ.erase X).card : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ))))) := by
      simp
    _ ≤ (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ))))) := by
      gcongr
      simp

end Tri.Multi

#print axioms Tri.Multi.expect_iter_le_of_support_invariant
#print axioms Tri.Multi.productiveInvolvingStageDeadlineStop_count_super
#print axioms Tri.Multi.productiveProperStage_completion_b
#print axioms Tri.Multi.productiveInvolvingStageDeadlineStop_global_capped_exp_tail
