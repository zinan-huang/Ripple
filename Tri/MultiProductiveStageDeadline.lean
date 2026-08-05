/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveStageProgress

/-!
# Proper-stage involvement deadline

Completion (c) is a hitting event: the stage freezes when the involvement
counter first reaches its deadline.  Since that boundary depends on the
involvement counter, the relevant-counter marginal alone is not Markov.  The
progress potential is therefore iterated directly on the full joint state.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- Common proper-stage involvement process stopped at the involvement
deadline as well as the safety and global-success boundaries. -/
noncomputable def productiveInvolvingStageDeadlineStop
    (h3 : 3 ≤ n) (X : Species m) (S d target K : ℕ) :
    Config m n × ℕ → PMF (Config m n × ℕ) := by
  classical
  exact fun q =>
    if HasPairwiseGap q.1 X d ∧ count q.1 X ≤ S ∧
        ¬ HasPairwiseGap q.1 X target ∧ q.2 < K then
      productiveInvolvingCount h3 X q
    else
      PMF.pure q

/-- Full joint process stopped at the common involvement deadline. -/
noncomputable def productivePairJointStageDeadlineStop
    (h3 : 3 ≤ n) (X Y : Species m) (S d target K : ℕ) :
    ProductivePairJointState m n → PMF (ProductivePairJointState m n) := by
  classical
  exact fun q =>
    if HasPairwiseGap q.config X d ∧ count q.config X ≤ S ∧
        ¬ HasPairwiseGap q.config X target ∧ q.involving < K then
      productivePairJointCount h3 X Y q
    else
      PMF.pure q

/-- One unstopped joint step conserves the repaired potential pulled back
from its relevant-counter marginal. -/
theorem productivePairJointCount_proper_conserve
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d : ℕ) (hS : 0 < S) (hd2 : 2 ≤ d) (hd3S : 3 * d ≤ S)
    (q : ProductivePairJointState m n)
    (hxS : count q.config X ≤ S)
    (hgap : HasPairwiseGap q.config X d) :
    expect (productivePairJointCount h3 X Y q)
        (fun z => pairProgressPotential X Y
          (pairProperProgressTilt S d) (pairProperProgressFactor S d)
          z.toRelevant) ≤
      pairProgressPotential X Y
        (pairProperProgressTilt S d) (pairProperProgressFactor S d)
        q.toRelevant := by
  rw [← expect_map, productivePairJointCount_map_relevant]
  exact productivePairRelevantCount_proper_conserve
    q.config h3 X Y hXY q.relevant S d hS hd2 hd3S hxS hgap

/-- The full joint potential remains a supermartingale after the involvement
deadline stop. -/
theorem productivePairJointStageDeadlineStop_proper_conserve
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d target K : ℕ) (hS : 0 < S) (hd2 : 2 ≤ d)
    (hd3S : 3 * d ≤ S)
    (q : ProductivePairJointState m n) :
    expect
        (productivePairJointStageDeadlineStop h3 X Y S d target K q)
        (fun z => pairProgressPotential X Y
          (pairProperProgressTilt S d) (pairProperProgressFactor S d)
          z.toRelevant) ≤
      pairProgressPotential X Y
        (pairProperProgressTilt S d) (pairProperProgressFactor S d)
        q.toRelevant := by
  classical
  unfold productivePairJointStageDeadlineStop
  split_ifs with hlive
  · exact productivePairJointCount_proper_conserve
      h3 X Y hXY S d hS hd2 hd3S q hlive.2.1 hlive.1
  · simp only [expect_pure]
    exact le_rfl

/-- The deadline-stopped joint process projects to the common
involvement-clock process. -/
theorem productivePairJointStageDeadlineStop_map_involving
    (h3 : 3 ≤ n) (X Y : Species m) (S d target K : ℕ)
    (q : ProductivePairJointState m n) :
    (productivePairJointStageDeadlineStop h3 X Y S d target K q).map
        ProductivePairJointState.toInvolving =
      productiveInvolvingStageDeadlineStop h3 X S d target K
        q.toInvolving := by
  classical
  unfold productivePairJointStageDeadlineStop
    productiveInvolvingStageDeadlineStop
  change
    (if HasPairwiseGap q.config X d ∧ count q.config X ≤ S ∧
          ¬ HasPairwiseGap q.config X target ∧ q.involving < K then
        productivePairJointCount h3 X Y q
      else PMF.pure q).map ProductivePairJointState.toInvolving =
      if HasPairwiseGap q.config X d ∧ count q.config X ≤ S ∧
          ¬ HasPairwiseGap q.config X target ∧ q.involving < K then
        productiveInvolvingCount h3 X q.toInvolving
      else PMF.pure q.toInvolving
  by_cases hlive :
      HasPairwiseGap q.config X d ∧ count q.config X ≤ S ∧
        ¬ HasPairwiseGap q.config X target ∧ q.involving < K
  · rw [if_pos hlive, if_pos hlive]
    exact productivePairJointCount_map_involving h3 X Y q
  · rw [if_neg hlive, if_neg hlive]
    exact PMF.pure_map _ _

/-- The deadline-stopped joint kernel preserves counter ordering on support. -/
theorem productivePairJointStageDeadlineStop_counterInv_of_apply_ne_zero
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d target K : ℕ)
    (q : ProductivePairJointState m n) (hq : q.CounterInv)
    (z : ProductivePairJointState m n)
    (hqz :
      productivePairJointStageDeadlineStop h3 X Y S d target K q z ≠ 0) :
    z.CounterInv := by
  classical
  unfold productivePairJointStageDeadlineStop at hqz
  by_cases hlive :
      HasPairwiseGap q.config X d ∧ count q.config X ≤ S ∧
        ¬ HasPairwiseGap q.config X target ∧ q.involving < K
  · rw [if_pos hlive] at hqz
    exact productivePairJointCount_counterInv_of_apply_ne_zero
      h3 X Y hXY q hq z hqz
  · rw [if_neg hlive] at hqz
    simp only [PMF.pure_apply] at hqz
    by_cases hzq : z = q
    · simpa [hzq] using hq
    · simp [hzq] at hqz

theorem productivePairJointStageDeadlineStop_iter_counterInv
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d target K T : ℕ) (q z : ProductivePairJointState m n)
    (hq : q.CounterInv)
    (hqz :
      iter (productivePairJointStageDeadlineStop h3 X Y S d target K)
        T q z ≠ 0) :
    z.CounterInv := by
  induction T generalizing q with
  | zero =>
      simp only [iter, PMF.pure_apply] at hqz
      by_cases hzq : z = q
      · simpa [hzq] using hq
      · simp [hzq] at hqz
  | succ T ih =>
      rw [iter_succ, PMF.bind_apply] at hqz
      by_contra hzInv
      apply hqz
      rw [ENNReal.tsum_eq_zero]
      intro a
      by_cases hqa :
          productivePairJointStageDeadlineStop h3 X Y S d target K q a = 0
      · simp [hqa]
      · have haInv :=
          productivePairJointStageDeadlineStop_counterInv_of_apply_ne_zero
            h3 X Y hXY S d target K q hq a hqa
        have hiaz :
            iter (productivePairJointStageDeadlineStop
              h3 X Y S d target K) T a z = 0 := by
          by_contra hne
          exact hzInv (ih a haInv hne)
        simp [hiaz]

theorem iter_productivePairJointStageDeadlineStop_map_involving
    (h3 : 3 ≤ n) (X Y : Species m) (S d target K T : ℕ)
    (q : ProductivePairJointState m n) :
    (iter (productivePairJointStageDeadlineStop h3 X Y S d target K)
        T q).map ProductivePairJointState.toInvolving =
      iter (productiveInvolvingStageDeadlineStop h3 X S d target K)
        T q.toInvolving := by
  induction T generalizing q with
  | zero => exact PMF.pure_map _ _
  | succ T ih =>
      rw [iter_succ, iter_succ, PMF.map_bind]
      simp_rw [ih]
      change
        (productivePairJointStageDeadlineStop h3 X Y S d target K q).bind
            ((iter (productiveInvolvingStageDeadlineStop
              h3 X S d target K) T) ∘
              ProductivePairJointState.toInvolving) = _
      rw [← PMF.bind_map,
        productivePairJointStageDeadlineStop_map_involving]

/-- Relevant-counter endpoint tail on the full deadline-stopped joint
process. -/
theorem productivePairJointStageDeadlineStop_relevant_tail
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d target K T : ℕ) (hS : 0 < S) (hd2 : 2 ≤ d)
    (hd3S : 3 * d ≤ S) (htarget : 1 ≤ target)
    (q0 : ProductivePairJointState m n) :
    (∑' z : ProductivePairJointState m n,
      if pairGapNat z.config X Y < target ∧ K ≤ z.relevant then
        iter (productivePairJointStageDeadlineStop
          h3 X Y S d target K) T q0 z
      else 0) ≤
      pairProgressPotential X Y
          (pairProperProgressTilt S d) (pairProperProgressFactor S d)
          q0.toRelevant /
        (pairProperProgressTilt S d ^ (target - 1) *
          (pairProperProgressFactor S d)⁻¹ ^ K) := by
  let w := pairProperProgressTilt S d
  let φ := pairProperProgressFactor S d
  let V : ProductivePairJointState m n → ℝ≥0∞ := fun z =>
    pairProgressPotential X Y w φ z.toRelevant
  let Bad : ProductivePairJointState m n → Prop := fun z =>
    pairGapNat z.config X Y < target ∧ K ≤ z.relevant
  let θ : ℝ≥0∞ := w ^ (target - 1) * (φ⁻¹) ^ K
  have hw1 : w ≤ 1 := by
    dsimp only [w]
    exact pairProperProgressTilt_le_one S d hS
  have hw0 : w ≠ 0 := by
    dsimp only [w]
    exact pairProperProgressTilt_ne_zero S d hS
  have hwtop : w ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hw1
  have hφ1 : φ ≤ 1 := by
    dsimp only [φ]
    exact pairProperProgressFactor_le_one S d hS
  have hφ0 : φ ≠ 0 := by
    dsimp only [φ]
    exact pairProperProgressFactor_ne_zero S d hS
  have hφtop : φ ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hφ1
  have hinv1 : 1 ≤ φ⁻¹ := ENNReal.one_le_inv.mpr hφ1
  have hinv0 : φ⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hφtop
  have hinvtop : φ⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hφ0
  have hθ0 : θ ≠ 0 := by
    dsimp only [θ]
    exact mul_ne_zero (pow_ne_zero _ hw0) (pow_ne_zero _ hinv0)
  have hθtop : θ ≠ ∞ := by
    dsimp only [θ]
    exact ENNReal.mul_ne_top
      (ENNReal.pow_ne_top hwtop) (ENNReal.pow_ne_top hinvtop)
  have hstep :
      ∀ q,
        expect
          (productivePairJointStageDeadlineStop h3 X Y S d target K q) V ≤
        V q := by
    intro q
    exact productivePairJointStageDeadlineStop_proper_conserve
      h3 X Y hXY S d target K hS hd2 hd3S q
  have hbad : ∀ z, Bad z → θ ≤ V z := by
    intro z hz
    have hgapExp : pairGapNat z.config X Y ≤ target - 1 := by
      dsimp only [Bad] at hz
      omega
    dsimp only [θ, V, pairProgressPotential,
      ProductivePairJointState.toRelevant]
    exact mul_le_mul'
      (pow_le_pow_right_of_le_one' hw1 hgapExp)
      (pow_le_pow_right₀ hinv1 hz.2)
  simpa only [Bad, V, θ, w, φ] using
    Tri.stopped_bad_mass_le
      (productivePairJointStageDeadlineStop h3 X Y S d target K)
      V Bad θ hθ0 hθtop hstep hbad T q0

/-- The actual completion-(c) involvement event is contained in the
relevant-counter event on every supported joint path. -/
theorem productivePairJointStageDeadlineStop_involving_mass_le_relevant_mass
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d target K T : ℕ) (q0 : ProductivePairJointState m n)
    (hq0 : q0.CounterInv) :
    (∑' z : ProductivePairJointState m n,
      if pairGapNat z.config X Y < target ∧ K ≤ z.involving then
        iter (productivePairJointStageDeadlineStop
          h3 X Y S d target K) T q0 z
      else 0) ≤
      ∑' z : ProductivePairJointState m n,
        if pairGapNat z.config X Y < target ∧ K ≤ z.relevant then
          iter (productivePairJointStageDeadlineStop
            h3 X Y S d target K) T q0 z
        else 0 := by
  apply ENNReal.tsum_le_tsum
  intro z
  by_cases hz : pairGapNat z.config X Y < target ∧ K ≤ z.involving
  · by_cases hpz :
        iter (productivePairJointStageDeadlineStop
          h3 X Y S d target K) T q0 z = 0
    · simp [hpz]
    · have hInv : z.CounterInv :=
        productivePairJointStageDeadlineStop_iter_counterInv
          h3 X Y hXY S d target K T q0 z hq0 hpz
      have hR : pairGapNat z.config X Y < target ∧ K ≤ z.relevant :=
        ⟨hz.1, hz.2.trans hInv⟩
      simp [hz, hR]
  · simp [hz]

theorem productivePairJointStageDeadlineStop_involving_tail
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (S d target K T : ℕ) (hS : 0 < S) (hd2 : 2 ≤ d)
    (hd3S : 3 * d ≤ S) (htarget : 1 ≤ target)
    (q0 : ProductivePairJointState m n) (hq0 : q0.CounterInv) :
    (∑' z : ProductivePairJointState m n,
      if pairGapNat z.config X Y < target ∧ K ≤ z.involving then
        iter (productivePairJointStageDeadlineStop
          h3 X Y S d target K) T q0 z
      else 0) ≤
      pairProgressPotential X Y
          (pairProperProgressTilt S d) (pairProperProgressFactor S d)
          q0.toRelevant /
        (pairProperProgressTilt S d ^ (target - 1) *
          (pairProperProgressFactor S d)⁻¹ ^ K) := by
  exact
    (productivePairJointStageDeadlineStop_involving_mass_le_relevant_mass
      h3 X Y hXY S d target K T q0 hq0).trans
      (productivePairJointStageDeadlineStop_relevant_tail
        h3 X Y hXY S d target K T hS hd2 hd3S htarget q0)

/-- Fixed-competitor completion-(c) hitting probability on the common
deadline process. -/
theorem productiveInvolvingStageDeadlineStop_fixed_pair_exp_tail
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (D x0 T : ℕ) (hD4 : 4 ≤ D) (hDx0 : D ≤ x0)
    (c0 : Config m n) (hinit : D ≤ pairGapNat c0 X Y) :
    (∑' q : Config m n × ℕ,
      if pairGapNat q.1 X Y < properPairTarget D ∧ x0 ≤ 2 * q.2 then
        iter
          (productiveInvolvingStageDeadlineStop h3 X
            (properStageScale x0) (D / 2) (properPairTarget D)
            (properInvolvingTarget x0))
          T (c0, 0) q
      else 0) ≤
      ENNReal.ofReal
        (Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ))))) := by
  let q0 : ProductivePairJointState m n :=
    { config := c0, involving := 0, relevant := 0 }
  let S := properStageScale x0
  let d := D / 2
  let target := properPairTarget D
  let K := properInvolvingTarget x0
  let w := pairProperProgressTilt S d
  let φ := pairProperProgressFactor S d
  have hq0 : q0.CounterInv := by simp [q0, ProductivePairJointState.CounterInv]
  have htail :=
    productivePairJointStageDeadlineStop_involving_tail
      h3 X Y hXY S d target K T
      (properStageScale_pos x0 (by omega)) (by omega)
      (three_halfGap_le_properStageScale D x0 hDx0)
      (properPairTarget_pos D (by omega)) q0 hq0
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
  have hscalar := properProgress_quotient_le_exp D x0 hD4 hDx0
  simpa only [properInvolvingTarget_le_iff, q0,
    ProductivePairJointState.toInvolving,
    S, d, target, K, w, φ] using
      hcommon.le.trans (htail.trans (hquot.trans hscalar))

/-- Genuine all-competitor completion-(c) hitting bound on the common
deadline-stopped involvement process. -/
theorem productiveInvolvingStageDeadlineStop_global_exp_tail
    (h3 : 3 ≤ n) (X : Species m)
    (D x0 T : ℕ) (hD4 : 4 ≤ D) (hDx0 : D ≤ x0)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    globalProperTargetFailureMass
        (iter
          (productiveInvolvingStageDeadlineStop h3 X
            (properStageScale x0) (D / 2) (properPairTarget D)
            (properInvolvingTarget x0))
          T (c0, 0))
        X (properPairTarget D) (properInvolvingTarget x0) ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ))))) := by
  calc
    globalProperTargetFailureMass
        (iter
          (productiveInvolvingStageDeadlineStop h3 X
            (properStageScale x0) (D / 2) (properPairTarget D)
            (properInvolvingTarget x0))
          T (c0, 0))
        X (properPairTarget D) (properInvolvingTarget x0) ≤
      ∑ Y ∈ Finset.univ.erase X,
        ∑' q : Config m n × ℕ,
          if pairGapNat q.1 X Y < properPairTarget D ∧
              properInvolvingTarget x0 ≤ q.2 then
            iter
              (productiveInvolvingStageDeadlineStop h3 X
                (properStageScale x0) (D / 2) (properPairTarget D)
                (properInvolvingTarget x0))
              T (c0, 0) q
          else 0 :=
      globalProperTargetFailureMass_le_pair_sum
        _ X (properPairTarget D) (properInvolvingTarget x0)
        (properPairTarget_pos D (by omega))
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
        productiveInvolvingStageDeadlineStop_fixed_pair_exp_tail
          h3 X Y (Ne.symm hYX) D x0 T hD4 hDx0 c0 hpair
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

#print axioms Tri.Multi.productivePairJointStageDeadlineStop_proper_conserve
#print axioms Tri.Multi.productivePairJointStageDeadlineStop_involving_tail
#print axioms Tri.Multi.productiveInvolvingStageDeadlineStop_fixed_pair_exp_tail
#print axioms Tri.Multi.productiveInvolvingStageDeadlineStop_global_exp_tail
